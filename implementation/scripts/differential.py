#!/usr/bin/env python3
"""Compare finite OCaml cases against compiler-evaluated Gallina/reference Z cases.

Large nat cases use exact Rocq Z reference arithmetic, not enormous unary nat
normalisation. This distinction is recorded separately for every case.
"""
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import audit

FIXTURES = '''
From Coq Require Import ZArith String List.
From PCFW Require Import Orchestration RecordCrosscheck.
Import ListNotations.
Open Scope string_scope.
Set Printing Width 100000.
Section VerdictFixtures.
Variable ops : primitive_ops.
Variable ti : trusted_inputs.
Definition mc := mkManifestCommitment "d" "s" "sig".
Definition ac := mkAuthenticatedCampaign mc (mkManifest "m") [] (mkCampaignRecord "r") CompletenessUnknown.
Definition wd := mkWitnessData 0 "sd" "cd" [4611686018427387904%Z] [(-40000000000000000000000000001)%Z] [] [] [].
Definition empty_rr := mkReplayResult [] NoContextNeeded [] (mkFuelLedger 100 0) None [].
Definition witness_rr := mkReplayResult [] NoContextNeeded [mkStage2Slot 0 (Done (mkStage2Result 0 (ValidWitness wd) []))] (mkFuelLedger 100 0) None [].
Definition fuel_rr := mkReplayResult [] NoContextNeeded [] (mkFuelLedger 100 0) (Some CampaignFuelExhausted) [].
Definition rc := mkResolvedContext "p" "c" "d".
Definition exact_rr := mkReplayResult [] (ContextResolved rc []) [] (mkFuelLedger 100 0) None [].
Definition complete_ac := mkAuthenticatedCampaign mc (mkManifest "m") [] (mkCampaignRecord "r") (CompletenessComplete (mkCompletenessCertificate "registry-v0" "b")).
'''


def literal(x):
    return f'({x})%Z'


def cases():
    result=[]
    def add(args,term,kind):result.append({'input':args,'oracle_expression':term,'oracle_kind':kind})
    boundary=2**62-1
    huge=10**80+1
    for a,b in [(0,0),(1,2),(17,19),(boundary,1),(boundary,2),(boundary+1,huge),(huge,huge)]:
        for op in ('add','mul'):
            small=max(a,b)<100
            term=f'Z.of_nat (Nat.{op} {a} {b})' if small else f'Z.{op} {literal(a)} {literal(b)}'
            add([op,str(a),str(b)],term,'actual Gallina nat' if small else 'Rocq Z reference for nonnegative nat arithmetic')
    for a,b in [(0,0),(-1,-1),(-1,1),(-huge,-huge),(-huge,huge),(huge,huge+1),(huge,huge)]:
        add(['zeq',str(a),str(b)],f'Z.eqb {literal(a)} {literal(b)}','actual Gallina Z')
    for budget,used,cost in [(0,0,0),(1,0,1),(1,1,1),(100,99,1),(100,99,2),(boundary,boundary,1),(boundary+1,boundary,1),(huge,huge-1,1),(huge,huge,1),(huge,huge-1,2)]:
        small=max(budget,used,cost)<1000
        if small:
            term=f'match charge (mkFuelLedger {budget} {used}) {cost} with Some f => Some (Z.of_nat (fuel_consumed f)) | None => None end'
        else:
            term=f'if Z.leb (Z.add {literal(used)} {literal(cost)}) {literal(budget)} then Some (Z.add {literal(used)} {literal(cost)}) else None'
        add(['charge',str(budget),str(used),str(cost)],term,'actual Gallina charge' if small else 'Rocq Z reference for charge inequality')
    for s in ['', '0','1','123','-1','01','+1',' 1','1 ','1x','0x','1.0','999']:
        term=f'match RecordCrosscheck.parse_nat {json.dumps(s)} with Some (v,rest) => if String.eqb rest "" then Some (Z.of_nat v) else None | None => None end'
        add(['parse',s],term,'actual Gallina parse_nat with full-consumption wrapper')
    for value in [boundary,boundary+1,2**64,huge]:
        add(['parse',str(value)],literal(value),'Rocq Z numeric reference for large decimal roundtrip; no huge Gallina nat parser evaluation')
    for value in [-1,-huge,0,huge]:
        add(['nat-input',str(value)],f'Z.leb 0 {literal(value)}','Rocq Z reference for checked host nat conversion')
    for value in [0,-huge,huge]:
        term=f'match event_input (mkExecEvent (mkCallKey ContextProbe Probe 0) [{literal(value)}] (ExecOk [{literal(value)}])) with [x] => x | _ => 0%Z end'
        add(['event',str(value)],term,'actual Gallina signed transcript input projection')
    for kind,rr,ac in [('empty','empty_rr','ac'),('witness','witness_rr','ac'),('fuel','fuel_rr','ac'),('exact-disabled','exact_rr','complete_ac')]:
        add(['verdict',kind],f'verdict_of (decide ops {rr} {ac} ti [] NoTranscript (ParsedCommitment "d"))','actual Gallina decide on supplied typed fixture; no witness/faithfulness warrant')
    return result


def parse_oracle(text,count):
    if re.search(r'\b(?:Error|Anomaly|Fatal)\s*:',text):raise audit.AuditError('error diagnostic in differential oracle')
    matches=re.findall(r'PCFW_CASE:(\d+)\s*\n\s*=\s*(.*?)\s*\n\s*:\s*[^\n]+',text,re.S)
    if [int(i) for i,_ in matches]!=list(range(count)):raise audit.AuditError('missing/duplicate/unexpected differential oracle response')
    def normal(value):
        value=' '.join(value.split())
        value=re.sub(r'\((-?\d+)\)%Z',r'\1',value)
        value=re.sub(r'(-?\d+)%Z',r'\1',value)
        if value=='None':return 'reject'
        if value.startswith('Some '):value=value[5:]
        return value
    return [normal(v) for _,v in matches]


def compare(expected,actual,data):
    if len(actual)!=len(data):raise audit.AuditError('differential output count mismatch')
    for i,(e,a,c) in enumerate(zip(expected,actual,data)):
        if c['input'][0]=='nat-input':e={'true':'accept','false':'reject'}.get(e,e)
        if a!=e:raise audit.AuditError(f'differential case {i} {c["input"]}: Gallina/reference={e}; OCaml={a}')
        c.update(oracle_result=e,ocaml_result=a,result='PASS')


def main():
    output=audit.IMPL/'release-audit';output.mkdir(exist_ok=True)
    path=output/'differential.json';path.write_text(json.dumps({'result':'FAILED','case_count':None})+'\n')
    try:
        data=cases()
        with tempfile.TemporaryDirectory(prefix='pcfw-differential-') as directory:
            source=Path(directory)/'Oracle.v'
            source.write_text(FIXTURES+'\n'.join(f'Goal True. idtac "PCFW_CASE:{i}". Abort.\nEval vm_compute in ({c["oracle_expression"]}).' for i,c in enumerate(data))+'\nEnd VerdictFixtures.\n')
            oracle=subprocess.run(['coqc','-Q','rocq','PCFW',str(source)],cwd=audit.IMPL,capture_output=True,text=True)
            (output/'differential-oracle.v').write_text(source.read_text())
            (output/'differential-oracle.log').write_text(oracle.stdout+oracle.stderr)
            if oracle.returncode:raise audit.AuditError(f'Gallina oracle compilation failed: {oracle.stderr}')
            expected=parse_oracle(oracle.stdout+oracle.stderr,len(data))
        executable=subprocess.run([str(audit.IMPL/'ocaml/test_integer_differential'),'--cases'],input=''.join('\t'.join(c['input'])+'\n' for c in data),capture_output=True,text=True)
        if executable.returncode:raise audit.AuditError(f'OCaml comparator failed: {executable.stderr}')
        compare(expected,executable.stdout.splitlines(),data)
        summary={'result':'PASS','case_count':len(data),'actual_Gallina_case_count':sum(c['oracle_kind'].startswith('actual Gallina') for c in data),
                 'reference_Z_case_count':sum(not c['oracle_kind'].startswith('actual Gallina') for c in data),'general_correspondence_theorem':False,'cases':data}
        path.write_text(json.dumps(summary,indent=2)+'\n')
        print(f'PASS: differential battery; {len(data)} cases; finite-case evidence only')
        return 0
    except (audit.AuditError,OSError,subprocess.SubprocessError) as e:
        path.write_text(json.dumps({'result':'FAILED','error':str(e)})+'\n');print(f'FAIL: differential battery: {e}',file=sys.stderr);return 1
if __name__=='__main__':sys.exit(main())
