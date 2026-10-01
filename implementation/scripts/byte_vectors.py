#!/usr/bin/env python3
"""Independent Python wire/digest vectors for the bounded ASCII transcript adapter."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import audit


def vectors():
    huge=10**80+1
    def event(phase,role,repeat,outcome):
        return {'input':[-huge],'key':{'phase':phase,'repeat':repeat,'role':role},'outcome':outcome}
    phase={'k':'stage2','v':huge}
    return [[],[event('context_probe','probe',0,{'k':'ok','v':[huge]})],
            [event(phase,'x',huge,{'k':'failed','v':'bad\n\0\v"\\'}),event(phase,'y',1,'exhausted')]]


def compare(lines):
    expected=vectors()
    if len(lines)!=len(expected):raise audit.AuditError('byte vector response count mismatch')
    evidence=[]
    for index,(value,line) in enumerate(zip(expected,lines)):
        canonical=json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True)
        digest_input=b'pcfw.exec_transcript.v1\x1f'+canonical.encode('ascii')
        fields=line.split('\t')
        wanted=[canonical,digest_input.hex(),hashlib.sha256(digest_input).hexdigest()]
        if fields!=wanted:raise audit.AuditError(f'byte vector {index}: canonical bytes/digest input/digest differ')
        evidence.append({'canonical_bytes':canonical,'digest_input_hex':wanted[1],'sha256':wanted[2],'result':'PASS'})
    return evidence


def main():
    output=audit.IMPL/'release-audit';output.mkdir(exist_ok=True)
    path=output/'byte-vectors.json';path.write_text(json.dumps({'result':'FAILED'})+'\n')
    try:
        client=subprocess.run([str(audit.IMPL/'ocaml/test_byte_boundaries'),'--transcript-vectors'],capture_output=True,text=True)
        if client.returncode:raise audit.AuditError(f'byte vector client failed: {client.stderr}')
        evidence=compare(client.stdout.splitlines())
        path.write_text(json.dumps({'result':'PASS','vector_count':len(evidence),'vectors':evidence,
                                   'formal_parser_correctness_theorem':False,'faithfulness_established':False},indent=2)+'\n')
        print(f'PASS: independent byte vectors; {len(evidence)} canonical transcript/digest inputs')
        return 0
    except (audit.AuditError,OSError,subprocess.SubprocessError) as error:
        path.write_text(json.dumps({'result':'FAILED','error':str(error)})+'\n')
        print(f'FAIL: byte vectors: {error}',file=sys.stderr);return 1
if __name__=='__main__':sys.exit(main())
