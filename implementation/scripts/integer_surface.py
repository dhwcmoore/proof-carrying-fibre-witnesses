#!/usr/bin/env python3
"""Structural gate and mechanical correspondence inventory; no equivalence claim."""
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import audit


def compile_checker(directory):
    source = Path(directory) / 'check_integer_interfaces.ml'
    source.write_bytes((audit.IMPL / 'scripts/check_integer_interfaces.ml').read_bytes())
    binary = Path(directory) / 'check_integer_interfaces'
    subprocess.run(['ocamlc','-I','+compiler-libs','ocamlcommon.cma',str(source),'-o',str(binary)], check=True, capture_output=True)
    return binary


def inspect(binary, pairs):
    result = subprocess.run([str(binary),*[str(p) for pair in pairs for p in pair]], capture_output=True, text=True)
    if result.returncode:
        raise audit.AuditError(result.stderr.strip() or 'integer structural inspection failed')


def check_link_plan(makefile):
    for line in makefile.replace("\\\n", " ").splitlines():
        if line.startswith('\t') and not line.startswith('\trm ') and not line.startswith('\tfind '):
            for word in shlex.split(line.strip()):
                if Path(word).name in ('orchestration.ml','orchestration.mli','orchestration.cmo','orchestration.cmi','orchestration.cmx','orchestration.o'):
                    raise audit.AuditError('historical native orchestration re-entered build/link plan')


def inventory():
    formal = audit.inventory()
    entries=[]; expected=[]
    for module in formal['extraction_modules']:
        driver = audit.IMPL / 'rocq' / (module+'.v')
        text=driver.read_text();code=audit.source_code(text)
        imports=re.findall(r'\bExtrOcaml\w+',code)
        if 'ExtrOcamlNatBigInt' not in imports or 'ExtrOcamlZBigInt' not in imports or any(i in imports for i in ('ExtrOcamlNatInt','ExtrOcamlZInt')):
            raise audit.AuditError(f'unapproved integer mappings in {driver.name}')
        targets=re.findall(r'\bExtraction\s+"(ocaml/extracted_\w+\.ml)"\s+([^.]*)\.',text)
        if len(targets)!=1: raise audit.AuditError(f'unknown extraction output in {driver.name}')
        target,roots=targets[0];path=audit.IMPL/target;interface=path.with_suffix('.mli')
        expected.append(interface)
        if not path.is_file() or not interface.is_file():raise audit.AuditError(f'missing regenerated extraction: {target}')
        numeric=[line.strip() for line in interface.read_text().splitlines() if 'Big_int_Z.big_int' in line]
        entries.append({'module':path.stem,'category':1,'driver':str(driver.relative_to(audit.IMPL.parent)),
          'extracted_roots':roots.split(),'nat_mapping':'Big_int_Z.big_int (nonnegative domain)',
          'Z_mapping':'Big_int_Z.big_int','integer_signature_fields':numeric,
          'native_int_semantic_overflow':False,'mapping_trusted':True,'general_correspondence_theorem':False,
          'differential_evidence':'see differential.json; only named finite cases','release_required':True})
    if set(expected)!=set((audit.IMPL/'ocaml').glob('extracted_*.mli')):
        raise audit.AuditError('unexpected or missing extracted interfaces')
    wrappers=sorted(p for p in (audit.IMPL/'ocaml').glob('*.ml') if not p.name.startswith('extracted_') and p.name!='orchestration.ml')
    for path in wrappers:
        entries.append({'module':path.stem,'category':4,'implementation':str(path.relative_to(audit.IMPL.parent)),
                        'integer_representation':'Big_int_Z semantic values; native bounded host byte/bit/list/parser utility indices where used',
                        'direct_Rocq_counterpart':None,'general_correspondence_theorem':False,'release_required':True})
    if not all((audit.IMPL/'ocaml'/name).is_file() for name in ('orchestration.ml','orchestration.mli')):
        raise audit.AuditError('historical demo inventory changed; review its classification')
    entries.append({'module':'orchestration','category':3,'implementation':'implementation/ocaml/orchestration.ml',
      'Rocq_source':'implementation/rocq/Orchestration.v','integer_representation':'native int',
      'overflow_possible':True,'data_representation':'reduced historical records; differs from extraction',
      'general_correspondence_theorem':False,'differential_evidence':False,'release_required':False,
      'status':'historical non-normative demo; excluded from compilation/linking'})
    return entries,expected,wrappers


def main():
    output=audit.IMPL/'release-audit';output.mkdir(exist_ok=True)
    path=output/'integer-correspondence.json';path.write_text(json.dumps({'result':'FAILED'})+'\n')
    try:
        check_link_plan((audit.IMPL/'Makefile').read_text())
        entries,interfaces,wrappers=inventory()
        with tempfile.TemporaryDirectory(prefix='pcfw-integer-audit-') as directory:
            inspect(compile_checker(directory),[('interface',p) for p in interfaces]+[('wrapper',p) for p in wrappers])
        data={'result':'PASS','extracted_module_count':len(interfaces),'native_int_extracted_interface_count':0,
              'normative_wrapper_count':len(wrappers),'historical_native_demo_count':sum(e['category']==3 for e in entries),'modules':entries}
        path.write_text(json.dumps(data,indent=2)+'\n')
        print(f'PASS: integer structural audit; {len(interfaces)} extracted interfaces; no native int or historical mirror dependency')
        return 0
    except (audit.AuditError,OSError,ValueError,subprocess.SubprocessError) as e:
        path.write_text(json.dumps({'result':'FAILED','error':str(e)})+'\n')
        print(f'FAIL: integer surface: {e}',file=sys.stderr);return 1
if __name__=='__main__':sys.exit(main())
