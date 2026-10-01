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


ROOT_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
OUTPUT_NAME = re.compile(r'"(ocaml/extracted_[A-Za-z0-9_]+\.ml)"')


def skip_trivia(text, position):
    """Skip whitespace and nested Rocq comments, preserving strings elsewhere."""
    while position < len(text):
        if text[position].isspace():
            position += 1
        elif text.startswith('(*', position):
            depth = 1
            position += 2
            while depth and position < len(text):
                if text.startswith('(*', position):
                    depth += 1
                    position += 2
                elif text.startswith('*)', position):
                    depth -= 1
                    position += 2
                else:
                    position += 1
            if depth:
                raise audit.AuditError('unterminated extraction comment')
        else:
            break
    return position


def parse_extraction(text, driver):
    """Parse the current drivers' single quoted-output Extraction command.

    Commands start at a statement boundary, excluding the Extraction library
    name in imports. Roots are whitespace/comment-separated identifiers,
    optionally qualified.
    Other extraction forms require an explicit review rather than guessing.
    """
    code = audit.source_code(text)
    commands = []
    for keyword in re.finditer(r'(?:\A\s*|(?<=\.)\s+)Extraction\b', code):
        position = skip_trivia(text, keyword.end())
        if re.match(r'Language\s+OCaml\s*\.(?=\s|$)', code[position:]):
            continue
        output = OUTPUT_NAME.match(text, position)
        if not output:
            raise audit.AuditError(f'unsupported extraction command in {driver}')
        position = output.end()
        roots = []
        while True:
            next_position = skip_trivia(text, position)
            if text[next_position:next_position + 1] == '.':
                end = next_position + 1
                if end < len(text) and not text[end].isspace() and not text.startswith('(*', end):
                    raise audit.AuditError(f'invalid extraction terminator in {driver}')
                break
            if next_position == position:
                raise audit.AuditError(f'missing extraction root separator in {driver}')
            root = ROOT_NAME.match(text, next_position)
            if not root:
                raise audit.AuditError(f'unsupported or unterminated extraction roots in {driver}')
            roots.append(root[0])
            position = root.end()
        if not roots or len(roots) != len(set(roots)):
            raise audit.AuditError(f'empty or duplicate extraction roots in {driver}')
        commands.append((output[1], roots))
    if len(commands) != 1:
        raise audit.AuditError(f'expected one extraction output in {driver}')
    return commands[0]


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


def inventory(formal=None, impl=None):
    impl = audit.IMPL if impl is None else impl
    formal = audit.inventory(impl) if formal is None else formal
    modules = formal.get('extraction_modules')
    if not isinstance(modules, list) or not modules or any(
            not isinstance(m, str) or not re.fullmatch(r'Extract\w+', m) for m in modules):
        raise audit.AuditError('empty or malformed extraction-driver inventory')
    if len(modules) != len(set(modules)):
        raise audit.AuditError('duplicate extraction driver')
    entries=[]; expected=[]
    for module in modules:
        driver = impl / 'rocq' / (module+'.v')
        if not driver.is_file():
            raise audit.AuditError(f'missing extraction driver: {driver.name}')
        text=driver.read_text();code=audit.source_code(text)
        imports=re.findall(r'\bExtrOcaml\w+',code)
        if 'ExtrOcamlNatBigInt' not in imports or 'ExtrOcamlZBigInt' not in imports or any(i in imports for i in ('ExtrOcamlNatInt','ExtrOcamlZInt')):
            raise audit.AuditError(f'unapproved integer mappings in {driver.name}')
        target,roots=parse_extraction(text,driver.name)
        path=impl/target;interface=path.with_suffix('.mli')
        expected.append(interface)
        if not path.is_file() or not interface.is_file():raise audit.AuditError(f'missing regenerated extraction: {target}')
        numeric=[line.strip() for line in interface.read_text().splitlines() if 'Big_int_Z.big_int' in line]
        entries.append({'module':path.stem,'category':1,'driver':str(driver.relative_to(impl.parent)),
          'output':str(path.relative_to(impl.parent)),
          'extracted_roots':roots,'extracted_root_count':len(roots),'nat_mapping':'Big_int_Z.big_int (nonnegative domain)',
          'Z_mapping':'Big_int_Z.big_int','integer_signature_fields':numeric,
          'native_int_semantic_overflow':False,'mapping_trusted':True,'general_correspondence_theorem':False,
          'differential_evidence':'see differential.json; only named finite cases','release_required':True})
    if len(expected)!=len(set(expected)) or set(expected)!=set((impl/'ocaml').glob('extracted_*.mli')):
        raise audit.AuditError('unexpected or missing extracted interfaces')
    wrappers=sorted(p for p in (impl/'ocaml').glob('*.ml') if not p.name.startswith('extracted_') and p.name!='orchestration.ml')
    for path in wrappers:
        entries.append({'module':path.stem,'category':4,'implementation':str(path.relative_to(impl.parent)),
                        'integer_representation':'Big_int_Z semantic values; native bounded host byte/bit/list/parser utility indices where used',
                        'direct_Rocq_counterpart':None,'general_correspondence_theorem':False,'release_required':True})
    if not all((impl/'ocaml'/name).is_file() for name in ('orchestration.ml','orchestration.mli')):
        raise audit.AuditError('historical demo inventory changed; review its classification')
    entries.append({'module':'orchestration','category':3,'implementation':'implementation/ocaml/orchestration.ml',
      'Rocq_source':'implementation/rocq/Orchestration.v','integer_representation':'native int',
      'overflow_possible':True,'data_representation':'reduced historical records; differs from extraction',
      'general_correspondence_theorem':False,'differential_evidence':False,'release_required':False,
      'status':'historical non-normative demo; excluded from compilation/linking'})
    return entries,expected,wrappers


def evidence(entries, interfaces, wrappers):
    return {'result':'PASS','extracted_module_count':len(interfaces),
            'extracted_root_count':sum(e['extracted_root_count'] for e in entries if e['category']==1),
            'native_int_extracted_interface_count':0,'normative_wrapper_count':len(wrappers),
            'historical_native_demo_count':sum(e['category']==3 for e in entries),'modules':entries}


def validate_evidence(recorded, formal, impl=None):
    """Reconcile every evidence row with current drivers, interfaces and clients.

    This validates inventory metadata; the separate AST gate establishes the
    structural integer result, and release checks that it actually executed.
    """
    expected = evidence(*inventory(formal, impl))
    if not isinstance(recorded, dict) or set(recorded) != set(expected):
        raise audit.AuditError('malformed integer evidence fields')
    rows = recorded['modules']
    if not isinstance(rows, list) or not rows or len(rows) != len(expected['modules']):
        raise audit.AuditError('incomplete integer module inventory')
    by_module = {}
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get('module'), str):
            raise audit.AuditError('malformed integer module record')
        if row['module'] in by_module:
            raise audit.AuditError('duplicate integer module record')
        by_module[row['module']] = row
    if set(by_module) != {row['module'] for row in expected['modules']}:
        raise audit.AuditError('integer module inventory differs from source')
    for key, value in expected.items():
        if key != 'modules' and (type(recorded[key]) is not type(value) or recorded[key] != value):
            raise audit.AuditError(f'integer evidence count/result differs: {key}')
    for row in expected['modules']:
        actual = by_module[row['module']]
        if set(actual) != set(row):
            raise audit.AuditError(f'malformed integer module fields: {row["module"]}')
        for key, value in row.items():
            if type(actual[key]) is not type(value) or actual[key] != value:
                raise audit.AuditError(f'integer inventory differs for {row["module"]}: {key}')


def main():
    output=audit.IMPL/'release-audit';output.mkdir(exist_ok=True)
    path=output/'integer-correspondence.json';path.write_text(json.dumps({'result':'FAILED'})+'\n')
    try:
        check_link_plan((audit.IMPL/'Makefile').read_text())
        entries,interfaces,wrappers=inventory()
        with tempfile.TemporaryDirectory(prefix='pcfw-integer-audit-') as directory:
            inspect(compile_checker(directory),[('interface',p) for p in interfaces]+[('wrapper',p) for p in wrappers])
        data=evidence(entries,interfaces,wrappers)
        path.write_text(json.dumps(data,indent=2)+'\n')
        print(f'PASS: integer structural audit; {len(interfaces)} extracted interfaces; no native int or historical mirror dependency')
        return 0
    except (audit.AuditError,OSError,ValueError,subprocess.SubprocessError) as e:
        path.write_text(json.dumps({'result':'FAILED','error':str(e)})+'\n')
        print(f'FAIL: integer surface: {e}',file=sys.stderr);return 1
if __name__=='__main__':sys.exit(main())
