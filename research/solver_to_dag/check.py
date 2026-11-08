"""Compile this bounded construction slice, using only a verified installed core.
Caller must provide the documented locks/resource scope. Not a hostile-code sandbox.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path

MODULES = {'Attempt', 'Attempt.Equality', 'Attempt.Assembly', 'Attempt.Leaves',
           'Attempt.Fixtures', 'Attempt.Surface', 'Attempt.Audit'}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--core', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    core, output = args.core.resolve(), args.output.resolve()
    if args.output.exists() or args.output.is_symlink():
        p.error('output must be a NEW private attempt')
    source = Path(__file__).resolve().parent
    sources = {'.'.join(q.relative_to(source).with_suffix('').parts):q
               for q in source.rglob('*.lean')}
    if set(sources) != MODULES or any(q.is_symlink() for q in sources.values()):
        raise ValueError('exact owned module set / regular source required')
    expected = {n:q.read_bytes() for n,q in sources.items()}
    spec = importlib.util.spec_from_file_location('solver_dag_installed_workbench',core/'tools/workbench.py')
    wb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(wb)
    identity = wb.verify_core(core)
    wb.create(output,core)
    for n,raw in expected.items():
        target = output / Path(*n.split('.')).with_suffix('.lean')
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(raw)
    for n,raw in expected.items():
        if (output/Path(*n.split('.')).with_suffix('.lean')).read_bytes() != raw:
            raise ValueError('source-before-copy fidelity')
    root = wb.fresh_check_run(output)
    order = wb.module_sources(output,root)
    order = [(n,q) for n,q in order if n != 'Attempt.Audit'] + [(n,q) for n,q in order if n == 'Attempt.Audit']
    if {n for n,_ in order} != MODULES:
        raise ValueError('exact copied module set')
    overrides = {}
    for i,(module,path) in enumerate(order):
        overrides[module] = wb.compile_source(output,root,'source-'+str(i),path,module,overrides)
    audit_text = (root/('source-'+str(len(order)-1)+'-compile')/'stdout.txt').read_text()
    roots = re.findall(r'\[SOLVER_DAG_ROOT\] (\S+)',audit_text)
    if not roots or len(roots) != len(set(roots)):
        raise ValueError('completed audit direct-root output missing or duplicate')
    if wb.verify_core(core) != identity:
        raise ValueError('core source changed')
    result = {'status':'COMPONENTS_ONLY_FULL_CODEC_VERIFIER_MISSING','core_inventory':identity,
              'module_order':[n for n,_ in order],'receipts':str(root),'direct_roots':roots,
              'source_approval':False,'full_bridge_complete':False,
              'source_rows':[{'module':n,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in expected.items()]}
    (root/'COMPONENT_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
