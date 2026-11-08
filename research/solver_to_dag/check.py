"""Compile this bounded construction slice, using only a verified installed core.
Caller must provide the documented locks/resource scope. Not a hostile-code sandbox.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import types
import json
import re
from pathlib import Path

MODULES = {'Attempt', 'Attempt.Equality', 'Attempt.Assembly', 'Attempt.Leaves',
           'Attempt.Fixtures', 'Attempt.Surface', 'Attempt.Audit',
           'Attempt.Prefix', 'Attempt.Parser', 'Attempt.Codec'}

# Reviewed public package identity, not authority supplied by --core.
# https://github.com/khanukov/p-np2/tree/1180e5e0ffe760bbc3a1c70143ec09b362d33a8e/conditional_separation
PUBLIC_CORE_COMMIT='1180e5e0ffe760bbc3a1c70143ec09b362d33a8e'
WORKBENCH_SHA256='0dceab37e05c901b37b7aadc9c5759dbd4e77659b8f98d43d30ce1ff69c0706c'
INVENTORY_SHA256='5f833d26620edc0404130be1ac445da0cb9f6a89599af1894fca94faf543c9a3'

def load_workbench(core):
    """Authenticate before executing; the installed core must remain immutable.

    Bootstrap Python imports are stdlib only. The pinned full inventory also
    binds the later executable SourceImports.lean, checked by verify_core.
    This is a known-version bootstrap, not a sandbox for hostile installations.
    """
    core=Path(core).resolve()
    checked={}
    for relative,size,digest in (
        ('tools/workbench.py',25755,WORKBENCH_SHA256),
        ('PACKAGE_FILES.json',209612,INVENTORY_SHA256)):
        path=core/relative
        try:
            if path.is_symlink() or not path.is_file() or path.resolve()!=path:
                raise ValueError('untrusted installed source path: '+relative)
            raw=path.read_bytes()
        except OSError as e:
            raise ValueError('untrusted installed source unreadable: '+relative) from e
        if len(raw)!=size or hashlib.sha256(raw).hexdigest()!=digest:
            raise ValueError('untrusted installed source identity: '+relative)
        checked[relative]=raw
    wb=types.ModuleType('solver_dag_installed_workbench')
    wb.__file__=str(core/'tools/workbench.py')
    wb.__package__=''
    # Compile/execute this authenticated buffer; never reopen it via a loader.
    exec(compile(checked['tools/workbench.py'],wb.__file__,'exec'),wb.__dict__)
    return wb

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
    wb = load_workbench(core)
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
    result = {'status':'CONDITIONAL_SOLVER_TO_DAG_KERNEL_CHECKED','core_inventory':identity,
              'module_order':[n for n,_ in order],'receipts':str(root),'direct_roots':roots,
              'source_approval':False,'full_bridge_complete':True,
              'source_rows':[{'module':n,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in expected.items()]}
    (root/'COMPONENT_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
