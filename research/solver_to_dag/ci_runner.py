"""No-skip addon CI. Caller supplies locks, CPU/resource scope and a built core."""
import sys
sys.dont_write_bytecode=True
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
import unittest

HERE=Path(__file__).resolve().parent

def load_own(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

CHECK=load_own('solver_dag_checker',HERE/'check.py')
EXPECTED_MODULES=frozenset(CHECK.MODULES)
BOOTSTRAP_IDS=tuple('solver_dag_bootstrap.BootstrapTests.'+name for name in (
    'test_actual_admitted_installed_core_positive',
    'test_executes_same_checked_buffer_not_reopened_source',
    'test_invalid_loader_rejected_before_compilation',
    'test_missing_loader_fails_closed',
    'test_optimized_execution_retains_workbench_rejection',
    'test_rejected_core_never_executes_import_marker',
    'test_self_supplied_manifest_does_not_authorize_loader',
    'test_substituted_inventory_rejected_before_exec',
    'test_symlinked_loader_rejected'))

def validate_bootstrap(r):
    fields={'schema','count','ids','successes','skipped','failures','errors',
            'expected_failures','unexpected_successes'}
    if not isinstance(r,dict) or set(r)!=fields or r['schema']!='solver-dag-bootstrap-v1':
        raise ValueError('missing/malformed bootstrap report')
    if type(r['count']) is not int or r['count']!=9:
        raise ValueError('exactly nine bootstrap tests required')
    for key in ('ids','successes'):
        if (not isinstance(r[key],list) or any(not isinstance(n,str) for n in r[key])
                or len(r[key])!=9 or sorted(r[key])!=sorted(BOOTSTRAP_IDS)):
            raise ValueError('missing/extra/duplicate bootstrap IDs: '+key)
    for key in fields-{'schema','count','ids','successes'}:
        if r[key]!=[]:
            raise ValueError('bootstrap skip/failure/error/nonordinary outcome: '+key)

def validate_component(r,code):
    if code!=0 or not isinstance(r,dict):raise ValueError('check.py failed or result missing')
    if r.get('status')!='CONDITIONAL_SOLVER_TO_DAG_KERNEL_CHECKED' or r.get('full_bridge_complete') is not True:
        raise ValueError('incomplete component status')
    modules=r.get('module_order');rows=r.get('source_rows');roots=r.get('direct_roots')
    if (not isinstance(modules,list) or any(not isinstance(n,str) for n in modules) or len(modules)!=len(EXPECTED_MODULES)
            or set(modules)!=EXPECTED_MODULES):raise ValueError('component module roster')
    if (not isinstance(rows,list) or len(rows)!=len(EXPECTED_MODULES)
            or any(not isinstance(x,dict) or set(x)!={'module','bytes','sha256'}
                   or not isinstance(x['module'],str) or type(x['bytes']) is not int or x['bytes']<0
                   or not isinstance(x['sha256'],str) or not re.fullmatch('[0-9a-f]{64}',x['sha256']) for x in rows)
            or {x.get('module') for x in rows}!=EXPECTED_MODULES):raise ValueError('component source roster')
    if (not isinstance(roots,list) or not roots or any(not isinstance(n,str) for n in roots)
            or len(set(roots))!=len(roots)):raise ValueError('missing/duplicate direct roots')

class RecordingResult(unittest.TextTestResult):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs);self.ids=[];self.successes=[]
    def startTest(self,test):
        self.ids.append(test.id());super().startTest(test)
    def addSuccess(self,test):
        self.successes.append(test.id());super().addSuccess(test)

def run_bootstrap(core,log):
    os.environ['SOLVER_DAG_TEST_CORE']=str(core)
    module=load_own('solver_dag_bootstrap',HERE/'test_bootstrap.py')
    suite=unittest.defaultTestLoader.loadTestsFromModule(module)
    with log.open('x') as stream:
        r=unittest.TextTestRunner(stream=stream,verbosity=2,resultclass=RecordingResult).run(suite)
    return dict(schema='solver-dag-bootstrap-v1',count=r.testsRun,ids=r.ids,successes=r.successes,
        skipped=[[t.id(),why] for t,why in r.skipped],failures=[[t.id(),s] for t,s in r.failures],
        errors=[[t.id(),s] for t,s in r.errors],expected_failures=[[t.id(),s] for t,s in r.expectedFailures],
        unexpected_successes=[t.id() for t in r.unexpectedSuccesses])

def pin(p):
    b=p.read_bytes();return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())

def consume_check(attempt,code):
    parent=attempt/'.lake/conditional-check/runs'
    runs=list(parent.iterdir()) if parent.is_dir() else []
    if len(runs)!=1 or runs[0].is_symlink():raise ValueError('exactly one owned check run required')
    run=runs[0];p=run/'COMPONENT_RESULT.json'
    if not p.is_file():raise ValueError('COMPONENT_RESULT.json missing')
    r=json.loads(p.read_bytes());validate_component(r,code)
    if Path(r['receipts']).resolve()!=run.resolve():raise ValueError('component receipt identity')
    for row in r['source_rows']:
        source=HERE/Path(*row['module'].split('.')).with_suffix('.lean')
        if {k:row[k] for k in ('bytes','sha256')}!=pin(source):raise ValueError('compiled source identity')
    for label in ['source-order-imports']+[f'source-{i}-{phase}'
            for i in range(len(EXPECTED_MODULES)) for phase in ['header-imports','compile']]:
        d=run/label
        for name in ('launch.json','process.json','terminal.json','stdout.txt','stderr.txt'):
            if not (d/name).is_file():raise ValueError('compiler receipt missing: '+label+'/'+name)
        if json.loads((d/'terminal.json').read_bytes())['OS_exit']!=0:raise ValueError('compiler failed: '+label)
    audit=(run/f'source-{len(EXPECTED_MODULES)-1}-compile/stdout.txt').read_text()
    if re.findall(r'\[SOLVER_DAG_ROOT\] (\S+)',audit)!=r['direct_roots']:raise ValueError('root stdout/result mismatch')
    axioms=re.findall(r'^\[SOLVER_DAG_AXIOM\] \S+ (\S+)$',audit,re.M)
    if set(axioms)-{'propext','Classical.choice','Quot.sound'}:raise ValueError('unexpected axiom')
    return r,run

def source_pins():
    paths=sorted(p for p in HERE.rglob('*') if p.suffix in {'.lean','.py','.md'} and p.is_file())
    if any(p.is_symlink() for p in paths):raise ValueError('owned source symlink')
    return {p.relative_to(HERE).as_posix():pin(p) for p in paths}

def save(path,value):
    with path.open('x') as h:json.dump(value,h,indent=2);h.write('\n')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--core',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    if sys.flags.optimize:p.error('optimized CI runner rejected')
    root=args.output.absolute()
    if root.exists() or root.is_symlink() or root.resolve()!=root:p.error('NEW unaliased private output required')
    root.mkdir(parents=True);art=root/'artifacts';art.mkdir();temp=root/'temp';temp.mkdir()
    os.environ.update(TMPDIR=str(temp),PYTHONDONTWRITEBYTECODE='1',PYTHONPYCACHEPREFIX=str(root/'bytecode'))
    tempfile.tempdir=str(temp)
    result=dict(status='FAILED',bootstrap=None,check_OS_exit=None,component=None,
                source_approval=False,release_approval=False)
    attempt=root/'attempt';run=None;before=source_pins()
    for name in before:
        dest=art/'sources'/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(HERE/name,dest)
    save(art/'SOURCE_PINS.json',before)
    try:
        core=args.core.resolve(strict=True)
        wb=CHECK.load_workbench(core);identity=wb.verify_core(core)
        save(art/'CORE_IDENTITY.json',dict(public_commit=CHECK.PUBLIC_CORE_COMMIT,
            inventory_sha256=identity,workbench=pin(core/'tools/workbench.py'),
            toolchain=(core/'lean-toolchain').read_text().strip(),lock=pin(core/'lake-manifest.json')))
        os.environ['SOLVER_DAG_TEST_RECEIPTS']=str(art/'bootstrap-subprocesses')
        report=run_bootstrap(core,art/'bootstrap.log');save(art/'BOOTSTRAP.json',report)
        validate_bootstrap(report);result['bootstrap']='NINE_PASS_ZERO_SKIPS'
        argv=[sys.executable,'-B',str(HERE/'check.py'),'--core',str(core),'--output',str(attempt)]
        try:
            wb.command(root,'addon-check',argv,HERE)
        finally:
            terminal=root/'addon-check/terminal.json'
            if terminal.is_file():result['check_OS_exit']=json.loads(terminal.read_bytes())['OS_exit']
        component,run=consume_check(attempt,result['check_OS_exit'])
        if component['core_inventory']!=identity or wb.verify_core(core)!=identity:raise ValueError('core identity changed')
        if source_pins()!=before:raise ValueError('owned source changed')
        save(art/'COMPONENT_RESULT.json',component)
        result.update(status='PASS',component=dict(modules=len(component['module_order']),
            direct_roots=len(component['direct_roots']),result_pin=pin(art/'COMPONENT_RESULT.json')))
    except (OSError,ValueError,RuntimeError) as error:
        result['error']=str(error)
    finally:
        # Only owned verification evidence. Never upload core/dependency caches,
        # toolchains, credentials, attempt .lake objects or downloaded archives.
        command=root/'addon-check'
        if command.is_dir():shutil.copytree(command,art/'check-command')
        parents=attempt/'.lake/conditional-check/runs'
        if parents.is_dir():
            for r in parents.iterdir():
                for source in r.rglob('*'):
                    if source.is_file() and not source.is_symlink() and source.suffix in {'.json','.txt'}:
                        dest=art/'compiler'/r.name/source.relative_to(r)
                        dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest)
        save(art/'CI_RESULT.json',result)
    print(json.dumps(result))
    return 0 if result['status']=='PASS' else 1

if __name__=='__main__':raise SystemExit(main())
