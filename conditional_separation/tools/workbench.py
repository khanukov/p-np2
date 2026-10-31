"""Portable source-based attempt workbench; not a sandbox for hostile Lean code."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import uuid
import zipfile

if sys.flags.optimize:
    raise SystemExit('optimized checker rejected')

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PACKAGE = Path(__file__).resolve().parents[1]


def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result: raise ValueError('duplicate JSON key: '+key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(encoding='utf-8'), object_pairs_hook=pairs)


def name(value):
    if not isinstance(value,str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*", value):
        raise ValueError("use a fully qualified ordinary Lean declaration name")
    return value


def forbidden(source):
    """Lexical convenience guard; kernel type/axiom checking is separate."""
    clean = []
    i = depth = 0
    while i < len(source):
        if source.startswith('/-', i):
            clean.append(' '); depth += 1; i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif source.startswith('--', i):
            clean.append(' ')
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\': i += 2
                elif source[i] == '"': i += 1; break
                else: i += 1
        else:
            clean.append(source[i]); i += 1
    words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", ''.join(clean)))
    return sorted(words & {'axiom', 'sorry', 'admit', 'native_decide', 'unsafe'})


def create(destination, core):
    destination, core = Path(destination).resolve(), Path(core).resolve()
    if not (core/'PROVENANCE.json').is_file() or not (core/'ConditionalSeparation/OpenProblem.lean').is_file():
        raise ValueError('explicit installed core source package required')
    verify_core(core)
    destination.mkdir(parents=True, exist_ok=False)
    quoted = json.dumps(str(core), ensure_ascii=False)
    (destination/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage separation_attempt\nrequire conditional_separation from '+quoted+'\n@[default_target]\nlean_lib Attempt\n', encoding='utf-8')
    locked = json.loads((core/'lake-manifest.json').read_text(encoding='utf-8'))
    locked['name'] = 'separation_attempt'
    locked['packages'] = [{'type':'path','scope':'','name':'conditional_separation',
        'dir':str(core),'inherited':False,'configFile':'lakefile.lean','manifestFile':'lake-manifest.json'}] + [dict(r,inherited=True) for r in locked['packages']]
    (destination/'lake-manifest.json').write_text(json.dumps(locked,indent=2)+'\n',encoding='utf-8')
    shutil.copyfile(core/'lean-toolchain', destination/'lean-toolchain')
    shutil.copyfile(core/'template/Attempt.lean', destination/'Attempt.lean')
    (destination/'attempt.json').write_text(json.dumps({'core':str(core),'status':'PARTIAL_NO_PROOF_OF_R'},indent=2)+'\n',encoding='utf-8')
    return destination


def pin(path):
    path = Path(path)
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}


def command(root, label, argv, cwd):
    directory = root/label
    directory.mkdir()
    (directory/'launch.json').write_text(json.dumps({'argv':argv,'cwd':str(cwd),'start':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n',encoding='utf-8')
    options = {'start_new_session':True} if os.name != 'nt' else {'creationflags':subprocess.CREATE_NEW_PROCESS_GROUP}
    with (directory/'stdout.txt').open('wb') as out, (directory/'stderr.txt').open('wb') as err:
        p = subprocess.Popen(argv,cwd=cwd,stdout=out,stderr=err,**options)
        try:
            (directory/'process.json').write_text(json.dumps({'pid':p.pid,'pgid':os.getpgid(p.pid) if os.name != 'nt' else None})+'\n',encoding='utf-8')
            code = p.wait()
        except BaseException as original:
            try:
                if os.name != 'nt':
                    try: os.killpg(p.pid, signal.SIGTERM)
                    except ProcessLookupError: pass
                else: p.terminate()
                p.wait()
            except BaseException as cleanup:
                if hasattr(original,'add_note'): original.add_note('cleanup also failed: '+repr(cleanup))
            raise
    (directory/'terminal.json').write_text(json.dumps({'OS_exit':code,'end':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n',encoding='utf-8')
    if code:
        raise RuntimeError(f'{label} rejected or failed (exit {code}); see {directory}')
    return (directory/'stdout.txt').read_text(encoding='utf-8')


def guard_source(proof, expected):
    name(proof)
    return f'''import ConditionalSeparation.OpenProblem
import Attempt
import Lean
open Lean Elab Command Term Meta in
run_cmd do
  let n := `{proof}
  let env ← getEnv
  let rn := `ConditionalSeparation.OpenProblem.R
  let some rci := env.find? rn | throwError "installed R absent"
  match rci with
  | .defnInfo _ => pure ()
  | _ => throwError "installed R must be a definition"
  unless rci.levelParams.isEmpty do throwError "installed R universe arity"
  let some idx := env.getModuleIdxFor? rn | throwError "installed R has no imported owner"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "installed R owner bounds"
  unless owner == `ConditionalSeparation.OpenProblem do throwError "installed R owner identity"
  let some info := env.find? n | throwError "missing closed proof {{n}}"
  liftTermElabM do
    let expected ← elabType (← `({expected}))
    unless ← isDefEq info.type expected do
      throwError "declaration must have CLOSED exact expected type"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axs ← collectAxioms n
  for a in axs do
    unless allowed.contains a do throwError "nonallowed axiom {{a}}"
  logInfo m!"[CS_ROOT] {{n}}"
  for a in axs do logInfo m!"[CS_AXIOM] {{a}}"
#print axioms {proof}
'''


def verify_core(core):
    core = Path(core).resolve()
    provenance_path = core/'PROVENANCE.json'
    if provenance_path.is_symlink(): raise ValueError('provenance symlink')
    provenance = read_json(provenance_path)
    if not isinstance(provenance,dict) or set(provenance) != {'schema','donor_commit','copy_exception','not_declaration_minimum','modules'}:
        raise ValueError('provenance schema')
    if provenance['schema'] != 'conditional-separation-exact-core-v1' or not isinstance(provenance['modules'],list):
        raise ValueError('provenance version/modules')
    if not isinstance(provenance['donor_commit'],str) or not re.fullmatch('[0-9a-f]{40}',provenance['donor_commit']):
        raise ValueError('provenance revision')
    if not isinstance(provenance['copy_exception'],str) or provenance['not_declaration_minimum'] is not True:
        raise ValueError('provenance role')
    modules, copied_paths = set(), set()
    for row in provenance['modules']:
        if not isinstance(row,dict) or set(row) != {'module','path','donor_relative','sha256','bytes','physical_lines','imports'}:
            raise ValueError('provenance row schema')
        name(row['module'])
        for key in ['path','donor_relative']:
            value = row[key]
            if not isinstance(value,str): raise ValueError('provenance path type')
            relative = Path(value)
            if relative.is_absolute() or '..' in relative.parts or relative.as_posix() != value or '\\' in value:
                raise ValueError('provenance canonical relative path')
        if not row['path'].startswith('core/') or not row['donor_relative'].startswith(('pnp3/','pnp4/')):
            raise ValueError('provenance source roles')
        if row['module'] in modules or row['path'] in copied_paths:
            raise ValueError('provenance duplicate module/path')
        modules.add(row['module']); copied_paths.add(row['path'])
        if any(type(row[k]) is not int or row[k] < 0 for k in ['bytes','physical_lines']):
            raise ValueError('provenance nonboolean size/lines')
        if not isinstance(row['sha256'],str) or not re.fullmatch('[0-9a-f]{64}',row['sha256']):
            raise ValueError('provenance hash schema')
        if not isinstance(row['imports'],list): raise ValueError('provenance imports schema')
        for imported in row['imports']: name(imported)
        p = core/row['path']
        if p.resolve() != p or p.is_symlink() or not p.is_file():
            raise ValueError('provenance root-bound regular source')
        data = p.read_bytes()
        if len(data) != row['bytes'] or len(data.splitlines()) != row['physical_lines'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('installed copied-core source changed: '+row['path'])
    if (core/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.22.0-rc2':
        raise ValueError('pinned toolchain mismatch')
    inventory = core/'PACKAGE_FILES.json'
    if inventory.is_symlink() or not inventory.is_file(): raise ValueError('installed complete source inventory required')
    document = read_json(inventory)
    if set(document) != {'schema','files'} or document['schema'] != 'conditional-separation-source-files-v1' or not isinstance(document['files'],list):
        raise ValueError('package inventory schema')
    names = set()
    for row in document['files']:
        if not isinstance(row,dict) or set(row) != {'path','bytes','sha256'}: raise ValueError('package row schema')
        if not isinstance(row['path'],str): raise ValueError('package path type')
        relative = Path(row['path'])
        if relative.is_absolute() or '..' in relative.parts or relative.as_posix() != row['path'] or '\\' in row['path'] or row['path'] in names:
            raise ValueError('package inventory duplicate/path')
        if type(row['bytes']) is not int or row['bytes'] < 0 or not isinstance(row['sha256'],str) or not re.fullmatch('[0-9a-f]{64}',row['sha256']):
            raise ValueError('package size/hash schema')
        p = core/relative
        if p.resolve()!=p or p.is_symlink() or not p.is_file() or pin(p)['sha256'] != row['sha256'] or p.stat().st_size != row['bytes']:
            raise ValueError('installed package source changed: '+str(relative))
        names.add(row['path'])
    actual = set()
    for base,dirs,files in os.walk(core,followlinks=False):
        dirs[:] = [d for d in dirs if d not in {'.lake','.git','__pycache__'}]
        for d in dirs:
            if (Path(base)/d).is_symlink(): raise ValueError('package directory symlink')
        for filename in files:
            p = Path(base)/filename
            if p == inventory or filename == '.git': continue
            if p.is_symlink(): raise ValueError('package file symlink')
            actual.add(p.relative_to(core).as_posix())
    if actual != names: raise ValueError('exact installed source filename SET')
    return hashlib.sha256(inventory.read_bytes()).hexdigest()


def source_imports(attempt, root, label, sources):
    core = Path(read_json(attempt/'attempt.json')['core']).resolve()
    requests = [{'module':module,'source':str(path.resolve())} for module,path in sources.items()]
    request = root/(label+'.imports.request.json')
    output = root/(label+'.imports.json')
    request.write_text(json.dumps(requests,indent=2)+'\n',encoding='utf-8')
    command(root,label+'-imports',['lake','env','lean','-DwarningAsError=true','--run',
            str(core/'tools/SourceImports.lean'),str(request),str(output)],core)
    observed = read_json(output)
    if not isinstance(observed,list) or len(observed) != len(requests):
        raise ValueError('actual source-import response roster')
    result = {}
    for expected,row in zip(requests,observed):
        if not isinstance(row,dict) or set(row) != {'module','source','isModule','imports'} or any(row[k] != expected[k] for k in ['module','source']):
            raise ValueError('actual source-import response identity')
        if type(row['isModule']) is not bool or not isinstance(row['imports'],list):
            raise ValueError('actual source-import response schema')
        for imported in row['imports']: name(imported)
        result[row['module']] = row
    return result


def module_sources(attempt, root):
    result = {}
    for base, dirs, files in os.walk(attempt, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {'.lake','.git','__pycache__'}]
        if any((Path(base)/d).is_symlink() for d in dirs):
            raise ValueError('own source directory symlink rejected')
        for filename in files:
            p = Path(base)/filename
            if p.suffix != '.lean' or p.name == 'lakefile.lean': continue
            if p.is_symlink() or not p.resolve().is_relative_to(attempt):
                raise ValueError('own attempt source symlink/path rejected')
            if forbidden(p.read_text(encoding='utf-8')): raise ValueError('prohibited active source token: '+str(p))
            module = '.'.join(p.relative_to(attempt).with_suffix('').parts)
            name(module)
            if module != 'Attempt' and not module.startswith('Attempt.'):
                raise ValueError('own modules must be Attempt or Attempt.*; installed module shadow rejected')
            result[module] = p
    if 'Attempt' not in result: raise ValueError('Attempt.lean required')
    imports = source_imports(attempt,root,'source-order',result)
    ordered, visiting, seen = [], set(), set()
    def visit(n):
        if n in seen: return
        if n in visiting: raise ValueError('cyclic own module imports')
        visiting.add(n)
        for imported in imports[n]['imports']:
            if imported in result: visit(imported)
        visiting.remove(n); seen.add(n); ordered.append((n,result[n]))
    for n in sorted(result): visit(n)
    return ordered


def compile_source(attempt, root, label, source, module, overrides):
    core = Path(read_json(attempt/'attempt.json')['core']).resolve()
    header = source_imports(attempt,root,label+'-header',{module:source})[module]
    for imported in header['imports']:
        local = attempt/Path(*imported.split('.')).with_suffix('.lean')
        if local.is_file() and imported != module and imported not in overrides:
            raise ValueError('own actual import not freshly compiled before consumer: '+imported)
    # Execute the verified installed CORE workspace, never an attempt's Lake code
    # or .lake search path. Own objects are supplied solely by explicit overrides.
    setup = {'name':module,'isModule':header['isModule'],'options':{},
             'plugins':[],'dynlibs':[],'importArts':dict(overrides)}
    for key, parts in setup['importArts'].items():
        setup['importArts'][key] = [str((Path(p) if Path(p).is_absolute() else attempt/Path(p)).resolve()) for p in parts]
    setup_path = root/(label+'.setup.json')
    setup_path.write_text(json.dumps(setup,indent=2)+'\n',encoding='utf-8')
    shutil.copyfile(source,root/(label+'.source.lean.txt'))
    inputs = [pin(Path(p).resolve()) for parts in setup['importArts'].values() for p in parts]
    (root/(label+'.inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')
    output = root/(module+'.olean')
    command(root,label+'-compile',['lake','env','lean','-DwarningAsError=true','--root='+str(attempt),'--setup='+str(setup_path),'-o',str(output),str(source)],core)
    parts = [p for p in [output,Path(str(output)+'.server'),Path(str(output)+'.private')] if p.is_file()]
    if not parts: raise RuntimeError('compiler emitted no object')
    (root/(label+'.parts.json')).write_text(json.dumps([pin(p) for p in parts],indent=2)+'\n',encoding='utf-8')
    return [str(p) for p in parts]


def guard_body(proof, expected):
    source = guard_source(proof,expected)
    header = 'import ConditionalSeparation.OpenProblem\nimport Attempt\nimport Lean\n'
    if not source.startswith(header): raise RuntimeError('guard header identity')
    return source[len(header):]


def check(attempt, proof, *, expected='ConditionalSeparation.OpenProblem.R', assemble=True):
    """`expected=True`-style internal fixtures test validation, never prove R."""
    attempt = Path(attempt).resolve()
    core = Path(read_json(attempt/'attempt.json')['core']).resolve()
    fingerprint = verify_core(core)
    root = attempt/'.lake/conditional-check/runs'/str(uuid.uuid4())
    root.mkdir(parents=True)
    (root/'STATUS.json').write_text(json.dumps({'status':'STARTED_NOT_PASS','core_source_inventory_sha256':fingerprint})+'\n')
    overrides = {}
    for i,(module,source) in enumerate(module_sources(attempt,root)):
        overrides[module] = compile_source(attempt,root,'own-'+str(i),source,module,overrides)
    consumer = attempt/'.lake/conditional-check/Consumer.lean'
    consumer.write_text(guard_source(proof,expected),encoding='utf-8')
    compile_source(attempt,root,'exact-closed-guard',consumer,'Consumer',overrides)
    log = (root/'exact-closed-guard-compile/stdout.txt').read_text(encoding='utf-8')
    roots = re.findall(r'\[CS_ROOT\] ([^\s]+)',log)
    axioms = re.findall(r'\[CS_AXIOM\] ([^\s]+)',log)
    if roots != [proof] or not set(axioms) <= ALLOWED:
        raise RuntimeError('exact direct-root/axiom protocol differs')
    if assemble:
        assembly = attempt/'.lake/conditional-check/Assembly.lean'
        proposition = '''∃ k : Nat,
  UniformClassBridgeClosure.Ordinary.UniformNP
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  ¬ Pnp3.ComplexityInterfaces.PpolyDAG
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  ¬ UniformClassBridgeClosure.Ordinary.UniformP
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)))'''
        body = 'import ConditionalSeparation.Conditional\nimport Attempt\nimport Lean\nopen Pnp4.Frontier.ContractExpansion\nnamespace AttemptAssembly\n'
        body += f'theorem complete : {proposition} := ConditionalSeparation.close {proof}\n'
        body += f'theorem check_complete : {proposition} := complete\nend AttemptAssembly\n'
        body += guard_body('AttemptAssembly.complete',proposition)
        body += guard_body('AttemptAssembly.check_complete',proposition)
        assembly.write_text(body,encoding='utf-8')
        compile_source(attempt,root,'final-assembly',assembly,'Assembly',overrides)
    result = {'status':'CLOSED_R_AND_ASSEMBLY' if assemble else 'INTERNAL_GENERIC_VALIDATOR_ONLY',
              'proof':proof,'axioms':axioms,'core_source_inventory_sha256':fingerprint,'receipts':str(root)}
    (root/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode',required=True)
    new = sub.add_parser('new'); new.add_argument('directory',type=Path); new.add_argument('--core',required=True,type=Path)
    export = sub.add_parser('archive'); export.add_argument('--core',required=True,type=Path); export.add_argument('--output',required=True,type=Path)
    verify = sub.add_parser('verify-core'); verify.add_argument('--core',required=True,type=Path)
    final = sub.add_parser('check'); final.add_argument('directory',type=Path); final.add_argument('--proof',default='Attempt.research_lower_bound')
    args = parser.parse_args()
    if args.mode == 'new':
        print(json.dumps({'status':'PARTIAL_NO_PROOF_OF_R','directory':str(create(args.directory,args.core))}))
    elif args.mode == 'verify-core':
        print(json.dumps({'source_identity':verify_core(args.core),'status':'SOURCE_IDENTITY_ONLY_NOT_BUILD_OR_R_PROOF'}))
    elif args.mode == 'archive':
        core = args.core.resolve(); verify_core(core)
        inventory = json.loads((core/'PACKAGE_FILES.json').read_text(encoding='utf-8'))
        with zipfile.ZipFile(args.output,'x',compression=zipfile.ZIP_DEFLATED) as archive:
            for row in inventory['files']:
                archive.write(core/row['path'],row['path'])
            archive.write(core/'PACKAGE_FILES.json','PACKAGE_FILES.json')
        print(json.dumps({'source_archive':str(args.output),'files':len(inventory['files'])+1,'owned_objects':0}))
    else:
        try: print(json.dumps(check(args.directory,name(args.proof))))
        except (RuntimeError,ValueError,OSError) as error:
            print('REJECTED_OR_FAILED: '+str(error),file=sys.stderr); return 1
    return 0


if __name__ == '__main__': raise SystemExit(main())
