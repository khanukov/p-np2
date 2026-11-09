"""Thin frozen-goal adapter to the unchanged workbench, not a hostile-code sandbox.

The operator, installed core, compiler/dependencies and candidate executable are
trusted. A proof body cannot supply the goal, imports, checker or receipts.
"""
import hashlib
import json
import os
import re
import shutil
import sys
import types
from pathlib import Path

sys.dont_write_bytecode = True
WB_SHA = '0dceab37e05c901b37b7aadc9c5759dbd4e77659b8f98d43d30ce1ff69c0706c'
INV_SHA = '5f833d26620edc0404130be1ac445da0cb9f6a89599af1894fca94faf543c9a3'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path):
    p = Path(path)
    if p.is_symlink() or not p.is_file():
        raise ValueError('regular non-symlink file required: '+str(p))
    b = p.read_bytes()
    return {'path': str(p.resolve()), 'bytes': len(b), 'sha256': digest(b)}


def read(path):
    def pairs(items):
        d = {}
        for k, v in items:
            if k in d:
                raise ValueError('duplicate JSON key')
            d[k] = v
        return d
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs)


def write(path, obj):
    with Path(path).open('x', encoding='utf-8') as f:
        json.dump(obj, f, indent=2, ensure_ascii=False)
        f.write('\n')


def runtime_controls():
    here=Path(__file__).resolve().parent
    machine=here.parents[1]/'idea_search_machine'
    paths=list(here.glob('*.py'))+[machine/p for p in
          ['tools/extract_routes.py','registry.py','probe.py']]
    return [pin(p) for p in sorted(paths)]


def match(row):
    if pin(row['path']) != row:
        raise ValueError('changed evidence/context: '+row['path'])


def load_core(core):
    """Execute the SAME authenticated bytes, before borrowing any Python code.

    Known public core version 1180e5e0, not an untrusted self-signed manifest.
    Its stdlib-only loader verifies every source, including SourceImports.lean.
    The installed core/dependencies must remain immutable and nonconcurrent.
    """
    core = Path(core).resolve()
    checked = {}
    for relative, size, sha in [('tools/workbench.py', 25755, WB_SHA),
                                ('PACKAGE_FILES.json', 209612, INV_SHA)]:
        p = core/relative
        if p.resolve() != p or p.is_symlink():
            raise ValueError('installed source alias')
        raw = p.read_bytes()
        if len(raw) != size or digest(raw) != sha:
            raise ValueError('untrusted installed source identity: '+relative)
        checked[relative] = raw
    wb = types.ModuleType('idea_pilot_trusted_workbench')
    wb.__file__ = str(core/'tools/workbench.py')
    exec(compile(checked['tools/workbench.py'], wb.__file__, 'exec'), wb.__dict__)
    wb.verify_core(core)
    return wb


def proof_body(text):
    if not isinstance(text, str) or not text.strip() or len(text) > 16000:
        raise ValueError('bounded nonempty tactic body required')
    # Narrow tactic-body protocol; full Lean programs/plugins are not accepted.
    # This lexical restriction complements, never replaces, the kernel guard.
    words = set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*', text))
    blocked = {'import', 'namespace', 'end', 'theorem', 'lemma', 'def', 'abbrev',
               'axiom', 'sorry', 'admit', 'native_decide', 'unsafe', 'opaque',
               'constant', 'structure', 'class', 'instance', 'syntax', 'macro',
               'elab', 'run_cmd', 'run_tac', 'initialize', 'set_option',
               'attribute', 'notation', 'open', 'export', 'include', 'variable'}
    if words & blocked or any(c in text for c in ['#', '`', '"', '\x00']):
        raise ValueError('candidate is a tactic body, not declarations or commands')
    return text


def goal_source(spec):
    return ('\n'.join('import '+m for m in spec['imports'])+
            '\nnamespace IdeaPilotGoal\ndef statement : Prop :=\n'+
            spec['statement']+'\ndef negation : Prop := Not statement\n'+
            '#check (statement : Prop)\n#check (negation : Prop)\n'+
            '#print axioms statement\n#print axioms negation\nend IdeaPilotGoal\n')


def freeze(spec, core, destination):
    """Operator action BEFORE generation. Caller saves returned external SHA."""
    if not isinstance(spec, dict) or set(spec) != {'name', 'statement', 'imports', 'model', 'role'}:
        raise ValueError('exact goal specification schema')
    if any(not isinstance(spec[k], str) or not spec[k].strip() for k in ['name', 'statement', 'model', 'role']):
        raise ValueError('literal goal/model/role required')
    if not isinstance(spec['imports'], list) or not spec['imports'] or len(set(spec['imports'])) != len(spec['imports']):
        raise ValueError('explicit distinct imports required')
    if 'ConditionalSeparation.OpenProblem' not in spec['imports']:
        raise ValueError('installed R owner must remain imported')
    wb = load_core(core)
    for m in spec['imports']:
        wb.name(m)
        if m == 'Attempt' or m.startswith('Attempt.'):
            raise ValueError('separate addon Attempt roots are not merged')
    if wb.forbidden(spec['statement']):
        raise ValueError('prohibited goal source')
    destination = Path(destination).absolute()
    destination.mkdir(parents=True, exist_ok=False)
    target = destination/'TARGET.lean'
    target.write_text(goal_source(spec), encoding='utf-8')
    core = Path(core).resolve()
    identity = [pin(core/p) for p in ['PACKAGE_FILES.json', 'tools/workbench.py',
                'tools/SourceImports.lean', 'lean-toolchain', 'lake-manifest.json']]
    compiler = shutil.which('lean')
    if compiler is None:
        raise ValueError('pinned Lean must be on PATH')
    lake = shutil.which('lake')
    if lake is None:
        raise ValueError('pinned Lake must be on PATH')
    document = {'schema': 'idea-pilot-frozen-goal-v1', 'spec': spec,
                'core': str(core), 'core_identity': identity,
                'compiler': pin(Path(compiler).resolve()), 'lake': pin(Path(lake).resolve()), 'target': pin(target),
                'adapter': pin(__file__), 'final_R_authority': False}
    document['probe_controls'] = runtime_controls()
    write(destination/'GOAL.json', document)
    return pin(destination/'GOAL.json')


def frozen(path, expected_sha):
    p = Path(path)
    if pin(p)['sha256'] != expected_sha:
        raise ValueError('external goal hash differs')
    d = read(p)
    if d['schema'] != 'idea-pilot-frozen-goal-v1':
        raise ValueError('goal schema')
    for r in d['core_identity']+[d['compiler'], d['lake'], d['target'], d['adapter']]:
        match(r)
    if d['probe_controls'] != runtime_controls():
        raise ValueError('frozen probe control set or bytes changed')
    if sys.flags.optimize or any(os.environ.get(k) for k in
            ['LEAN_PATH', 'LEAN_SRC_PATH', 'ELAN_TOOLCHAIN', 'PYTHONOPTIMIZE']):
        raise ValueError('clean ordinary compiler environment required')
    for name, key in [('lean', 'compiler'), ('lake', 'lake')]:
        actual = shutil.which(name)
        if actual is None or pin(Path(actual).resolve()) != d[key]:
            raise ValueError('actual compiler command identity differs')
    if Path(d['target']['path']).read_text() != goal_source(d['spec']):
        raise ValueError('literal target does not match frozen goal')
    return d


def new_attempt(wb, goal, output):
    attempt = wb.create(output/'attempt', Path(goal['core']))
    (attempt/'Attempt').mkdir()
    shutil.copyfile(goal['target']['path'], attempt/'Attempt/Goal.lean')
    return attempt


def validate_goal(path, sha, output):
    """Actual source compile before any candidate is requested; not a proof."""
    goal = frozen(path, sha)
    wb = load_core(goal['core'])
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    attempt = new_attempt(wb, goal, output)
    root = output/'compile'
    root.mkdir()
    version = wb.command(root, 'compiler-version', ['lake','env','lean','--version'], Path(goal['core']))
    if 'version 4.22.0-rc2' not in version:
        raise ValueError('actual Lean version differs')
    deps = wb.command(root, 'goal-dependencies', ['lake','env','lean','--deps',
                      str(attempt/'Attempt/Goal.lean')], Path(goal['core']))
    dependency_pins = []
    for s in deps.splitlines():
        if not s.strip():
            continue
        p = Path(s)
        if not p.is_absolute():
            p = Path(goal['core'])/p
        # Admitted reused objects may be symlinks. Source files still may not.
        dependency_pins.append({'reported_path':str(p), 'resolved':pin(p.resolve())})
    write(output/'DEPENDENCIES.json', {'kind':'compiler-reported imports, admitted readonly objects',
                                     'files': dependency_pins})
    wb.compile_source(attempt, root, 'frozen-goal', attempt/'Attempt/Goal.lean',
                      'Attempt.Goal', {})
    frozen(path, sha)
    write(output/'VALIDATED.json', {'goal': pin(path), 'source': goal['target'],
                                   'dependencies': pin(output/'DEPENDENCIES.json'),
                                   'closed_proof': False})


def evaluate(path, sha, body, polarity, output):
    """Only internally produced and externally hash-bound kernel artifacts count.

    Always fresh. Failed compilation/type/axiom checks mean UNKNOWN. Never
    interpret compiler text, a provider exit, or an LLM opinion as a proof.
    """
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    result = {'schema': 'idea-pilot-kernel-result-v1', 'status': 'UNKNOWN',
              'goal_sha256': sha, 'polarity': polarity, 'technical_reason': None,
              'kernel_result': None, 'final_R_success': False}
    try:
        if polarity not in {'prove', 'refute'}:
            raise ValueError('exact prove/refute polarity required')
        goal = frozen(path, sha)
        body = proof_body(body)
        wb = load_core(goal['core'])
        attempt = new_attempt(wb, goal, output)
        target = 'IdeaPilotGoal.'+('statement' if polarity == 'prove' else 'negation')
        literal = goal['spec']['statement']
        proposition = '('+literal+')' if polarity == 'prove' else 'Not ('+literal+')'
        source = ('import Attempt.Goal\nnamespace IdeaPilotCandidate\n'+
                  'theorem result : '+target+' := by\n'+
                  '\n'.join('  '+line for line in body.splitlines())+'\n'+
                  'theorem check_result : '+proposition+' := result\n'+
                  '#print axioms result\n#print axioms check_result\n'+
                  'end IdeaPilotCandidate\n')
        (attempt/'Attempt.lean').write_text(source, encoding='utf-8')
        expected_sources = [pin(attempt/p) for p in ['Attempt.lean', 'Attempt/Goal.lean']]
        checked = wb.check(attempt, 'IdeaPilotCandidate.result', expected=target, assemble=False)
        if checked['status'] != 'INTERNAL_GENERIC_VALIDATOR_ONLY':
            raise ValueError('partial adapter must not acquire final R authority')
        # Retain original kernel RESULT and every real compiler terminal.
        for r in expected_sources:
            match(r)
        frozen(path, sha)
        wb.verify_core(Path(goal['core']))
        result.update(status='PROVED' if polarity == 'prove' else 'REFUTED',
                      kernel_result=pin(Path(checked['receipts'])/'RESULT.json'),
                      expected=target, axioms=checked['axioms'])
    except (ValueError, OSError, RuntimeError, KeyError, TypeError) as error:
        result['technical_reason'] = type(error).__name__+': '+str(error)
    # Sources, actual command receipts and outputs; no mutable provider stream.
    evidence = [pin(p) for p in sorted(output.rglob('*')) if p.is_file()]
    result['evidence'] = evidence
    write(output/'RESULT.json', result)
    return result


def verify_outcome(path, external_result_sha, external_goal_sha):
    """Read-only replay of immutable receipt pins, not another compiler run.

    The result hash MUST come from the trusted caller, not the result itself.
    This is custody of an observed run, not signatures or a hostile-code sandbox.
    """
    if pin(path)['sha256'] != external_result_sha:
        raise ValueError('external result anchor differs')
    d = read(path)
    if d.get('schema') != 'idea-pilot-kernel-result-v1' or d.get('goal_sha256') != external_goal_sha:
        raise ValueError('result/goal identity')
    for row in d['evidence']:
        match(row)
    if d['status'] == 'UNKNOWN':
        return d
    target = {'PROVED': ('prove', 'IdeaPilotGoal.statement'),
              'REFUTED': ('refute', 'IdeaPilotGoal.negation')}
    if d['status'] not in target or (d['polarity'], d['expected']) != target[d['status']]:
        raise ValueError('result polarity or target differs')
    match(d['kernel_result'])
    k = read(d['kernel_result']['path'])
    if (k['status'] != 'INTERNAL_GENERIC_VALIDATOR_ONLY' or
        k['proof'] != 'IdeaPilotCandidate.result' or
        not set(k['axioms']) <= ALLOWED or k['axioms'] != d['axioms']):
        raise ValueError('exact kernel result differs')
    # The success marker must be backed by actual successful guard compilation.
    root = Path(k['receipts'])
    terminal = root/'exact-closed-guard-compile/terminal.json'
    if str(terminal) not in {r['path'] for r in d['evidence']} or read(terminal)['OS_exit'] != 0:
        raise ValueError('missing actual guard terminal')
    consumer = root/'Consumer.lean'
    required = 'let expected ← elabType (← `('+d['expected']+'))'
    if str(consumer) not in {r['path'] for r in d['evidence']} or required not in consumer.read_text():
        raise ValueError('kernel consumer was for another target/polarity')
    return d
