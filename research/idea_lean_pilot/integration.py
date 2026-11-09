"""No-skip real kernel fixtures and DATA candidate loop; caller owns locks.

This uses the actual installed core and real Lean. Providers here are explicitly
synthetic; native model measurements are a separate parent-run command.
"""
import argparse
import re
import shutil
import sys
from pathlib import Path
from . import kernel as K
from . import pilot
from .data_provider import TRUE_PROOF

HERE = Path(__file__).resolve().parent


def fixture_compile(core, output):
    wb = K.load_core(core)
    output.mkdir(parents=True, exist_ok=False)
    attempt = wb.create(output/'attempt', core)
    (attempt/'Attempt').mkdir()
    root = output/'compile'
    root.mkdir()
    overrides = {}
    for module in ('Fixtures', 'Audit'):
        path = attempt/'Attempt'/(module+'.lean')
        shutil.copyfile(HERE/(module+'.lean'), path)
        overrides['Attempt.'+module] = wb.compile_source(
            attempt, root, module, path, 'Attempt.'+module, overrides)
    log = (root/'Audit-compile/stdout.txt').read_text()
    observed = re.findall(r'\[IDEA_PILOT_ROOT\] (\S+)', log)
    expected = ['Research.IdeaLeanPilot.'+n for n in (
        'BudgetWitness', 'AllBoundedAccept', 'budget_witness',
        'not_all_bounded_accept', 'check_budget_witness', 'check_not_all_bounded_accept')]
    if set(observed) != set(expected) or len(observed) != len(expected):
        raise ValueError('actual exact fixture roots differ')
    K.write(output/'ROOTS.json', {'roots': observed, 'audit_stdout': K.pin(root/'Audit-compile/stdout.txt')})
    return observed


def run(core, output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    K.write(output/'SOURCE.json', [K.pin(p) for p in sorted(HERE.iterdir()) if p.is_file()])
    cases = []
    def case(name, action):
        try:
            value = action()
            cases.append({'name': name, 'PASS': True, 'value': value})
            return value
        except Exception as e:
            cases.append({'name': name, 'PASS': False, 'error': repr(e)})
            raise
    result = {'schema': 'idea-pilot-kernel-integration-v1', 'cases': cases,
              'skipped': 0, 'status': 'FAIL', 'provider_kind': 'DATA',
              'real_model_calls': 0, 'not_cold_core': True}
    try:
        roots = case('fixture_public_roots', lambda: fixture_compile(core, output/'fixtures'))
        specs = K.read(HERE/'cohort.json')
        goals = [K.freeze(spec, core, output/f'goal-{i}') for i, spec in enumerate(specs)]
        def cfg(mode):
            return {'kind': 'DATA', 'seconds': 1 if mode == 'timeout' else 30,
                    'argv': [sys.executable, '-B', str(HERE/'data_provider.py'), mode]}
        good = pilot.run(goals[0]['path'], goals[0]['sha256'], cfg('repair'), output/'prove', calls=2)
        case('real_feedback_then_proved', lambda: require(
            good['status']=='PROVED' and len(good['rounds'])==2 and
            good['rounds'][0]['mathematical_status']=='UNKNOWN'))
        bad = pilot.run(goals[1]['path'], goals[1]['sha256'], cfg('repair'), output/'refute', calls=2, negate=True)
        case('entire_quantified_negation_refuted', lambda: require(bad['status']=='REFUTED'))
        unknown = pilot.run(goals[2]['path'], goals[2]['sha256'], cfg('wrong'), output/'open', calls=1)
        case('R_budget_control_unknown', lambda: require(unknown['status']=='UNKNOWN'))
        # Proved partial work must fail the UNCHANGED production final R guard.
        wb = K.load_core(core)
        try:
            wb.check(output/'prove/kernel-01/attempt', 'IdeaPilotCandidate.result')
        except RuntimeError:
            logs = list((output/'prove/kernel-01/attempt').rglob('exact-closed-guard-compile/stdout.txt'))
            case('partial_rejected_by_final_R_guard', lambda: require(any(
                'CLOSED exact expected type' in p.read_text() for p in logs)))
        else:
            raise ValueError('partial proof accepted as R')
        wrong = K.evaluate(goals[0]['path'], goals[0]['sha256'], TRUE_PROOF, 'refute', output/'wrong-polarity')
        case('wrong_polarity_unknown', lambda: require(wrong['status']=='UNKNOWN'))
        for mode in ('timeout', 'missing'):
            got = pilot.run(goals[0]['path'], goals[0]['sha256'], cfg(mode), output/mode, calls=1)
            case(mode+'_unknown', lambda: require(got['status']=='UNKNOWN' and got['candidate_calls']==1))
        artifact = output/'prove/kernel-01/RESULT.json'
        original = K.pin(artifact)
        case('verify_actual_anchored_outcome', lambda: require(
            K.verify_outcome(artifact, original['sha256'], goals[0]['sha256'])['status']=='PROVED'))
        def rejects(d, name, goal_sha=goals[0]['sha256']):
            path=output/(name+'.json')
            K.write(path,d)
            try:
                K.verify_outcome(path,K.pin(path)['sha256'],goal_sha)
            except ValueError:
                return True
            raise ValueError('substituted/missing evidence accepted')
        d=K.read(artifact)
        d.update(status='REFUTED',polarity='refute',expected='IdeaPilotGoal.negation')
        case('relabelled_polarity_receipt_rejected',lambda: rejects(d,'relabelled'))
        d=K.read(artifact)
        d['evidence']=[r for r in d['evidence'] if not r['path'].endswith('exact-closed-guard-compile/terminal.json')]
        case('missing_guard_receipt_rejected',lambda: rejects(d,'missing-receipt'))
        d=K.read(artifact)
        d['evidence'][0]['sha256']='0'*64
        case('changed_evidence_rejected',lambda: rejects(d,'changed-evidence'))
        d=K.read(artifact)
        case('another_goal_receipt_rejected',lambda: rejects(d,'other-goal',goals[1]['sha256']))
        if len(cases)!=13 or not all(c['PASS'] for c in cases):
            raise ValueError('complete no-skip case roster differs')
        result.update(status='PASS', direct_roots=roots,
                      frozen_goals=goals, actual_native_model_measurement='PENDING')
    except Exception as e:
        result['error'] = repr(e)
    finally:
        result['compiler_terminals'] = [K.pin(p) for p in sorted(output.rglob('*-compile/terminal.json'))]
        result['compiler_OS_exits'] = [K.read(p['path'])['OS_exit'] for p in result['compiler_terminals']]
        result['actual_cases'] = len(cases)
        K.write(output/'INTEGRATION.json', result)
    return result


def require(value):
    if value is not True:
        raise ValueError('actual acceptance condition failed')
    return True


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--core', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    result = run(a.core.resolve(), a.output)
    print({k:v for k,v in result.items() if k not in {'compiler_terminals','cases'}})
    raise SystemExit(0 if result['status']=='PASS' else 1)


if __name__ == '__main__':
    main()
