"""Bounded candidate → actual Lean feedback → repair loop. No LLM audit gate."""
import argparse
import time
from pathlib import Path
from . import kernel as K
from . import backend


def candidate_request(goal, goal_path, goal_sha, validation, *, mode, polarity, round_, feedback):
    """Required exact context first; only optional feedback may lose bytes.

    These are instructions to a trusted candidate, NOT an OS path allowlist.
    The outer frozen-goal/dependency/compiler checks remain the authority.
    """
    from idea_search_machine.tools.extract_routes import REPO_ROOT, current_context
    core = Path(goal['core']).resolve()
    sources = []
    for module in goal['spec']['imports']:
        relative = Path(*module.split('.')).with_suffix('.lean')
        found = [p for p in (core/relative, core/'core'/relative) if p.is_file()]
        if len(found) != 1:
            raise ValueError('candidate source lookup requires one installed source: '+module)
        sources.append(found[0])
    sources += [REPO_ROOT/p for p in (
        'conditional_separation/ConditionalSeparation/OpenProblem.lean',
        'research/lengthwise_search/Attempt/RNormalForm.lean',
        'research/solver_to_dag/Attempt/LowerBound.lean')]
    scope = dict(installed_core=str(core), frozen_goal=K.pin(goal_path),
                 target=goal['target'], validation=validation,
                 sources=[K.pin(p) for p in dict.fromkeys(sources)])
    request = dict(schema='idea-pilot-candidate-v1', goal_sha256=goal_sha,
        pre_candidate_validation=validation, statement=goal['spec']['statement'],
        imports=goal['spec']['imports'], model=goal['spec']['model'],
        research_role=goal['spec']['role'], polarity=polarity, round=round_,
        read_scope=scope, feedback='', feedback_truncated=False,
        instructions='Return JSON {"proof":"tactic body without by"}. Prove the ENTIRE '
        'closed statement, or ENTIRE Not(statement) for refute. No new assumptions, imports, '
        'declarations or placeholders. Use fully qualified names. Read only the exact frozen '
        'goal/target/validation and listed source files; use bounded reads or rg -n on those '
        'files directly. installed_core locates the admitted context, NOT permission to scan '
        'its directory. Do not search /root, /root/reports, corpora or history recursively; '
        'do not read credentials, provider transcripts, other sessions/agents, or either '
        'October19 part-a-v1 raw/runtime report tree. No network or other model/agent calls. '
        'Do not edit files, compile, build, install or run Lake/workbench: the OUTER loop '
        'owns compilation and returns feedback. If references are insufficient, report '
        'that limitation rather than searching elsewhere. These advice/read-scope rules '
        'are not a hostile-code sandbox; a custom candidate command remains trusted.')
    request['route_context'] = (current_context() if mode == 'integrated' else
        'Direct Codex + same frozen goal/workbench and source references; no route/audit augmentation.')
    if len(backend.request_bytes(request)) > backend.REQUEST_LIMIT:
        raise ValueError('required candidate context exceeds 9000 UTF-8 bytes; no provider launched')
    request['feedback'] = feedback
    if len(backend.request_bytes(request)) > backend.REQUEST_LIMIT:
        request['feedback_truncated'] = True
        # Bound the optional tail by the actual serialized JSON bytes, including
        # Unicode, escaping and newline. Never slice statement/imports/primary context.
        tail = feedback[-backend.REQUEST_LIMIT:]
        lo, hi = 0, len(tail)
        while lo < hi:
            mid = (lo+hi+1)//2
            request['feedback'] = tail[-mid:]
            if len(backend.request_bytes(request)) <= backend.REQUEST_LIMIT:
                lo = mid
            else:
                hi = mid-1
        request['feedback'] = tail[-lo:] if lo else ''
    return request


def run(goal_path, goal_sha, cfg, output, *, calls=2, negate=False, mode='integrated'):
    if type(calls) is not int or not 1 <= calls <= 10 or mode not in {'integrated', 'direct'}:
        raise ValueError('explicit finite calls (1..10) and comparison mode required')
    backend.config(cfg)
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    controls = K.runtime_controls()
    record = {'schema': 'idea-pilot-run-v1', 'goal': {'path':str(goal_path),'sha256':goal_sha},
              'status': 'UNKNOWN', 'technical_reason': 'budget', 'mode': mode,
              'calls_budget': calls, 'optional_negation': negate,
              'requested_model': cfg.get('model'), 'requested_effort': cfg.get('effort'),
              'verified_actual_model': None, 'price_record': None, 'cost': None,
              'provider_kind': cfg['kind'], 'rounds': [], 'controls': controls,
              'source_approval': False, 'R_success': False}
    started = time.monotonic()
    feedback = 'No candidate attempted.'
    try:
        goal = K.frozen(goal_path, goal_sha)
        record['observed_goal'] = K.pin(goal_path)
        # No candidate may be generated before the literal goal elaborates.
        K.validate_goal(goal_path, goal_sha, output/'goal-validation')
        validation = K.pin(output/'goal-validation/VALIDATED.json')
        dependencies = K.read(output/'goal-validation/DEPENDENCIES.json')['files']
        for i in range(calls):
            polarity = 'refute' if negate and i % 2 else 'prove'
            request = candidate_request(goal, goal_path, goal_sha, validation,
                mode=mode, polarity=polarity, round_=i, feedback=feedback)
            body, provider = backend.generate(cfg, request, output/f'candidate-{i:02d}')
            # Trusted command may still misbehave: recheck the independent inputs.
            K.frozen(goal_path, goal_sha)
            if K.runtime_controls() != controls:
                raise ValueError('probe control set changed')
            for dependency in dependencies:
                if str(Path(dependency['reported_path']).resolve()) != dependency['resolved']['path']:
                    raise ValueError('reported dependency alias changed')
                K.match(dependency['resolved'])
            for row in controls+[validation]+request['read_scope']['sources']:
                K.match(row)
            row = {'candidate': K.pin(output/f'candidate-{i:02d}'/'PROVIDER.json'),
                   'polarity': polarity, 'provider_OS_exit': provider['OS_exit'],
                   'provider_seconds': provider['elapsed_seconds']}
            if body is None:
                feedback = 'Candidate timeout/failure/malformed response; no mathematical result.'
                record['technical_reason'] = 'candidate_timeout' if provider['timeout'] else 'candidate_failure'
            else:
                checked = K.evaluate(goal_path, goal_sha, body, polarity, output/f'kernel-{i:02d}')
                artifact = K.pin(output/f'kernel-{i:02d}'/'RESULT.json')
                K.verify_outcome(artifact['path'], artifact['sha256'], goal_sha)
                row['kernel'] = artifact
                row['mathematical_status'] = checked['status']
                feedback = checked['technical_reason'] or checked['status']
                if checked['status'] == 'UNKNOWN':
                    record['technical_reason'] = checked['technical_reason']
                    # Actual compiler feedback, never just an LLM critique.
                    logs = sorted((output/f'kernel-{i:02d}').rglob('stderr.txt'))
                    logs += sorted((output/f'kernel-{i:02d}').rglob('stdout.txt'))
                    feedback += '\n'+'\n'.join(p.read_text(errors='replace')[-2000:] for p in logs)
                else:
                    record['status'] = checked['status']
                    record['technical_reason'] = None
            record['rounds'].append(row)
            if record['status'] != 'UNKNOWN':
                break
    except (ValueError, RuntimeError, OSError, KeyError, TypeError) as e:
        record['status'] = 'UNKNOWN'
        record['technical_reason'] = type(e).__name__+': '+str(e)
    record['elapsed_seconds'] = time.monotonic()-started
    record['candidate_calls'] = len(list(output.glob('candidate-*/PROVIDER.json')))
    terminals = sorted(output.rglob('*-compile/terminal.json'))
    record['compiler_calls'] = len(terminals)
    record['compiler_terminals'] = [K.pin(p) for p in terminals]
    record['compiler_OS_exits'] = [K.read(p)['OS_exit'] for p in terminals]
    record['repeat_goal_compiles'] = max(0, len(list(output.rglob('Attempt.Goal.olean')))-1)
    record['evidence_files'] = [K.pin(p) for p in sorted(output.rglob('*'))
                              if p.is_file() and p.suffix in {'.json', '.txt', '.lean'}]
    K.write(output/'RUN.json', record)
    return record


def compare(cohort, cfg, output, calls):
    """Same fixed goals/backend/model/budget/checker; no old markdown baseline.

    Prove-only in both arms; whole-negation is a separate probe --negate case.
    No significance/acceleration claim. Native model identity and price require
    separate parent evidence. A DATA/replay comparison measures only that seam.
    """
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    results = []
    for i, goal in enumerate(cohort):
        for mode in ('direct', 'integrated'):
            result = run(goal['path'], goal['sha256'], cfg, output/f'{i:02d}-{mode}',
                         calls=calls, mode=mode)
            results.append({'goal_sha256': goal['sha256'], 'mode': mode,
                            'run': K.pin(output/f'{i:02d}-{mode}'/'RUN.json'),
                            'status': result['status'], 'seconds': result['elapsed_seconds'],
                            'candidate_calls': result['candidate_calls'],
                            'compiler_calls': result['compiler_calls']})
    summary = {'schema': 'idea-pilot-comparison-v1', 'calls_per_arm': calls,
               'branches': ['prove'], 'optional_negation_exercised': False,
               'provider': cfg, 'verified_model': None, 'cost': None,
               'results': results, 'search_acceleration_established': False,
               'claim': 'descriptive fixed-cohort context comparison, no statistical or novelty claim'}
    K.write(output/'COMPARISON.json', summary)
    return summary


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    f = sub.add_parser('freeze')
    f.add_argument('--spec', type=Path, required=True)
    f.add_argument('--core', type=Path, required=True)
    f.add_argument('--output', type=Path, required=True)
    r = sub.add_parser('probe')
    r.add_argument('--goal', type=Path, required=True)
    r.add_argument('--goal-sha256', required=True)
    r.add_argument('--idea-id')
    r.add_argument('--registry', type=Path, help='Optional existing registry; audit status never gates a probe.')
    c = sub.add_parser('compare')
    c.add_argument('--cohort', type=Path, required=True)
    for parser in (r, c):
        parser.add_argument('--provider', type=Path, required=True)
        parser.add_argument('--output', type=Path, required=True)
        parser.add_argument('--calls', type=int, default=2)
    r.add_argument('--negate', action='store_true')
    a = p.parse_args()
    if a.command == 'freeze':
        result = K.freeze(K.read(a.spec), a.core, a.output)
    elif a.command == 'probe':
        idea = None
        if a.idea_id:
            from idea_search_machine import registry
            if a.registry is None:
                p.error('--idea-id requires explicit --registry')
            registry.REGISTRY_DIR = a.registry.resolve()
            registry.IDEAS_DIR = registry.REGISTRY_DIR/'ideas'
            registry.INDEX_FILE = registry.REGISTRY_DIR/'index.jsonl'
            idea = registry.load_idea(a.idea_id)
        result = run(a.goal, a.goal_sha256, K.read(a.provider), a.output,
                     calls=a.calls, negate=a.negate)
        if idea is not None:
            idea.formal_outcomes[a.goal_sha256] = {
                'run': K.pin(a.output/'RUN.json'), 'status': result['status'],
                'scope': 'exact intermediate goal, not the whole idea or R'}
            registry.save_idea(idea)
    else:
        result = compare(K.read(a.cohort), K.read(a.provider), a.output, a.calls)
    print(__import__('json').dumps({k:v for k,v in result.items() if k not in {'evidence_files','compiler_terminals','rounds','controls'}}, ensure_ascii=False))


if __name__ == '__main__':
    main()
