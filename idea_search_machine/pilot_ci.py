"""Small no-skip DATA runner; real kernel integration is a separate CI command."""
import argparse
import json
import sys
import unittest
from pathlib import Path

MODULES = ['idea_search_machine.tests.test_current_context',
           'research.idea_lean_pilot.test_pilot', 'research.idea_lean_pilot.test_request',
           'idea_search_machine.tests.test_smoke',
           'idea_search_machine.tests.test_pilot_ci']


def ids(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from ids(item)
        else:
            yield item.id()


def run_suite(suite, output, expected_ids):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    observed = list(ids(suite))
    with (output/'unittest.txt').open('x') as stream:
        r = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    ok = (r.wasSuccessful() and not r.skipped and not r.expectedFailures and
          not r.unexpectedSuccesses and r.testsRun == len(expected_ids) and
          len(observed) == len(set(observed)) and set(observed) == set(expected_ids))
    result = {'schema':'idea-pilot-DATA-v1','PASS':ok,'test_ids':observed,
              'expected_ids':sorted(expected_ids),'tests':r.testsRun,
              'failures':[(t.id(),s) for t,s in r.failures],
              'errors':[(t.id(),s) for t,s in r.errors],
              'skipped':[(t.id(),s) for t,s in r.skipped],
              'expected_failures':len(r.expectedFailures),
              'unexpected_successes':len(r.unexpectedSuccesses)}
    with (output/'DATA.json').open('x') as f:
        json.dump(result,f,indent=2); f.write('\n')
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    suite=unittest.defaultTestLoader.loadTestsFromNames(MODULES)
    # The shipped roster is literal source metadata, never inferred from success.
    roster=json.loads((Path(__file__).parent/'tests/pilot_test_ids.json').read_bytes())
    r=run_suite(suite,a.output,roster)
    print({k:r[k] for k in ('PASS','tests','skipped')})
    raise SystemExit(0 if r['PASS'] else 1)


if __name__=='__main__':
    main()
