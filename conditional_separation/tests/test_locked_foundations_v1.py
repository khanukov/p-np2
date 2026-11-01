"""Inert function DATA: explicit locked acquisition, not real Lake/network."""
import ast
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
SOURCE = Path(__file__).resolve().parents[1] / 'ci/native_ci_v1.py'
if '--source' in sys.argv:
    i = sys.argv.index('--source'); SOURCE = Path(sys.argv[i + 1]); del sys.argv[i:i + 2]

class LockedFoundations(unittest.TestCase):
    def scenario(self, mode='normal'):
        temporary = tempfile.TemporaryDirectory(prefix='locked-foundations-')
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        package = root / 'package'; package.mkdir()
        work = root / 'work'; work.mkdir()
        lock = package / 'lake-manifest.json'; lock.write_text('{"locked":"fixture"}')
        rows = [{'name':'mathlib','rev':'1' * 40}, {'name':'batteries','rev':'2' * 40}]
        events = []
        def require(ok, why):
            if not ok: raise ValueError(why)
        def own_objects(): return list(package.rglob('*.olean'))
        def materialize():
            for row in rows:
                p = package / '.lake/packages' / row['name']; p.mkdir(parents=True, exist_ok=True)
                (p / 'HEAD').write_text(row['rev'])
            if mode == 'revision': (package / '.lake/packages/mathlib/HEAD').write_text('9' * 40)
        def command(name, argv, cwd):
            events.append((name, argv, cwd))
            require(cwd == package or cwd.is_relative_to(package / '.lake/packages'), 'unexpected cwd')
            if name == 'locked-dependency-materialization':
                require(argv == ['lake','env',sys.executable,'-c','pass'], 'exact acquisition command')
                require(not (package / '.lake/packages').exists(), 'fresh empty dependency tree')
                materialize()
                if mode == 'lock': lock.write_text('mutated')
                if mode == 'injected': (package / 'bad.olean').write_bytes(b'not an object')
            elif name == 'lean-version':
                materialize()  # Old Lake env can acquire too; do not simulate inevitable failure.
                return 'Lean (version 4.22.0-rc2)'
            elif name.startswith('dependency-'):
                require(argv == ['git','rev-parse','HEAD'], 'revision check')
                return (cwd / 'HEAD').read_text()
            elif name == 'external-foundation-cache':
                require(cwd == package and argv == ['lake','exe','cache','get'], 'package cache cwd')
            elif name != 'source-identity': raise ValueError('unadmitted command')
            return ''
        tree = ast.parse(SOURCE.read_text())
        selected = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'foundations']
        self.assertEqual(len(selected), 1)
        g = dict(PACKAGE=package, WORK=work, sys=sys, require=require,
                 exact_source=lambda: rows, command=command, own_objects=own_objects,
                 digest=lambda p: hashlib.sha256(p.read_bytes()).hexdigest(),
                 save=lambda p,v: p.write_text(json.dumps(v)))
        exec(compile(ast.Module(body=selected,type_ignores=[]),str(SOURCE),'exec'),g)
        if mode == 'before': (package / 'before.olean').write_bytes(b'not an object')
        return g['foundations'], events, package, work
    def test_explicit_fresh_acquisition_before_checks(self):
        run, events, package, work = self.scenario(); run()
        self.assertEqual(events[0][0], 'locked-dependency-materialization')
        self.assertEqual(events[1][0], 'lean-version')
        self.assertTrue((package / '.lake/packages/mathlib/HEAD').is_file())
        self.assertTrue((work / 'FOUNDATIONS.json').is_file())
    def test_lock_mutation_rejected(self):
        run,_,_,_ = self.scenario('lock')
        with self.assertRaisesRegex(ValueError,'manifest changed'): run()
    def test_wrong_revision_rejected(self):
        run,_,_,_ = self.scenario('revision')
        with self.assertRaisesRegex(ValueError,'commit mismatch'): run()
    def test_owned_object_before_acquisition_rejected(self):
        run,events,_,_ = self.scenario('before')
        with self.assertRaisesRegex(ValueError,'project object'): run()
        self.assertEqual(events, [])
    def test_owned_object_from_acquisition_rejected(self):
        run,_,_,_ = self.scenario('injected')
        with self.assertRaisesRegex(ValueError,'project object'): run()
    def test_cache_in_package_workspace(self):
        run,events,package,_ = self.scenario(); run()
        self.assertEqual([x[2] for x in events if x[0]=='external-foundation-cache'],[package])

if __name__ == '__main__': unittest.main()
