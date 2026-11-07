"""Finite public-entrypoint/provenance DATA; no Git, network or Lean execution."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
PUBLIC = 'c96d9d72c99120e3775437414417505fd4904a3d'
LOCAL = 'e5dbbe7fd6dee72ae3c3b31a84b54fc1b2727f8f'
REPOSITORY = 'https://github.com/khanukov/p-np2.git'


def fresh(prefix):
    return Path(tempfile.mkdtemp(prefix=prefix, dir=os.environ['CI_DATA_ROOT']))


def load_workbench():
    spec = importlib.util.spec_from_file_location('reproducibility_workbench', ROOT/'tools/workbench.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class PublicEntrypointTests(unittest.TestCase):
    def probe(self, flags=(), contaminated=False):
        """Exact runner; synthetic finite tuple; real, unweakened trust validator.

        Only the fixture's manifest digest is independently rebound as FAKE DATA.
        Its single test validates the complete fixture and starts one Python
        import child. No copy of this outer test enters discovery: depth is one.
        Full production-tuple discovery is exercised separately by the suite.
        """
        work = fresh('public-entrypoint-')
        package = work/'package'
        for directory in ('ci', 'tools', 'tests'):
            (package/directory).mkdir(parents=True)
        bodies = {
            'ci/run_data_tests_v2.py': (ROOT/'ci/run_data_tests_v2.py').read_bytes(),
            'tools/probe.py': b"VALUE = 'SYNTHETIC_IMPORT_DATA'\n",
            'tests/test_public_probe.py': b'''import hashlib, importlib.util, pathlib, subprocess, sys, unittest
ROOT = pathlib.Path(__file__).resolve().parents[1]
def load(relative):
    path = ROOT/relative
    spec = importlib.util.spec_from_file_location('probe_'+path.stem, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module
class VerticalPublicProbe(unittest.TestCase):
    def test_actual_trust_and_inherited_child_import(self):
        guard = load('ci/trusted_controls_v1.py')
        load('tools/probe.py')
        anchor = hashlib.sha256((ROOT/'ci/trusted_controls_v1.py').read_bytes()).hexdigest()
        self.assertIn('tools/probe.py', guard.verify_controls(ROOT, anchor))
        subprocess.run([sys.executable, '-c', "import importlib.util; s=importlib.util.spec_from_file_location('child_probe','tools/probe.py'); m=importlib.util.module_from_spec(s); s.loader.exec_module(m)"], cwd=ROOT, check=True)
        self.assertEqual(list(ROOT.rglob('__pycache__')), [])
''',
        }
        for name, raw in bodies.items():
            (package/name).write_bytes(raw)
        manifest = {'schema':'trusted-native-controls-v1',
                    'seed_revision':'9c8e998457514fbf3f2dba5cc3a0edf362010571',
                    'files':[dict(path=name, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
                             for name,raw in sorted(bodies.items())]}
        raw = (json.dumps(manifest, sort_keys=True)+'\n').encode()
        (package/'ci/TRUSTED_NATIVE_CONTROLS_V1.json').write_bytes(raw)
        guard = (ROOT/'ci/trusted_controls_v1.py').read_text()
        guard, count = re.subn(r"(?m)^MANIFEST_SHA256 = '[0-9a-f]{64}'$",
                               "MANIFEST_SHA256 = '"+hashlib.sha256(raw).hexdigest()+"'", guard)
        self.assertEqual(count, 1)
        (package/'ci/trusted_controls_v1.py').write_text(guard)
        (package/'ci/conditional-separation-native-v2.yml').write_text('SYNTHETIC DATA; NOT A WORKFLOW\n')
        if contaminated:
            cache = package/'tools/__pycache__'
            cache.mkdir()
            (cache/'untrusted.pyc').write_bytes(b'SYNTHETIC UNTRUSTED BYTECODE; NEVER EXECUTED')
        env = os.environ.copy()
        for key in ('PYTHONDONTWRITEBYTECODE','PYTHONPYCACHEPREFIX','PYTHONOPTIMIZE','CI_DATA_ROOT'):
            env.pop(key, None)
        env['TMPDIR'] = str(work)
        argv = [sys.executable, *flags, 'ci/run_data_tests_v2.py']
        start = datetime.now(timezone.utc).isoformat()
        with (work/'stdout.txt').open('wb') as out, (work/'stderr.txt').open('wb') as err:
            result = subprocess.run(argv, cwd=package, env=env, stdout=out, stderr=err)
        record = dict(argv=argv, cwd=str(package), start_UTC=start,
                      end_UTC=datetime.now(timezone.utc).isoformat(), actual_OS_exit=result.returncode,
                      synthetic_tuple=True, recursion_depth=1,
                      cleared_environment=['PYTHONDONTWRITEBYTECODE','PYTHONPYCACHEPREFIX','PYTHONOPTIMIZE','CI_DATA_ROOT'])
        for name in ('stdout.txt','stderr.txt'):
            data=(work/name).read_bytes()
            record[name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        (work/'wait.json').write_text(json.dumps(record,indent=2)+'\n')
        return result.returncode, package, (work/'stderr.txt').read_text()

    def test_fresh_plain_public_entrypoint(self):
        code, package, stderr = self.probe()
        self.assertEqual(code, 0, stderr)
        self.assertEqual(list(package.rglob('__pycache__')), [])

    def test_fresh_B_public_entrypoint(self):
        code, package, stderr = self.probe(('-B',))
        self.assertEqual(code, 0, stderr)
        self.assertEqual(list(package.rglob('__pycache__')), [])

    def test_preexisting_bytecode_is_still_rejected(self):
        for flags in ((), ('-B',)):
            with self.subTest(flags=flags):
                code, package, stderr = self.probe(flags, contaminated=True)
                self.assertNotEqual(code, 0)
                self.assertIn('unknown control directory, bytecode or alias', stderr)
                self.assertTrue((package/'tools/__pycache__/untrusted.pyc').is_file())

    def test_optimized_public_entrypoint_is_rejected(self):
        code, _, stderr = self.probe(('-O',))
        self.assertNotEqual(code, 0)
        self.assertIn('optimized unit runner rejected', stderr)


class PublicProvenanceTests(unittest.TestCase):
    def test_package_public_mapping(self):
        value = json.loads((ROOT/'PROVENANCE.json').read_bytes())
        self.assertEqual(value['schema'], 'conditional-separation-public-core-v2')
        self.assertEqual(value['source_repository'], REPOSITORY)
        self.assertEqual(value['source_commit'], PUBLIC)
        self.assertEqual(value['historical_origin'], {'donor_commit':LOCAL,'visibility':'local-non-public',
                                                    'source_path_field':'donor_relative'})
        self.assertEqual(len(value['modules']), 1062)
        for row in value['modules']:
            with self.subTest(path=row['path']):
                self.assertEqual(row['source_relative'], 'conditional_separation/'+row['path'])
                data = (ROOT/row['path']).read_bytes()
                self.assertEqual(len(data),row['bytes'])
                self.assertEqual(hashlib.sha256(data).hexdigest(),row['sha256'])

    def fixture(self):
        root=fresh('provenance-')
        data=b'-- SYNTHETIC provenance DATA, never compiled\n'
        path='core/Pnp4/Fixture.lean'
        (root/path).parent.mkdir(parents=True)
        (root/path).write_bytes(data)
        (root/'lean-toolchain').write_text('leanprover/lean4:v4.22.0-rc2\n')
        value={'schema':'conditional-separation-public-core-v2','source_repository':REPOSITORY,
               'source_commit':PUBLIC,'historical_origin':{'donor_commit':LOCAL,'visibility':'local-non-public',
               'source_path_field':'donor_relative'},'copy_exception':'SYNTHETIC DATA, not acceptance',
               'not_declaration_minimum':True,'modules':[{'module':'Pnp4.Fixture','path':path,
               'source_relative':'conditional_separation/'+path,'donor_relative':'pnp4/Pnp4/Fixture.lean',
               'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'physical_lines':1,'imports':[]}]}
        self.save(root,value)
        return root,value

    def save(self, root, value):
        (root/'PROVENANCE.json').write_text(json.dumps(value))
        rows=[]
        for name in ('PROVENANCE.json','lean-toolchain',value['modules'][0]['path']):
            raw=(root/name).read_bytes()
            rows.append(dict(path=name,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
        (root/'PACKAGE_FILES.json').write_text(json.dumps({'schema':'conditional-separation-source-files-v1','files':sorted(rows,key=lambda r:r['path'])}))

    def test_strict_public_provenance_valid(self):
        root, _ = self.fixture()
        self.assertRegex(load_workbench().verify_core(root), r'^[0-9a-f]{64}$')

    def test_public_and_historical_roles_fail_closed(self):
        root, value = self.fixture()
        changes=[lambda d:d.update(schema='conditional-separation-exact-core-v1'),
                 lambda d:d.update(source_repository='file:///LOCAL'),
                 lambda d:d.update(source_commit='0'*40),
                 lambda d:d.update(ignored='not allowed'),
                 lambda d:d['historical_origin'].update(visibility='public'),
                 lambda d:d['historical_origin'].update(donor_commit='0'*40),
                 lambda d:d['historical_origin'].update(ignored=True),
                 lambda d:d['modules'][0].update(source_relative='../escape'),
                 lambda d:d['modules'][0].update(source_relative='conditional_separation/core/Other.lean'),
                 lambda d:d['modules'][0].update(donor_relative='arbitrary/file'),
                 lambda d:d['modules'][0].update(bytes=True),
                 lambda d:d['modules'].append(copy.deepcopy(d['modules'][0]))]
        wb=load_workbench()
        for i,change in enumerate(changes):
            mutated=copy.deepcopy(value);change(mutated)
            self.save(root,mutated)
            with self.subTest(case=i), self.assertRaises(ValueError):wb.verify_core(root)

    def test_duplicate_json_keys_are_rejected(self):
        root, _ = self.fixture()
        path=root/'PROVENANCE.json'
        path.write_text(path.read_text().replace('"source_commit":', '"source_commit":"'+PUBLIC+'", "source_commit":',1))
        with self.assertRaisesRegex(ValueError,'duplicate JSON key'):
            load_workbench().verify_core(root)

    def test_repeated_public_path_is_rejected(self):
        root, value = self.fixture()
        repeated = copy.deepcopy(value['modules'][0])
        repeated['module'] = 'Pnp4.DifferentModule'
        value['modules'].append(repeated)
        self.save(root,value)
        with self.assertRaisesRegex(ValueError,'provenance duplicate module/path'):
            load_workbench().verify_core(root)
