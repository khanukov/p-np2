"""Finite DATA: actual CLI validation and retired proposal refusal; no native build/fetch."""
import datetime
import errno
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
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
WORKBENCH = ROOT/'tools/workbench.py'
WORKFLOW = ROOT/'ci/conditional-separation.yml.proposed'
CLI = '''import pathlib,runpy,sys
source,attempt,marker=sys.argv[1:]
def deny(event,args):
    if event in {'subprocess.Popen','os.system','os.posix_spawn','os.exec','os.spawn'}:
        pathlib.Path(marker).write_text('FORBIDDEN DATA child effect: '+event)
        raise AssertionError('compiler/process effects forbidden in DATA')
sys.addaudithook(deny)
sys.argv=[source,'check',attempt]
runpy.run_path(source,run_name='__main__')
'''
SHELL_TRAPS = r'''
forbidden_source() { printf 'FORBIDDEN DATA source command: %s\n' "$*" >> "$COMMAND_LOG"; return 97; }
git() { forbidden_source git "$@"; }
lake() { forbidden_source lake "$@"; }
python3() { forbidden_source python3 "$@"; }
elan() { forbidden_source elan "$@"; }
lean() { forbidden_source lean "$@"; }
curl() { forbidden_source curl "$@"; }
wget() { forbidden_source wget "$@"; }
'''
RETIRED_HEADER = '''# Retired proposal only; not an installed native workflow.
# No dispatched source, checkout, bootstrap, installer or tests are executed.
# The supported route is the independently admitted conditional-separation-native.yml.
name: conditional-separation-unadmitted-source-refused
on: [workflow_dispatch]
permissions: {}
jobs:
  refuse-unadmitted-source:
    runs-on: ubuntu-24.04
    steps:
      - name: Refuse unadmitted source execution
        shell: bash
        run: |
'''
RETIRED_BODY = "set -euo pipefail\nprintf '%s\\n' 'unadmitted-source-refused: use the independently admitted native controller workflow' >&2\nexit 1\n"


def retired_body(text):
    # Fixed, deliberately tiny refusal policy; unknown steps/keys/commands reject
    # BEFORE the DATA shell is allowed to execute any supplied recipe body.
    expected = RETIRED_HEADER + ''.join('          '+line+'\n' for line in RETIRED_BODY.splitlines())
    if text != expected: raise AssertionError('exact retired no-source-execution recipe required')
    return shell_blocks(text)[0]



def snapshot(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file() and not p.is_symlink()}


def shell_blocks(text):
    blocks = []
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line == '        run: |':
            body = []
            for value in lines[i+1:]:
                if not value.startswith('          '): break
                body.append(value[10:])
            blocks.append('\n'.join(body)+'\n')
    if len(blocks) != 1: raise AssertionError('exact one refusal shell block')
    return blocks


def fixture_environment(extra=None):
    """No ambient/caller Git context, config, executable, trace or object overrides."""
    merged = dict(os.environ)
    merged.update(extra or {})
    clean = {key:value for key,value in merged.items() if not key.upper().startswith('GIT_')}
    clean.update(PYTHONDONTWRITEBYTECODE='1', GIT_CONFIG_NOSYSTEM='1',
                 GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull,
                 GIT_TERMINAL_PROMPT='0')
    return clean


class ReliabilityData(unittest.TestCase):
    def setUp(self):
        self.data = Path(tempfile.mkdtemp(prefix='reliability-', dir=os.environ['CI_DATA_ROOT']))
        self.sequence = 0

    def child(self, argv, cwd=None, env=None):
        self.sequence += 1
        folder = self.data/('child-'+str(self.sequence));folder.mkdir()
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        options = fixture_environment(env)
        result = subprocess.run(argv, cwd=cwd or self.data, env=options,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        (folder/'stdout.txt').write_bytes(result.stdout)
        (folder/'stderr.txt').write_bytes(result.stderr)
        (folder/'wait.json').write_text(json.dumps(dict(
            scope='actual finite DATA child, not a compiler/native receipt',
            argv=argv, cwd=str(cwd or self.data), start=started,
            end=datetime.datetime.now(datetime.timezone.utc).isoformat(), OS_exit=result.returncode,
            stdout_sha256=hashlib.sha256(result.stdout).hexdigest(),
            stderr_sha256=hashlib.sha256(result.stderr).hexdigest()), indent=2)+'\n')
        return result

    def test_cli_malformed_metadata_has_controlled_rejection_without_effects(self):
        cases = [('missing', None, 'attempt.json'), ('object', {}, 'attempt metadata'),
                 ('array', [], 'attempt metadata'), ('null', None, 'attempt metadata'),
                 ('false', False, 'attempt metadata'), ('text', 'DATA', 'attempt metadata'),
                 ('core_bool', {'core': False}, 'attempt metadata'),
                 ('core_array', {'core': []}, 'attempt metadata'),
                 ('core_object', {'core': {}}, 'attempt metadata'),
                 ('core_number', {'core': 1}, 'attempt metadata'),
                 ('empty', {'core': ''}, 'attempt metadata'),
                 ('blank', {'core': ' \t'}, 'attempt metadata'),
                 ('nul', {'core': 'DATA\0path'}, 'attempt metadata'),
                 ('duplicate', '{"core":"a","core":"b"}', 'duplicate JSON key'),
                 ('malformed', '{', 'REJECTED_OR_FAILED')]
        for label, value, diagnostic in cases:
            with self.subTest(case=label):
                attempt = self.data/label;attempt.mkdir()
                if label != 'missing':
                    (attempt/'attempt.json').write_text(value if label in {'duplicate','malformed'} else json.dumps(value))
                before = snapshot(attempt);marker = self.data/(label+'-FORBIDDEN')
                result = self.child([sys.executable,'-B','-c',CLI,str(WORKBENCH),str(attempt),str(marker)])
                self.assertEqual(result.returncode, 1)
                self.assertIn(b'REJECTED_OR_FAILED:', result.stderr)
                self.assertNotIn(b'Traceback', result.stderr)
                self.assertIn(diagnostic.encode(), result.stderr)
                self.assertFalse(marker.exists())
                self.assertEqual(snapshot(attempt), before)
                self.assertFalse((attempt/'.lake').exists())

    def test_all_three_core_readers_validate_before_effects(self):
        spec = importlib.util.spec_from_file_location('reliability_workbench', WORKBENCH)
        wb = importlib.util.module_from_spec(spec);spec.loader.exec_module(wb)
        attempt = self.data/'attempt';attempt.mkdir();(attempt/'attempt.json').write_text('{}')
        with mock.patch.object(wb,'command',side_effect=AssertionError('process')), \
             mock.patch.object(wb,'verify_core',side_effect=AssertionError('verify before metadata')), \
             mock.patch.object(wb,'fresh_check_run',side_effect=AssertionError('write')):
            for method,args in [(wb.check,(attempt,'Attempt.unit')),
                                (wb.source_imports,(attempt,self.data,'DATA',{})),
                                (wb.compile_source,(attempt,self.data,'DATA',self.data/'absent','Attempt',{}))]:
                with self.subTest(reader=method.__name__):
                    with self.assertRaisesRegex(ValueError,'attempt metadata'):
                        method(*args)
        self.assertEqual(set(attempt.iterdir()), {attempt/'attempt.json'})

    def test_valid_core_path_and_duplicate_key_contract(self):
        spec = importlib.util.spec_from_file_location('valid_metadata_workbench', WORKBENCH)
        wb = importlib.util.module_from_spec(spec);spec.loader.exec_module(wb)
        core = self.data/'core DATA with spaces';core.mkdir()
        (self.data/'attempt.json').write_text(json.dumps({'core':str(core),'status':'FAKE_DATA'}))
        self.assertEqual(wb.attempt_core(self.data), core.resolve())
        (self.data/'attempt.json').write_text('{"core":"a","core":"b"}')
        with self.assertRaisesRegex(ValueError,'duplicate JSON key'): wb.attempt_core(self.data)

    def refusal(self, extra=None):
        log = self.data/('refusal-'+str(self.sequence)+'.calls')
        env = dict(COMMAND_LOG=str(log), RUNNER_TEMP=str(self.data), SOURCE_RUN='legacy-selected-source',
                   GITHUB_REPOSITORY='FAKE/DATA', GITHUB_SHA='d'*40)
        env.update(extra or {})
        body = retired_body(WORKFLOW.read_text())
        result = self.child(['bash','--noprofile','--norc','-e','-o','pipefail','-c',SHELL_TRAPS+body],env=env)
        self.assertEqual(result.returncode,1,result.stderr.decode())
        self.assertIn(b'unadmitted-source-refused',result.stderr)
        self.assertFalse(log.exists(),'no source command may run')
        return result

    def test_retired_recipe_has_no_persistent_source_executor(self):
        body = retired_body(WORKFLOW.read_text())
        self.assertEqual(body,RETIRED_BODY)
        self.assertNotIn('self-hosted',WORKFLOW.read_text())
        self.assertNotIn('uses:',WORKFLOW.read_text())
        self.refusal()

    def test_every_selected_head_is_refused_and_prior_workspace_survives(self):
        old = self.data/'checkout';old.mkdir();(old/'previous.DATA').write_text('PRESERVE FAKE DATA')
        before = snapshot(old)
        for head in ['a'*40,'b'*40]:
            with self.subTest(selected_head=head):self.refusal({'GITHUB_SHA':head})
        self.assertEqual(snapshot(old),before)
        self.assertFalse((self.data/'legacy-selected-source').exists())

    def test_git_environment_cannot_redirect_fixture_repository(self):
        outside = self.data/'outside-INERT-DATA';(outside/'.git').mkdir(parents=True)
        config = outside/'.git/config';config.write_text('[core]\n bare = false\n')
        (outside/'sentinel.DATA').write_text('PRESERVE OUTSIDE DATA')
        before = snapshot(outside)
        injected = dict(GIT_DIR=str(outside/'.git'),GIT_WORK_TREE=str(outside),GIT_COMMON_DIR=str(outside/'.git'),
            GIT_INDEX_FILE=str(outside/'index'),GIT_OBJECT_DIRECTORY=str(outside/'.git/objects'),
            GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='core.bare',GIT_CONFIG_VALUE_0='true',
            GIT_EXEC_PATH=str(outside/'absent'),GIT_TRACE=str(outside/'trace'),GIT_CONFIG_GLOBAL=str(config))
        script = "import json,os; print(json.dumps({k:v for k,v in os.environ.items() if k.upper().startswith('GIT_')}))"
        # Actual inert Python child observes the same sanitizer; no Git is run.
        with mock.patch.dict(os.environ,injected):
            result = self.child([sys.executable,'-B','-c',script],env=injected)
        self.assertEqual(result.returncode,0)
        self.assertEqual(json.loads(result.stdout),dict(GIT_CONFIG_NOSYSTEM='1',
            GIT_CONFIG_GLOBAL=os.devnull,GIT_CONFIG_SYSTEM=os.devnull,GIT_TERMINAL_PROMPT='0'))
        self.assertEqual(snapshot(outside),before)
        self.assertFalse((outside/'trace').exists())

    def test_recipe_mutations_reject_before_shell_dispatch(self):
        text = WORKFLOW.read_text()
        mutations = [('ubuntu-24.04','[self-hosted, conditional-separation]'),('permissions: {}','permissions: write-all'),
            ('exit 1','exit 0'),('on: [workflow_dispatch]','on: [pull_request_target]'),
            ("          printf '%s\\n'",'          lake build; printf'),
            ('    steps:','    env: {SOURCE_APPROVED: true}\n    steps:')]
        for old,new in mutations:
            self.assertIn(old,text)
            with self.subTest(mutation=old),self.assertRaises(AssertionError):retired_body(text.replace(old,new,1))
        with self.assertRaises(AssertionError):retired_body(text+'      - run: python3 untrusted.py\n')

    def test_existing_file_directory_and_symlink_paths_are_untouched(self):
        for kind in ['file','directory','symlink','dangling']:
            with self.subTest(path_kind=kind):
                parent=self.data/kind;parent.mkdir();destination=parent/'legacy-selected-source'
                target=parent/'target'
                if kind=='file':destination.write_text('PRESERVE')
                elif kind=='directory':destination.mkdir();(destination/'sentinel.DATA').write_text('PRESERVE')
                else:
                    if kind=='symlink':target.mkdir();(target/'sentinel.DATA').write_text('PRESERVE')
                    try:destination.symlink_to(target,target_is_directory=True)
                    except OSError as error:
                        if error.errno in {errno.EACCES,errno.EPERM,errno.ENOSYS,errno.ENOTSUP}:
                            self.skipTest('symlink capability unavailable: '+str(error))
                        raise
                before=snapshot(parent)
                link=os.readlink(destination)if destination.is_symlink()else None
                self.refusal({'RUNNER_TEMP':str(parent)})
                self.assertEqual(snapshot(parent),before)
                if link is not None:self.assertTrue(destination.is_symlink());self.assertEqual(os.readlink(destination),link)


if __name__ == '__main__': unittest.main()
