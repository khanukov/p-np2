"""Finite DATA: actual CLI validation and literal proposed shell; no native build/fetch."""
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
git() {
  printf 'git\t%s\t' "$PWD" >> "$COMMAND_LOG"
  printf '%s\t' "$@" >> "$COMMAND_LOG"; printf '\n' >> "$COMMAND_LOG"
  if [[ "$1" == init || ( "$1" == -C && "$3" == remote ) ]]; then
    command git "$@" # Real local init/remote-add only, confined to this DATA root.
  elif [[ "$1" == -C && ( "$3" == fetch || "$3" == checkout ) ]]; then
    return 0 # Inert argv observation; never execute fetch or checkout.
  else return 97; fi
}
lake() { printf 'lake\t%s\t%s\n' "$PWD" "$*" >> "$COMMAND_LOG"; }
python3() { printf 'python3\t%s\t%s\n' "$PWD" "$*" >> "$COMMAND_LOG"; }
'''


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
    if len(blocks) != 2: raise AssertionError('exact two proposed shell blocks')
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

    def source_destination(self, run_id):
        text = WORKFLOW.read_text()
        value = re.search(r'^      SOURCE_RUN: (.+)$',text,re.M).group(1)
        values = {'runner.temp':str(self.data), 'github.run_id':run_id,
                  'github.run_attempt':'1', 'github.job':'source'}
        for key, replacement in values.items(): value = value.replace('${{ '+key+' }}',replacement)
        self.assertNotIn('${{', value)
        destination = self.data/value
        self.assertEqual(destination.parent, self.data)
        return destination

    def fetch(self, destination):
        log = self.data/('fetch-'+str(self.sequence)+'.calls')
        result = self.child(['bash','--noprofile','--norc','-e','-o','pipefail','-c',SHELL_TRAPS+shell_blocks(WORKFLOW.read_text())[0]],
                            env=dict(RUNNER_TEMP=str(self.data), SOURCE_RUN=destination.name, COMMAND_LOG=str(log),
                                     GITHUB_SERVER_URL='https://example.invalid',
                                     GITHUB_REPOSITORY='FAKE/DATA', GITHUB_SHA='d'*40))
        return result, log

    def test_fresh_runs_preserve_reused_workspace_and_build_same_path(self):
        old = self.data/'checkout';old.mkdir();(old/'previous.DATA').write_text('PRESERVE FAKE DATA')
        for run_id in ['100','101']:
            destination = self.source_destination(run_id)
            result, log = self.fetch(destination)
            self.assertEqual(result.returncode, 0, result.stderr.decode())
            self.assertTrue((destination/'.git').is_dir())
            calls = [line.split('\t') for line in log.read_text().splitlines()]
            self.assertEqual([c[2:-1] for c in calls], [
                ['init',str(destination)],
                ['-C',str(destination),'remote','add','origin','https://example.invalid/FAKE/DATA.git'],
                ['-C',str(destination),'fetch','--depth=1','origin','d'*40],
                ['-C',str(destination),'checkout','--detach','FETCH_HEAD']])
            text = WORKFLOW.read_text()
            binding = 'SOURCE_DEST="${RUNNER_TEMP:?}/${SOURCE_RUN:?}"'
            self.assertTrue(all(block.count(binding)==1 for block in shell_blocks(text)))
            build = destination/'conditional_separation'
            build.mkdir() # Synthetic package directory; no fetched source/build exists.
            build_log = self.data/('build-'+run_id+'.calls')
            result = self.child(['bash','--noprofile','--norc','-e','-o','pipefail','-c',SHELL_TRAPS+shell_blocks(text)[1]],
                                cwd=self.data,env={'COMMAND_LOG':str(build_log),'RUNNER_TEMP':str(self.data),'SOURCE_RUN':destination.name})
            self.assertEqual(result.returncode,0)
            self.assertEqual(build_log.read_text().splitlines(),[
                'lake\t'+str(build)+'\tbuild',
                'python3\t'+str(build)+'\t-B ci/run_data_tests_v2.py'])
        self.assertEqual((old/'previous.DATA').read_text(),'PRESERVE FAKE DATA')
        self.assertFalse((old/'.git').exists())

    def test_git_environment_cannot_redirect_fixture_repository(self):
        outside = self.data/'outside-INERT-DATA';outside.mkdir()
        init = self.child(['git','init',str(outside)])
        self.assertEqual(init.returncode,0)
        (outside/'sentinel.DATA').write_text('PRESERVE OUTSIDE DATA')
        config = outside/'.git/config';original_config = config.read_bytes()
        before = snapshot(outside)
        destination = self.source_destination('500')
        ambient = dict(GIT_DIR=str(outside/'.git'), GIT_WORK_TREE=str(outside),
                       GIT_COMMON_DIR=str(outside/'.git'))
        with mock.patch.dict(os.environ,ambient):
            result,log = self.fetch(destination)
        after = snapshot(outside)
        (self.data/'outside-comparison.DATA.json').write_text(json.dumps(dict(
            scope='own inert repositories only',before=before,after=after,
            fetch_OS_exit=result.returncode),indent=2)+'\n')
        self.assertEqual(after,before)
        self.assertEqual(config.read_bytes(),original_config)
        self.assertEqual(result.returncode,0,result.stderr.decode())
        self.assertTrue((destination/'.git').is_dir())
        extra = dict(ambient,GIT_INDEX_FILE=str(outside/'index.DATA'),
                     GIT_OBJECT_DIRECTORY=str(outside/'.git/objects'),
                     GIT_ALTERNATE_OBJECT_DIRECTORIES=str(outside/'.git/objects'),
                     GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='core.bare',GIT_CONFIG_VALUE_0='true',
                     GIT_CONFIG_PARAMETERS="'core.bare=true'",GIT_CONFIG=str(config),
                     GIT_CONFIG_GLOBAL=str(config),GIT_CONFIG_SYSTEM=str(config),
                     GIT_NAMESPACE='FAKE',GIT_CEILING_DIRECTORIES=str(self.data),
                     GIT_EXEC_PATH=str(outside/'nonexistent-helpers'),
                     GIT_TEMPLATE_DIR=str(outside/'nonexistent-template'),
                     GIT_TRACE=str(outside/'trace.DATA'))
        identity = self.child(['git','-C',str(destination),'rev-parse','--absolute-git-dir'],env=extra)
        self.assertEqual(identity.returncode,0,identity.stderr.decode())
        self.assertEqual(identity.stdout.decode().strip(),str(destination/'.git'))
        self.assertEqual(snapshot(outside),before)
        self.assertFalse((outside/'trace.DATA').exists())

    def test_same_run_existing_destination_rejects_before_git(self):
        destination = self.source_destination('200')
        first,_ = self.fetch(destination);self.assertEqual(first.returncode,0)
        (destination/'sentinel.DATA').write_text('unchanged')
        before = snapshot(destination)
        second,log = self.fetch(destination)
        self.assertNotEqual(second.returncode,0)
        self.assertIn(b'fresh source destination already exists',second.stderr)
        self.assertFalse(log.exists())
        self.assertEqual(snapshot(destination),before)

    def test_existing_regular_file_destination_rejects(self):
        destination = self.source_destination('300');destination.write_text('PRESERVE')
        result,log = self.fetch(destination)
        self.assertNotEqual(result.returncode,0)
        self.assertEqual(destination.read_text(),'PRESERVE')
        self.assertFalse(log.exists())

    def test_existing_and_dangling_symlink_destinations_reject(self):
        for run_id,existing in [('400',True),('401',False)]:
            with self.subTest(existing_target=existing):
                destination = self.source_destination(run_id);target=self.data/('target-'+run_id)
                if existing: target.mkdir();(target/'sentinel.DATA').write_text('PRESERVE')
                try: destination.symlink_to(target,target_is_directory=True)
                except OSError as error:
                    if error.errno in {errno.EACCES,errno.EPERM,errno.ENOSYS,errno.ENOTSUP}:
                        self.skipTest('symlink capability unavailable: '+str(error))
                    raise
                before = snapshot(target) if existing else None
                result,log = self.fetch(destination)
                self.assertNotEqual(result.returncode,0)
                self.assertTrue(destination.is_symlink());self.assertFalse(log.exists())
                self.assertEqual(snapshot(target) if target.exists() else None,before)


if __name__ == '__main__': unittest.main()
