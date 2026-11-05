"""Vertical completion DATA; no workflow, installer, Git or compiler execution."""
import importlib.util
import json
import os
from pathlib import Path
import re
import unittest

A = Path(__file__).resolve().parents[1]
P = A / ("ci" if (A / "ci").is_dir() else "proposal")
WORKFLOW = P / "conditional-separation-native-v2.yml"


def evidence_symlink_capability(path, target):
    import errno
    try:
        path.symlink_to(target)
    except OSError as error:
        permitted = {errno.EPERM, errno.EACCES, errno.ENOSYS, errno.ENOTSUP,
                     getattr(errno, "EOPNOTSUPP", errno.ENOTSUP)}
        if error.errno not in permitted and getattr(error, "winerror", None) not in {50, 1314}:
            raise
        return {"available": False, "errno": error.errno, "winerror": getattr(error, "winerror", None)}
    return {"available": True, "errno": None, "winerror": None}


class WorkflowCompletion(unittest.TestCase):
    def test_unprivileged_PR_and_manual_events(self):
        text = WORKFLOW.read_text()
        self.assertIn("  pull_request:", text)
        self.assertIn("  workflow_dispatch:", text)
        self.assertNotIn("\n  push:", text)
        self.assertIn("conditional_separation/**", text)
        self.assertIn(".github/workflows/conditional-separation-native.yml", text)
        self.assertNotIn("pull_request_target:", text)
        self.assertIn("contents: read", text)
        self.assertNotIn("uses: actions/checkout@", text)
        self.assertNotIn("secrets.", text)

    def test_exact_PR_head_not_synthetic_merge(self):
        text = WORKFLOW.read_text()
        self.assertIn("CI_EXPECTED_HEAD: ${{ github.event.pull_request.head.sha || github.sha }}", text)
        self.assertIn("row = event['pull_request']['head']", text)
        self.assertIn("repo.get('private') is not False", text)
        self.assertIn("CI_EXPECTED_HEAD:", text)
        self.assertIn("github.event.pull_request.head.sha || github.sha", text)

    def test_two_native_rows_parallel_two(self):
        text = WORKFLOW.read_text()
        self.assertEqual(re.findall(r"- runner: ([\w.-]+)", text), ["ubuntu-24.04", "macos-15"])
        self.assertIn("max-parallel: 2", text)
        self.assertNotIn("windows-", text)
        self.assertNotIn("-large\n", text)

    def test_always_owned_upload_and_retention(self):
        text = WORKFLOW.read_text()
        self.assertIn("actions/upload-artifact@cf430e030ddbb5b0abf93d22962f4752f3646cd9", text)
        self.assertGreaterEqual(text.count("if: ${{ always() }}"), 2)
        self.assertIn("path: ${{ runner.temp }}/conditional-separation-evidence-v2", text)
        self.assertIn("retention-days: 7", text)
        self.assertIn("if-no-files-found: error", text)
        self.assertIn("include-hidden-files: false", text)
        self.assertIn("github.run_attempt", text)
        self.assertNotIn("path: ${{ runner.temp }}\n", text)


    def test_installed_root_workflow_matches_package(self):
        root = A.parent / '.github/workflows/conditional-separation-native.yml'
        if not root.exists() and not root.is_symlink():
            self.skipTest('standalone package: monorepo root workflow absent')
        self.assertEqual(root.read_bytes(), WORKFLOW.read_bytes(),
                         'installed root workflow differs from packaged workflow')


class EvidenceCompletion(unittest.TestCase):
    def setUp(self):
        path = P / "ci_evidence_data_v2.py"
        if not path.exists():
            self.fail("prospective evidence/head DATA implementation is absent")
        spec = importlib.util.spec_from_file_location("ci_evidence_data_v2", path)
        self.m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.m)
        self.root = Path(os.environ["CI_DATA_ROOT"]) / self.id().split(".")[-1]
        self.root.mkdir()
        self.work = self.root / "work"
        self.package = self.root / "package"
        self.work.mkdir()
        self.package.mkdir()
        (self.package / "PACKAGE_FILES.json").write_text('{"schema":"DATA","files":[]}')
        self.identity = {"event": "DATA", "tested_head": "a" * 40}

    def test_PR_identity_and_wrong_merge_rejection(self):
        event = {"pull_request": {"head": {"sha": "a" * 40}}}
        result = self.m.resolve_head("pull_request", event, "b" * 40, "a" * 40, "refs/pull/1/merge")
        self.assertEqual(result["tested_head"], "a" * 40)
        self.assertEqual(result["event_sha"], "b" * 40)
        with self.assertRaises(ValueError):
            self.m.resolve_head("pull_request", event, "b" * 40, "b" * 40, "refs/pull/1/merge")

    def test_nonmain_push_dispatch_and_invalid_events(self):
        for event in ("push", "workflow_dispatch"):
            self.assertEqual(self.m.resolve_head(event, {}, "a" * 40, "a" * 40, "refs/heads/feature/test")["tested_head"], "a" * 40)
            for ref in ("refs/heads/main", "refs/heads/master", "refs/tags/v1"):
                with self.assertRaises(ValueError):
                    self.m.resolve_head(event, {}, "a" * 40, "a" * 40, ref)
        with self.assertRaises(ValueError):
            self.m.resolve_head("pull_request_target", {}, "a" * 40, "a" * 40, "refs/heads/main")
        with self.assertRaises(ValueError):
            self.m.resolve_head("pull_request", {}, "a" * 40, "a" * 40, "refs/pull/1/merge")

    def write(self, relative, text):
        path = self.work / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_owned_selection_excludes_caches_and_credentials(self):
        self.write("project-source-build/stdout.txt", "INERT compiler DATA")
        self.write("project-source-build/launch.json", '{"argv":["DATA"]}')
        for path in ("elan/token", ".git/config", "cache/config.json", "environment.json", "toolchains/lean.exe"):
            self.write(path, "MUST NOT UPLOAD")
        out = self.root / "evidence"
        result = self.m.stage_evidence(self.work, self.package, out, self.identity)
        names = [row["path"] for row in result["files"]]
        self.assertIn("commands/project-source-build/stdout.txt", names)
        self.assertFalse(any("elan" in n or "environment" in n or ".git" in n or "cache/" in n for n in names))
        self.assertNotIn("MUST NOT UPLOAD", "".join(p.read_text() for p in out.rglob("*") if p.is_file()))

    def test_missing_terminal_remains_UNKNOWN(self):
        self.write("project-source-build/launch.json", '{"argv":["DATA"]}')
        result = self.m.stage_evidence(self.work, self.package, self.root / "evidence", self.identity)
        self.assertEqual(result["command_states"]["project-source-build"], "STARTED_NO_TERMINAL_UNKNOWN")
        self.assertFalse((self.root / "evidence/commands/project-source-build/terminal.json").exists())
        self.assertTrue(all(v == "UNKNOWN_NO_COMPLETE_MARKER" for v in result["phase_states"].values()))

    def test_symlink_is_not_followed(self):
        path = self.work / "project-source-build/stdout.txt"
        path.parent.mkdir()
        target = self.root / "outside-DATA"
        target.write_text("NOT TO COPY")
        capability = evidence_symlink_capability(path, target)
        (self.root / "symlink-capability.json").write_text(json.dumps(capability))
        if not capability["available"]:
            self.skipTest("recognized native symlink capability denial: " + str(capability))
        result = self.m.stage_evidence(self.work, self.package, self.root / "evidence", self.identity)
        self.assertFalse(result["export_complete"])
        self.assertFalse((self.root / "evidence/commands/project-source-build/stdout.txt").exists())

    def test_mocked_production_symlink_refusal_always(self):
        from unittest.mock import patch
        path = self.write("project-source-build/stdout.txt", "MUST NOT COPY")
        original = Path.is_symlink
        with patch.object(Path, "is_symlink", new=lambda p: p == path or original(p)):
            result = self.m.stage_evidence(self.work, self.package, self.root / "evidence", self.identity)
        self.assertFalse(result["export_complete"])
        self.assertFalse(result["native_validation_pass"])
        self.assertFalse((self.root / "evidence/commands/project-source-build/stdout.txt").exists())

    def test_forced_recognized_symlink_capability_denial(self):
        import errno
        from unittest.mock import patch
        path = self.root / "not-created"
        with patch.object(Path, "symlink_to", side_effect=PermissionError(errno.EPERM, "forced DATA denial")):
            capability = evidence_symlink_capability(path, self.root)
        self.assertFalse(capability["available"])
        self.assertEqual(capability["errno"], errno.EPERM)
        self.assertFalse(path.exists())

    def test_unexpected_symlink_EIO_propagates(self):
        import errno
        from unittest.mock import patch
        with patch.object(Path, "symlink_to", side_effect=OSError(errno.EIO, "forced DATA I/O failure")):
            with self.assertRaises(OSError):
                evidence_symlink_capability(self.root / "not-created", self.root)

    def test_size_budget_records_incomplete_export(self):
        self.write("project-source-build/stdout.txt", "x" * 2000)
        result = self.m.stage_evidence(self.work, self.package, self.root / "evidence", self.identity,
                                       max_file_bytes=1024, max_total_bytes=4096)
        self.assertFalse(result["export_complete"])
        self.assertTrue(result["omissions"])

    def test_invalid_budget_types_rejected(self):
        for index, value in enumerate((True, 0, -1, 1.5, "100")):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    self.m.stage_evidence(self.work, self.package, self.root / ("invalid-" + str(index)),
                                          self.identity, max_files=value)

    def test_omission_sample_is_bounded(self):
        self.m.MAX_OMISSIONS = 2
        for name in ("stdout.txt", "stderr.txt", "launch.json", "terminal.json"):
            self.write("project-source-build/" + name, "x" * 200)
        result = self.m.stage_evidence(self.work, self.package, self.root / "evidence", self.identity,
                                       max_file_bytes=100)
        self.assertFalse(result["export_complete"])
        self.assertLessEqual(len(result["omissions"]), 2)
        self.assertGreater(result["omission_count"], 2)
        self.assertTrue(result["omission_sample_truncated"])

    def test_compiler_identity_metadata_not_binary_objects(self):
        prefix = "native-rejection-attempt/.lake/conditional-check/runs/DATA/"
        self.write(prefix + "own-0.source.lean.txt", "-- inert source DATA")
        self.write(prefix + "own-0.setup.json", '{"importArts":{}}')
        self.write(prefix + "own-0.parts.json", '[{"path":"Attempt.olean","sha256":"DATA"}]')
        self.write(prefix + "Attempt.olean", "NOT AN OBJECT")
        self.write("native-rejection-attempt/.lake/packages/private-key.json", "NOT TO UPLOAD")
        result = self.m.stage_evidence(self.work, self.package, self.root / "evidence", self.identity)
        names = [row["path"] for row in result["files"]]
        self.assertTrue(any(n.endswith("own-0.setup.json") for n in names))
        self.assertTrue(any(n.endswith("own-0.parts.json") for n in names))
        self.assertTrue(any(n.endswith("own-0.source.lean.txt") for n in names))
        self.assertFalse(any(n.endswith(".olean") or "private-key" in n for n in names))
    def test_oversized_stdout_lossless_default_limits(self):
        import hashlib
        payload = b'x' * (8 * 1024**2) + b'y'
        source = self.write('project-source-build/stdout.txt', '')
        source.write_bytes(payload)
        self.write('project-source-build/terminal.json', '{"fixture":"DATA only"}')
        out = self.root / 'evidence'
        result = self.m.stage_evidence(self.work, self.package, out, self.identity)
        self.assertTrue(result['export_complete'], result['omissions'])
        records = result['fragmented_text']
        self.assertEqual(len(records), 1)
        record = records[0]
        self.assertEqual(record['path'], 'commands/project-source-build/stdout.txt')
        self.assertEqual(record['bytes'], len(payload))
        self.assertEqual(record['sha256'], hashlib.sha256(payload).hexdigest())
        self.assertEqual(record['parts'], [record['path'] + '.parts/' + f'{i:08d}.txt' for i in range(2)])
        pieces = [(out / name).read_bytes() for name in record['parts']]
        for piece in pieces:
            self.assertLessEqual(len(piece), 8 * 1024**2)
            piece.decode('utf-8')
        self.assertEqual(b''.join(pieces), payload)
        self.assertEqual(result['payload_bytes'], sum(row['bytes'] for row in result['files']))
        physical = result['physical_export']
        self.assertEqual(physical['files'], len(result['files']) + 1)
        self.assertEqual(physical['manifest_bytes'], (out / 'EVIDENCE_MANIFEST.json').stat().st_size)
        self.assertEqual(physical['total_bytes'], result['payload_bytes'] + physical['manifest_bytes'])
        self.assertFalse(result['native_validation_pass'])
    def test_same_size_source_change_rejected_before_fragment_writes(self):
        from unittest.mock import patch
        source = self.write('project-source-build/stdout.txt', 'a' * 200)
        self.write('project-source-build/terminal.json', '{"fixture":"DATA"}')
        original_read = Path.read_bytes
        def changed(path):
            data = original_read(path)
            if path == source:
                path.write_bytes(b'b' * len(data))
            return data
        out = self.root / 'evidence'
        with patch.object(Path, 'read_bytes', new=changed):
            with self.assertRaisesRegex(ValueError, 'evidence changed while read'):
                self.m.stage_evidence(self.work, self.package, out, self.identity, max_file_bytes=64)
        self.assertFalse((out / 'commands/project-source-build/stdout.txt.parts').exists())
    def test_payload_caps_cannot_be_raised(self):
        for i, limits in enumerate(({'max_file_bytes': 8*1024**2+1},
                                    {'max_total_bytes': 64*1024**2+1},
                                    {'max_files': 4097})):
            with self.subTest(limits=limits), self.assertRaises(ValueError):
                self.m.stage_evidence(self.work, self.package, self.root / ('raised-' + str(i)), self.identity, **limits)
    def test_multibyte_fragment_roundtrip_and_small_file_compatibility(self):
        import hashlib
        payload = b'a' * 63 + '😀αβ'.encode('utf-8') * 30
        source = self.write('project-source-build/stdout.txt', '')
        self.write('project-source-build/terminal.json', '{"fixture":"DATA"}')
        source.write_bytes(payload)
        for limit in (64, 65, 66, 67):
            out = self.root / ('evidence-' + str(limit))
            result = self.m.stage_evidence(self.work, self.package, out, self.identity, max_file_bytes=limit)
            self.assertTrue(result['export_complete'])
            actual = self.m.reconstruct_text_export(out, result, 'commands/project-source-build/stdout.txt')
            self.assertEqual(actual, payload)
            record = result['fragmented_text'][0]
            self.assertEqual(record['sha256'], hashlib.sha256(payload).hexdigest())
            for name in record['parts']:
                (out / name).read_bytes().decode('utf-8')
            self.assertEqual(result['payload_bytes'], sum(r['bytes'] for r in result['files']))
        source.write_bytes(b'small\r\nLF\n')
        out = self.root / 'small'
        result = self.m.stage_evidence(self.work, self.package, out, self.identity)
        self.assertTrue(result['export_complete'])
        self.assertNotIn('fragmented_text', result)
        self.assertEqual((out / 'commands/project-source-build/stdout.txt').read_bytes(), source.read_bytes())
        self.assertEqual(self.m.reconstruct_text_export(out, result, 'commands/project-source-build/stdout.txt'), source.read_bytes())

    def test_fragment_integrity_mutations_are_rejected(self):
        import copy
        payload = ('😀αβ' * 40).encode('utf-8')
        source = self.write('project-source-build/stdout.txt', '')
        source.write_bytes(payload)
        self.write('project-source-build/terminal.json', '{"fixture":"DATA"}')
        out = self.root / 'evidence'
        result = self.m.stage_evidence(self.work, self.package, out, self.identity, max_file_bytes=64)
        original = 'commands/project-source-build/stdout.txt'
        self.assertEqual(self.m.reconstruct_text_export(out, result, original), payload)
        def rejected(label, change):
            value = copy.deepcopy(result)
            change(value)
            (self.root / (label + '.mutation.json')).write_text(json.dumps(value))
            with self.subTest(mutation=label), self.assertRaises((ValueError, UnicodeError)):
                self.m.reconstruct_text_export(out, value, original)
        rejected('order', lambda m: m['fragmented_text'][0]['parts'].reverse())
        rejected('original_hash', lambda m: m['fragmented_text'][0].update(sha256='0' * 64))
        rejected('original_size', lambda m: m['fragmented_text'][0].update(bytes=len(payload) + 1))
        rejected('duplicate_record', lambda m: m['fragmented_text'].append(copy.deepcopy(m['fragmented_text'][0])))
        rejected('duplicate_pin', lambda m: m['files'].append(copy.deepcopy(m['files'][0])))
        rejected('missing_pin', lambda m: m['files'].pop(0))
        rejected('part_hash', lambda m: m['files'][0].update(sha256='0' * 64))
        rejected('part_size', lambda m: m['files'][0].update(bytes=m['files'][0]['bytes'] + 1))
        rejected('bool_size', lambda m: m['files'][0].update(bytes=True))
        rejected('extra_reference', lambda m: m['fragmented_text'][0]['parts'].append('commands/project-source-build/stdout.txt.parts/99999999.txt'))
        rejected('missing_record', lambda m: m.pop('fragmented_text'))
        rejected('payload_total', lambda m: m.update(payload_bytes=m['payload_bytes'] + 1))
        rejected('path_escape', lambda m: m['files'][0].update(path='../outside'))
        rejected('physical_count', lambda m: m['physical_export'].update(files=999))
        rejected('descriptor_size', lambda m: m['physical_export'].update(manifest_bytes=999))
        rejected('physical_total', lambda m: m['physical_export'].update(total_bytes=999))
    def test_fragment_missing_extra_and_aliased_files_rejected(self):
        import shutil
        from unittest.mock import patch
        source = self.write('project-source-build/stdout.txt', 'x' * 200)
        self.write('project-source-build/terminal.json', '{"fixture":"DATA"}')
        out = self.root / 'evidence'
        result = self.m.stage_evidence(self.work, self.package, out, self.identity, max_file_bytes=64)
        name = result['fragmented_text'][0]['path']
        first = result['fragmented_text'][0]['parts'][0]
        missing = self.root / 'missing'
        shutil.copytree(out, missing, ignore=lambda parent, names: [Path(first).name] if Path(parent) == (out / first).parent else [])
        with self.assertRaises(ValueError):
            self.m.reconstruct_text_export(missing, result, name)
        extra = self.root / 'extra'
        shutil.copytree(out, extra)
        (extra / 'unlisted.txt').write_text('unlisted DATA')
        with self.assertRaises(ValueError):
            self.m.reconstruct_text_export(extra, result, name)
        original = Path.is_symlink
        target = out / first
        with patch.object(Path, 'is_symlink', new=lambda p: p == target or original(p)):
            with self.assertRaises(ValueError):
                self.m.reconstruct_text_export(out, result, name)

    def test_total_count_and_codepoint_budgets_are_atomic(self):
        source = self.write('project-source-build/stdout.txt', 'x' * 200)
        self.write('project-source-build/terminal.json', '{"fixture":"DATA"}')
        for label, limits in [('total', {'max_file_bytes':64, 'max_total_bytes':100}),
                              ('count', {'max_file_bytes':64, 'max_files':2})]:
            out = self.root / label
            result = self.m.stage_evidence(self.work, self.package, out, self.identity, **limits)
            self.assertFalse(result['export_complete'])
            self.assertFalse((out / 'commands/project-source-build/stdout.txt.parts').exists())
            self.assertNotIn('fragmented_text', result)
            self.assertLessEqual(result['payload_bytes'], result['limits']['payload_bytes'])
            self.assertLessEqual(len(result['files']), result['limits']['files'])
        with self.assertRaises(ValueError):
            self.m._utf8_chunks('😀'.encode('utf-8'), 3, 10)

    def test_fragmented_missing_terminal_is_still_UNKNOWN(self):
        self.write('project-source-build/stdout.txt', 'x' * 200)
        out = self.root / 'evidence'
        result = self.m.stage_evidence(self.work, self.package, out, self.identity, max_file_bytes=64)
        self.assertFalse(result['export_complete'])
        self.assertEqual(result['command_states']['project-source-build'], 'STARTED_NO_TERMINAL_UNKNOWN')
        self.assertFalse((out / 'commands/project-source-build/terminal.json').exists())
        self.assertEqual(self.m.reconstruct_text_export(out, result, 'commands/project-source-build/stdout.txt'), b'x' * 200)

    def test_invalid_UTF8_nonregular_and_hardlinked_source_rejected(self):
        import errno
        source = self.write('project-source-build/stdout.txt', '')
        source.write_bytes(b'x' * 200 + b'\xff')
        self.write('project-source-build/terminal.json', '{"fixture":"DATA"}')
        out = self.root / 'invalid'
        result = self.m.stage_evidence(self.work, self.package, out, self.identity, max_file_bytes=64)
        self.assertFalse(result['export_complete'])
        self.assertTrue(any(r['reason'] == 'not UTF8 text evidence' for r in result['omissions']))
        source.write_bytes(b'x' * 200)
        alias = self.root / 'hardlink'
        try:
            os.link(source, alias)
        except OSError as error:
            if error.errno not in {errno.EPERM, errno.EACCES, errno.ENOSYS, errno.ENOTSUP, getattr(errno, 'EOPNOTSUPP', errno.ENOTSUP)}:
                raise
            (self.root / 'hardlink-capability.json').write_text(json.dumps({'available':False, 'errno':error.errno}))
        else:
            result = self.m.stage_evidence(self.work, self.package, self.root / 'linked', self.identity, max_file_bytes=64)
            self.assertFalse(result['export_complete'])
            self.assertTrue(any('hardlink' in r['reason'] for r in result['omissions']))
        directory = self.work / 'lean-version/stdout.txt'
        directory.mkdir(parents=True)
        result = self.m.stage_evidence(self.work, self.package, self.root / 'nonregular', self.identity, max_file_bytes=64)
        self.assertFalse(result['export_complete'])
        self.assertTrue(any(r['path'] == 'commands/lean-version/stdout.txt' and 'nonregular' in r['reason'] for r in result['omissions']))
    def test_outer_descriptor_counts_against_hard_export_budgets(self):
        for label, value in (
            ('count', {'files':[{}] * 4096, 'payload_bytes':0}),
            ('total', {'files':[], 'payload_bytes':64*1024**2}),
            ('descriptor', {'files':[], 'payload_bytes':0, 'identity':'x' * (8*1024**2+1)}),
        ):
            with self.subTest(case=label), self.assertRaises(ValueError):
                self.m._evidence_descriptor(value)
