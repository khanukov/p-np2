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


class WorkflowCompletion(unittest.TestCase):
    def test_unprivileged_feature_and_PR_events(self):
        text = WORKFLOW.read_text()
        self.assertIn("  pull_request:", text)
        self.assertIn("  push:", text)
        self.assertIn("branches-ignore: [main, master]", text)
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

    def test_three_native_rows_parallel_three(self):
        text = WORKFLOW.read_text()
        self.assertEqual(re.findall(r"- runner: ([\w.-]+)", text), ["ubuntu-24.04", "macos-15", "windows-2022"])
        self.assertIn("max-parallel: 3", text)
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
        try:
            path.symlink_to(target)
        except OSError:
            self.skipTest("native symlink permission unavailable; no privilege change")
        result = self.m.stage_evidence(self.work, self.package, self.root / "evidence", self.identity)
        self.assertFalse(result["export_complete"])
        self.assertFalse((self.root / "evidence/commands/project-source-build/stdout.txt").exists())

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
