"""Finite copy-fidelity DATA; only workbench acquisition is stubbed, not copying.

Run with a private TMPDIR: python3 -B -m unittest -v test_prepare
These tests neither compile Lean nor assert a proof/checker result.
"""
import sys
sys.dont_write_bytecode = True
from contextlib import redirect_stdout
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("lengthwise_prepare_under_test", SOURCE / "prepare.py")
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)
COPYTREE = shutil.copytree


class PrepareCopyFidelityTests(unittest.TestCase):
    def setUp(self):
        # Preserve fault fixtures for inspection; caller chooses private TMPDIR.
        self.root = Path(tempfile.mkdtemp(prefix="lengthwise-copy-DATA-"))
        self.output = self.root / "attempt"
        self.core = self.root / "FAKE-UNEXECUTED-CORE"
        self.acquisitions = []

    def acquire(self, argv, *, check):
        self.assertTrue(check)
        self.assertEqual(argv, [sys.executable, "-B", str(self.core / "tools/workbench.py"),
                                "new", str(self.output), "--core", str(self.core)])
        self.acquisitions.append(argv)
        self.output.mkdir()
        (self.output / "Attempt.lean").write_text("-- FAKE acquisition template, overwritten by real copy\n")
        (self.output / "lakefile.lean").write_text("-- FAKE DATA, never compiled\n")

    def invoke(self, effect=None):
        def copytree(source, destination, *args, **kwargs):
            result = COPYTREE(source, destination, *args, **kwargs)
            if effect:
                effect(Path(destination))
            return result
        with patch.object(sys, "argv", ["prepare.py", "--core", str(self.core),
                                         "--output", str(self.output)]), \
             patch.object(prepare.subprocess, "run", self.acquire), \
             patch.object(prepare.shutil, "copytree", copytree), redirect_stdout(io.StringIO()):
            prepare.main()

    def reject(self, effect):
        with self.assertRaises(ValueError):
            self.invoke(effect)
        self.assertFalse((self.output / "RESEARCH_SOURCE_MANIFEST.json").exists())
        self.assertEqual(len(self.acquisitions), 1)

    def test_normal_copy_matches_independent_source_bytes(self):
        expected = []
        for p in sorted([SOURCE / "Attempt.lean", *(SOURCE / "Attempt").rglob("*.lean")]):
            b = p.read_bytes()
            expected.append({"path": p.relative_to(SOURCE).as_posix(), "bytes": len(b),
                             "sha256": hashlib.sha256(b).hexdigest()})
        self.invoke()
        manifest = json.loads((self.output / "RESEARCH_SOURCE_MANIFEST.json").read_bytes())
        self.assertEqual(manifest["status"], "PARTIAL_INTERFACE_NOT_PROOF_OF_R")
        self.assertEqual(manifest["files"], expected)
        for row in expected:
            self.assertEqual((self.output / row["path"]).read_bytes(),
                             (SOURCE / row["path"]).read_bytes())

    def test_corrupt_copy_rejected_without_success_manifest(self):
        def corrupt(destination):
            p = destination.parent / "Attempt.lean"
            p.write_bytes(p.read_bytes() + b"-- DATA copy corruption\n")
        self.reject(corrupt)

    def test_missing_copy_rejected_without_success_manifest(self):
        self.reject(lambda d: (d / "Lengthwise.lean").unlink())

    def test_extra_lean_copy_rejected_without_success_manifest(self):
        self.reject(lambda d: (d / "Unrequested.lean").write_text("-- DATA extra\n"))

    def test_extra_nonlean_copy_rejected_without_success_manifest(self):
        self.reject(lambda d: (d / "Unrequested.txt").write_text("FAKE DATA extra\n"))

    def test_existing_directory_not_overwritten(self):
        self.output.mkdir()
        sentinel = self.output / "sentinel.txt"
        sentinel.write_text("PRESERVE DATA\n")
        with self.assertRaises(SystemExit) as caught:
            self.invoke()
        self.assertEqual(caught.exception.code, 2)
        self.assertEqual(sentinel.read_text(), "PRESERVE DATA\n")
        self.assertEqual(self.acquisitions, [])

    def test_existing_symlink_not_followed(self):
        target = self.root / "sentinel-directory"
        target.mkdir()
        self.output.symlink_to(target, target_is_directory=True)
        with self.assertRaises(SystemExit) as caught:
            self.invoke()
        self.assertEqual(caught.exception.code, 2)
        self.assertTrue(self.output.is_symlink())
        self.assertEqual(list(target.iterdir()), [])
        self.assertEqual(self.acquisitions, [])


if __name__ == "__main__":
    unittest.main()
