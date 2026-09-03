#!/usr/bin/env python3
"""Negative controls for the TMVerifier freeze checker."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "pnp3/Complexity/TMVerifier"
CHECKER = ROOT / "scripts/check_tmverifier_freeze.py"
MANIFEST = ROOT / "spec/tmverifier_freeze.json"
TARGET = Path("pnp3/Complexity/TMVerifier/TuringToolkit/GateNBodyRound.lean")


def run(candidate: Path, expect_ok: bool, manifest: Path | None = None) -> None:
    command = [str(CHECKER), "--candidate-root", str(candidate)]
    if manifest is not None:
        command.extend(["--manifest", str(manifest)])
    result = subprocess.run(
        command,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if (result.returncode == 0) != expect_ok:
        raise AssertionError(
            f"checker return code {result.returncode}, expected_ok={expect_ok}\n{result.stdout}"
        )


def fixture(parent: Path) -> Path:
    root = parent / "candidate"
    shutil.copytree(SOURCE, root / SOURCE.relative_to(ROOT), symlinks=True)
    return root


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="tmverifier-freeze-") as tmp:
        parent = Path(tmp)
        baseline = fixture(parent / "baseline")
        run(baseline, True)

        generated_manifest = parent / "generated-manifest.json"
        generated = subprocess.run(
            [str(CHECKER), "--manifest", str(generated_manifest), "--write-manifest"],
            cwd=ROOT,
            check=False,
        )
        if generated.returncode != 0:
            raise AssertionError("manifest regeneration failed")
        if json.loads(generated_manifest.read_text()) != json.loads(MANIFEST.read_text()):
            raise AssertionError("regenerated manifest differs from the reviewed manifest")

        exact_manifest = parent / "exact-manifest.json"
        shutil.copy2(MANIFEST, exact_manifest)
        run(baseline, True, exact_manifest)

        tampered_commit = parent / "tampered-commit.json"
        data = json.loads(MANIFEST.read_text())
        data["frozen_commit"] = "0" * 40
        tampered_commit.write_text(json.dumps(data))
        run(baseline, False, tampered_commit)

        tampered_entry = parent / "tampered-entry.json"
        data = json.loads(MANIFEST.read_text())
        next(iter(data["files"].values()))["sha256"] = "0" * 64
        tampered_entry.write_text(json.dumps(data))
        run(baseline, False, tampered_entry)

        modified = fixture(parent / "modified")
        with (modified / TARGET).open("ab") as handle:
            handle.write(b"\n-- negative control\n")
        run(modified, False)

        added = fixture(parent / "added")
        (added / SOURCE.relative_to(ROOT) / "Unexpected.lean").write_text("def x := 0\n")
        run(added, False)

        removed = fixture(parent / "removed")
        (removed / TARGET).unlink()
        run(removed, False)

        linked = fixture(parent / "linked")
        victim = linked / TARGET
        payload = linked / "same-content.lean"
        payload.write_bytes(victim.read_bytes())
        victim.unlink()
        os.symlink(payload, victim)
        run(linked, False)

        executable = fixture(parent / "executable")
        mode_target = executable / TARGET
        mode_target.chmod(mode_target.stat().st_mode | 0o111)
        run(executable, False)

    print("[tmverifier-freeze-test] OK: manifest trust + 5 filesystem controls")


if __name__ == "__main__":
    main()
