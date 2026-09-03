#!/usr/bin/env python3
"""Negative controls for the TMVerifier freeze checker."""

from __future__ import annotations

import os
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "pnp3/Complexity/TMVerifier"
CHECKER = ROOT / "scripts/check_tmverifier_freeze.py"
MANIFEST = ROOT / "spec/tmverifier_freeze.json"
LAKEFILE = ROOT / "lakefile.lean"
TARGET = Path("pnp3/Complexity/TMVerifier/TuringToolkit/GateNBodyRound.lean")


def run(candidate: Path, expect_ok: bool, manifest: Path | None = None,
        lakefile: Path | None = None) -> None:
    command = [str(CHECKER), "--candidate-root", str(candidate)]
    if manifest is not None:
        command.extend(["--manifest", str(manifest)])
    if lakefile is not None:
        command.extend(["--lakefile", str(lakefile)])
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
    shutil.copytree(SOURCE, root / "pnp3/Complexity/TMVerifier", symlinks=True)
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

        exact_lakefile = parent / "lakefile.lean"
        shutil.copy2(LAKEFILE, exact_lakefile)
        run(baseline, True, lakefile=exact_lakefile)

        missing_module = parent / "missing-module.lean"
        lake = LAKEFILE.read_text()
        lake = lake.replace(
            "    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBodyRound,\n",
            "",
            1,
        )
        missing_module.write_text(lake)
        run(baseline, False, lakefile=missing_module)

        commented_module = parent / "commented-module.lean"
        lake = LAKEFILE.read_text().replace(
            "    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBodyRound,\n",
            "    -- Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBodyRound,\n",
            1,
        )
        commented_module.write_text(lake)
        run(baseline, False, lakefile=commented_module)

        blocked_module = parent / "blocked-module.lean"
        lake = LAKEFILE.read_text().replace(
            "    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBodyRound,\n",
            "    /- Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBodyRound, -/\n",
            1,
        )
        blocked_module.write_text(lake)
        run(baseline, False, lakefile=blocked_module)

        decoy_module = parent / "decoy-module.lean"
        active = "    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBodyRound,\n"
        lake = LAKEFILE.read_text().replace(active, "", 1)
        lake += "\ndef decoyGlobs := #[\n" + active + "]\n"
        decoy_module.write_text(lake)
        run(baseline, False, lakefile=decoy_module)

        raw_decoy = parent / "raw-decoy.lean"
        lake = LAKEFILE.read_text().replace(active, "", 1)
        lake += '\ndef decoy := r#"' + active + '"#\n'
        raw_decoy.write_text(lake)
        run(baseline, False, lakefile=raw_decoy)

        nested_decoy = parent / "nested-decoy.lean"
        lake = LAKEFILE.read_text().replace(active, "", 1)
        nested = "    by\n      let decoy := #[\n" + active + "      ]\n"
        lake = lake.replace(
            "  ]\n\nlean_lib Pnp4 where",
            nested + "  ]\n\nlean_lib Pnp4 where",
            1,
        )
        nested_decoy.write_text(lake)
        run(baseline, False, lakefile=nested_decoy)

        nested_field = parent / "nested-field.lean"
        lake = LAKEFILE.read_text().replace(
            "  globs := #[\n", "  other := {\n    globs := #[\n", 1
        )
        lake = lake.replace(
            "  ]\n\nlean_lib Pnp4 where",
            "    ]\n  }\n\nlean_lib Pnp4 where",
            1,
        )
        nested_field.write_text(lake)
        run(baseline, False, lakefile=nested_field)

        tampered_manifest = parent / "tampered-manifest.json"
        data = json.loads(MANIFEST.read_text())
        data["frozen_commit"] = "0" * 40
        tampered_manifest.write_text(json.dumps(data))
        run(baseline, False, tampered_manifest)

        tampered_entry = parent / "tampered-entry.json"
        data = json.loads(MANIFEST.read_text())
        first = next(iter(data["files"].values()))
        first["sha256"] = "0" * 64
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

    print("[tmverifier-freeze-test] OK: manifest/lake trust + 5 filesystem controls")


if __name__ == "__main__":
    main()
