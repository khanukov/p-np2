#!/usr/bin/env python3
"""Verify the content-addressed freeze of pnp3/Complexity/TMVerifier."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TREE = ROOT / "pnp3/Complexity/TMVerifier"
MANIFEST = ROOT / "spec/tmverifier_freeze.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected: dict[str, str] = data["files"]
    actual_paths = {
        path.relative_to(ROOT).as_posix()
        for path in TREE.rglob("*")
        if path.is_file()
    }
    expected_paths = set(expected)

    added = sorted(actual_paths - expected_paths)
    removed = sorted(expected_paths - actual_paths)
    changed = sorted(
        rel for rel in actual_paths & expected_paths if digest(ROOT / rel) != expected[rel]
    )

    if added or removed or changed:
        print("TMVerifier freeze violation.", file=sys.stderr)
        if added:
            print("  Added:", *added, sep="\n    ", file=sys.stderr)
        if removed:
            print("  Removed:", *removed, sep="\n    ", file=sys.stderr)
        if changed:
            print("  Changed:", *changed, sep="\n    ", file=sys.stderr)
        print(
            "The tree is frozen at 42c598815c8e7d27a53f26102705f84455c6979d. "
            "Use a separately reviewed unfreeze/migration PR to alter it.",
            file=sys.stderr,
        )
        return 1

    print(
        f"[tmverifier-freeze] OK: {len(expected)} files match "
        f"{data['frozen_commit'][:12]}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
