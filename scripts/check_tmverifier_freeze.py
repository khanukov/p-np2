#!/usr/bin/env python3
"""Verify the content-addressed freeze of pnp3/Complexity/TMVerifier."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TREE = "pnp3/Complexity/TMVerifier"
FROZEN_COMMIT = "42c598815c8e7d27a53f26102705f84455c6979d"
SCHEMA_VERSION = 2
MANIFEST = ROOT / "spec/tmverifier_freeze.json"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate manifest key: {key!r}")
        result[key] = value
    return result


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def frozen_git_entries() -> dict[str, dict[str, str]]:
    records = git("ls-tree", "-rz", FROZEN_COMMIT, "--", TREE).split(b"\0")
    result: dict[str, dict[str, str]] = {}
    for record in records:
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, object_type, oid = metadata.decode("ascii").split()
        rel = os.fsdecode(raw_path)
        payload = git("cat-file", object_type, oid)
        result[rel] = {
            "mode": mode,
            "type": object_type,
            "git_oid": oid,
            "sha256": sha256(payload),
        }
    return result


def manifest_data() -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "frozen_commit": FROZEN_COMMIT,
        "tree": TREE,
        "files": dict(sorted(frozen_git_entries().items())),
    }


def load_manifest(path: Path) -> dict[str, dict[str, str]]:
    data: dict[str, Any] = json.loads(
        path.read_text(encoding="utf-8"), object_pairs_hook=unique_object
    )
    required = {
        "schema_version": SCHEMA_VERSION,
        "frozen_commit": FROZEN_COMMIT,
        "tree": TREE,
    }
    for key, value in required.items():
        if data.get(key) != value:
            raise ValueError(f"manifest {key!r} must equal {value!r}")
    files = data.get("files")
    if not isinstance(files, dict):
        raise ValueError("manifest 'files' must be an object")
    if files != frozen_git_entries():
        raise ValueError("manifest entries do not match Git objects at the frozen commit")
    return files


def working_entries(candidate_root: Path) -> dict[str, dict[str, str]]:
    tree = candidate_root / TREE
    if tree.is_symlink() or not tree.is_dir():
        raise ValueError(f"candidate tree must be a real directory: {tree}")
    result: dict[str, dict[str, str]] = {}
    for path in tree.rglob("*"):
        info = path.lstat()
        if stat.S_ISDIR(info.st_mode):
            continue
        rel = path.relative_to(candidate_root).as_posix()
        if stat.S_ISREG(info.st_mode):
            mode = "100755" if info.st_mode & 0o111 else "100644"
            result[rel] = {
                "mode": mode,
                "type": "blob",
                "sha256": sha256(path.read_bytes()),
            }
        elif stat.S_ISLNK(info.st_mode):
            result[rel] = {
                "mode": "120000",
                "type": "blob",
                "sha256": sha256(os.fsencode(os.readlink(path))),
            }
        else:
            result[rel] = {"mode": "special", "type": "special", "sha256": ""}
    return result


def missing_lake_modules(expected_paths: set[str], lakefile_path: Path) -> list[str]:
    lakefile = lakefile_path.read_text(encoding="utf-8")
    missing: list[str] = []
    for rel in sorted(expected_paths):
        if not rel.endswith(".lean") or not rel.startswith("pnp3/"):
            continue
        module = rel.removeprefix("pnp3/").removesuffix(".lean").replace("/", ".")
        if f"Glob.one `{module}," not in lakefile:
            missing.append(module)
    return missing


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate-root", type=Path, default=ROOT)
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    parser.add_argument("--lakefile", type=Path, default=ROOT / "lakefile.lean")
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    if args.write_manifest:
        args.manifest.write_text(
            json.dumps(manifest_data(), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(f"[tmverifier-freeze] wrote {args.manifest}")
        return 0
    try:
        expected = load_manifest(args.manifest.resolve())
        actual = working_entries(args.candidate_root.resolve())
        missing_modules = missing_lake_modules(set(expected), args.lakefile.resolve())
    except (OSError, ValueError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        print(f"TMVerifier freeze check failed: {exc}", file=sys.stderr)
        return 1

    expected_paths = set(expected)
    actual_paths = set(actual)
    added = sorted(actual_paths - expected_paths)
    removed = sorted(expected_paths - actual_paths)
    changed = sorted(
        rel
        for rel in expected_paths & actual_paths
        if any(actual[rel].get(key) != expected[rel].get(key) for key in ("mode", "type", "sha256"))
    )
    if added or removed or changed or missing_modules:
        print("TMVerifier freeze violation.", file=sys.stderr)
        for label, paths in (("Added", added), ("Removed", removed), ("Changed", changed)):
            if paths:
                print(f"  {label}:", *paths, sep="\n    ", file=sys.stderr)
        if missing_modules:
            print("  Missing lake modules:", *missing_modules, sep="\n    ", file=sys.stderr)
        print(
            f"The tree is frozen at {FROZEN_COMMIT}. Use a separately reviewed "
            "unfreeze/migration PR to alter it.",
            file=sys.stderr,
        )
        return 1

    print(f"[tmverifier-freeze] OK: {len(expected)} Git objects match {FROZEN_COMMIT[:12]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
