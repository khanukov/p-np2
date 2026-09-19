#!/usr/bin/env python3
"""Verify the content-addressed freeze of pnp3/Complexity/TMVerifier.

The frozen content is enumerated from ``FROZEN_TREE``, the Git tree object of
the frozen subtree.  Tree objects are content-addressed, so that enumeration
survives every history rewrite: a squash merge, a rebase, a branch force-push,
and a shallow or single-branch clone all still carry the tree object as long as
they carry the bytes.  ``FROZEN_TREE`` is therefore the authoritative source
this checker verifies against.

``FROZEN_COMMIT`` is retained as *reviewed provenance*: the commit at which the
frozen bytes were reviewed and re-pinned.  It is no longer the enumeration
source.  When the checkout still contains it, its subtree is cross-checked
against ``FROZEN_TREE``; when a rewritten or shallow history no longer contains
it, content verification proceeds unchanged.  Provenance that is present but
malformed or disagreeing fails closed — only genuine absence is skipped.

A tree pin does not prove commit ancestry.  Retaining the reviewed commit in
``main``'s history still requires the history-preserving merge rule recorded in
``pnp3/Docs/TMVERIFIER_FREEZE.md``; this checker only guarantees that the frozen
*content* stays verifiable regardless of how the history is reshaped.
"""

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
# Reviewed provenance only.  Content enumeration must not depend on it.
FROZEN_COMMIT = "249435bfa4cb540822e47844107781042f18537f"
# Authoritative immutable content source: the Git tree object for TREE.
FROZEN_TREE = "7ef6ac6e119f0f078f9c896f17415fa560a6edf3"
SCHEMA_VERSION = 3
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


def git_probe(*args: str) -> str | None:
    """Run a read-only Git query whose failure is a legitimate answer.

    Returns the stripped stdout, or None when Git exits nonzero.  Git's own
    stderr is discarded because "this object is not in this repository" is an
    expected outcome here, not a diagnostic worth printing.
    """
    try:
        output = subprocess.check_output(
            ["git", "-C", str(ROOT), *args], stderr=subprocess.DEVNULL
        )
    except subprocess.CalledProcessError:
        return None
    return output.decode("ascii").strip()


def verify_provenance() -> bool:
    """Cross-check the reviewed provenance commit when this history still has it.

    Returns True when FROZEN_COMMIT was available and recorded TREE as
    FROZEN_TREE, and False when the object is simply absent — the rewritten or
    shallow-clone case, in which content verification still proceeds from
    FROZEN_TREE.  Raises when the object is present but is not a commit, has no
    frozen subtree, or records a different one: available provenance that
    disagrees with the pin is a hard failure, never a skip.
    """
    object_type = git_probe("cat-file", "-t", FROZEN_COMMIT)
    if object_type is None:
        return False
    if object_type != "commit":
        raise ValueError(
            f"reviewed provenance {FROZEN_COMMIT} is present as a {object_type}, "
            "not a commit"
        )
    recorded = git_probe("rev-parse", "--verify", f"{FROZEN_COMMIT}:{TREE}")
    if recorded is None:
        raise ValueError(
            f"reviewed provenance commit {FROZEN_COMMIT} is present but records "
            f"no {TREE!r} subtree"
        )
    if recorded != FROZEN_TREE:
        raise ValueError(
            f"reviewed provenance commit {FROZEN_COMMIT} records {TREE} as tree "
            f"{recorded}, not the frozen tree {FROZEN_TREE}"
        )
    return True


def frozen_tree_object() -> str:
    """Resolve FROZEN_TREE, with an exact diagnostic when it is unavailable."""
    object_type = git_probe("cat-file", "-t", FROZEN_TREE)
    if object_type is None:
        raise ValueError(
            f"frozen tree object {FROZEN_TREE} is absent from this repository, so "
            f"the frozen {TREE} content cannot be enumerated"
        )
    if object_type != "tree":
        raise ValueError(
            f"frozen tree {FROZEN_TREE} is present as a {object_type}, not a tree"
        )
    return FROZEN_TREE


def frozen_git_entries() -> dict[str, dict[str, str]]:
    """Enumerate the frozen subtree from its authoritative tree object.

    `git ls-tree` on a tree object yields tree-relative paths, so each record is
    re-prefixed with TREE to rebuild the repository-relative manifest keys.
    """
    records = git("ls-tree", "-r", "-z", frozen_tree_object()).split(b"\0")
    result: dict[str, dict[str, str]] = {}
    for record in records:
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, object_type, oid = metadata.decode("ascii").split()
        rel = f"{TREE}/{os.fsdecode(raw_path)}"
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
        "frozen_tree": FROZEN_TREE,
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
        "frozen_tree": FROZEN_TREE,
        "tree": TREE,
    }
    for key, value in required.items():
        if data.get(key) != value:
            raise ValueError(f"manifest {key!r} must equal {value!r}")
    files = data.get("files")
    if not isinstance(files, dict):
        raise ValueError("manifest 'files' must be an object")
    if files != frozen_git_entries():
        raise ValueError(
            f"manifest entries do not match the Git objects in frozen tree {FROZEN_TREE}"
        )
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



def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate-root", type=Path, default=ROOT)
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    try:
        provenance = verify_provenance()
        if args.write_manifest:
            args.manifest.write_text(
                json.dumps(manifest_data(), indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            print(f"[tmverifier-freeze] wrote {args.manifest}")
            return 0
        expected = load_manifest(args.manifest.resolve())
        actual = working_entries(args.candidate_root.resolve())
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
    if added or removed or changed:
        print("TMVerifier freeze violation.", file=sys.stderr)
        for label, paths in (("Added", added), ("Removed", removed), ("Changed", changed)):
            if paths:
                print(f"  {label}:", *paths, sep="\n    ", file=sys.stderr)

        print(
            f"The tree is frozen at Git tree {FROZEN_TREE} (reviewed at "
            f"{FROZEN_COMMIT}). Use a separately reviewed unfreeze/migration PR "
            "to alter it.",
            file=sys.stderr,
        )
        return 1

    provenance_note = (
        f"reviewed provenance {FROZEN_COMMIT[:12]} verified"
        if provenance
        else f"reviewed provenance {FROZEN_COMMIT[:12]} absent from this history"
    )
    print(
        f"[tmverifier-freeze] OK: {len(expected)} Git objects match tree "
        f"{FROZEN_TREE[:12]} ({provenance_note})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
