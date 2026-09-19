#!/usr/bin/env python3
"""Verify the content-addressed freeze of pnp3/Complexity/TMVerifier.

The frozen content is enumerated from ``FROZEN_TREE``, the Git tree object of
the frozen subtree.  Tree objects are content-addressed, so that enumeration
survives every history rewrite: a squash merge, a rebase, a branch force-push,
and a shallow or single-branch clone all still carry the tree object, as long as
they carry a Git object store that holds those bytes.  Carrying the bytes alone
is not sufficient: an exported working tree — ``git archive``, a release
tarball, any ``.git``-less copy — has byte-identical content and no object
store, so it cannot be verified here and is refused rather than passed.
``FROZEN_TREE`` is the authoritative source this checker verifies against.

``FROZEN_COMMIT`` is retained as *reviewed provenance*: the commit at which the
frozen bytes were reviewed and re-pinned.  It is no longer the enumeration
source.  When the checkout still contains it, its subtree is cross-checked
against ``FROZEN_TREE``; when a rewritten or shallow history no longer contains
it, content verification proceeds unchanged.  Provenance that is present but
malformed or disagreeing fails closed, and so does any Git failure that leaves
the question unanswered — absence is concluded only from Git's own silent
``missing`` reply, never from a command that merely failed.  Manifest authoring
(``--write-manifest``) is stricter still: it refuses to write unless the
reviewed provenance resolves and records exactly ``FROZEN_TREE``.

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
# The object types `git cat-file --batch-check` can report for a resolved spec.
OBJECT_TYPES = ("blob", "tree", "commit", "tag")


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


def git_object(spec: str) -> tuple[str, str] | None:
    """Resolve `spec` to its (object id, object type), or None when it is absent.

    `git cat-file --batch-check` answers `<spec> missing` with exit status 0
    both when an object genuinely is not in this object store and when Git found
    it but could not read it.  The two are told apart by Git's own diagnostics:
    a genuine miss is silent, while corruption, an unreadable object store, a
    failed promisor fetch or a damaged pack is announced on stderr.

    None therefore means, and only means, that Git reported the object missing
    without emitting a single diagnostic.  A nonzero exit status, a terminating
    signal, any diagnostic accompanying a `missing` answer, and any reply this
    function cannot parse all raise, with Git's own stderr preserved in the
    message.  A present-but-unreadable object is never reported as an absent
    one, and no Git failure is ever silently answered.
    """
    process = subprocess.run(
        ["git", "-C", str(ROOT), "cat-file", "--batch-check", "--buffer"],
        input=f"{spec}\n".encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    stdout = process.stdout.decode("utf-8", "replace").strip()
    stderr = process.stderr.decode("utf-8", "replace").strip()
    if process.returncode != 0:
        raise ValueError(
            f"git cat-file --batch-check {spec} failed with exit status "
            f"{process.returncode}: {stderr or '(no stderr)'}"
        )
    fields = stdout.split()
    if len(fields) == 2 and fields[1] == "missing":
        if stderr:
            raise ValueError(
                f"git reported {spec} missing but could not read this object "
                f"store, so it is present but unusable, not absent: {stderr}"
            )
        return None
    if len(fields) == 3 and fields[1] in OBJECT_TYPES:
        return fields[0], fields[1]
    raise ValueError(
        f"unexpected git cat-file --batch-check reply for {spec}: {stdout!r}"
        + (f" (stderr: {stderr})" if stderr else "")
    )


def verify_provenance() -> bool:
    """Cross-check the reviewed provenance commit when this history still has it.

    Returns True when FROZEN_COMMIT was available and recorded TREE as
    FROZEN_TREE, and False only when Git reports the object genuinely absent —
    the rewritten or shallow-clone case, in which content verification still
    proceeds from FROZEN_TREE.  Raises when the object is present but is not a
    commit, has no frozen subtree, or records a different one, and raises when
    Git could not answer at all: provenance that disagrees with the pin, and a
    Git failure that leaves the question open, are both hard failures and never
    a skip.
    """
    found = git_object(FROZEN_COMMIT)
    if found is None:
        return False
    _, object_type = found
    if object_type != "commit":
        raise ValueError(
            f"reviewed provenance {FROZEN_COMMIT} is present as a {object_type}, "
            "not a commit"
        )
    subtree = git_object(f"{FROZEN_COMMIT}:{TREE}")
    if subtree is None:
        raise ValueError(
            f"reviewed provenance commit {FROZEN_COMMIT} is present but records "
            f"no {TREE!r} subtree"
        )
    recorded, _ = subtree
    if recorded != FROZEN_TREE:
        raise ValueError(
            f"reviewed provenance commit {FROZEN_COMMIT} records {TREE} as tree "
            f"{recorded}, not the frozen tree {FROZEN_TREE}"
        )
    return True


def frozen_tree_object() -> str:
    """Resolve FROZEN_TREE, with an exact diagnostic when it is unavailable.

    Absence and unreadability are reported as the different things they are: an
    object store Git cannot read raises `git_object`'s Git-level diagnostic, and
    only an object Git reports genuinely missing is called absent here.
    """
    found = git_object(FROZEN_TREE)
    if found is None:
        raise ValueError(
            f"frozen tree object {FROZEN_TREE} is absent from this repository, so "
            f"the frozen {TREE} content cannot be enumerated"
        )
    _, object_type = found
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
    """Load the manifest and hold it to the pin, entry by entry.

    Duplicate keys are rejected outright; unrecognised top-level keys are
    ignored, deliberately, because the manifest carries no independent
    authority: the four scalars below must equal this checker's own constants,
    and `files` must equal what Git reports for the frozen tree, so an extra key
    can neither add nor weaken a claim.
    """
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
            # Authoring is strict where verification is not.  A checkout that
            # has lost the reviewed commit may still verify content against
            # FROZEN_TREE, but it cannot prove the commit/tree pair a new
            # manifest would assert, so it must not be allowed to author one.
            if not provenance:
                raise ValueError(
                    f"refusing to write {args.manifest}: reviewed provenance "
                    f"commit {FROZEN_COMMIT} is absent from this repository, so "
                    "the commit/tree pair this manifest would record cannot be "
                    "verified. Commit the new frozen bytes first, repin "
                    "FROZEN_COMMIT and FROZEN_TREE onto that commit, then "
                    "regenerate; see the unfreeze recipe in "
                    "pnp3/Docs/TMVERIFIER_FREEZE.md."
                )
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
