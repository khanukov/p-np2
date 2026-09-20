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
reviewed provenance resolves and records exactly ``FROZEN_TREE``, and when it
does write it replaces the target atomically instead of truncating it.

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
import tempfile
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


def probe_environment() -> dict[str, str]:
    """The environment for the one Git call whose stderr carries meaning.

    `git_object` reads stderr as a signal rather than as decoration, so anything
    that writes to it for an unrelated reason would be misread as a Git
    diagnostic.  Git's own tracing switches do exactly that: `GIT_TRACE=1`,
    `GIT_TRACE2=1`, `GIT_TRACE_SETUP=1` and their relatives print command and
    timing chatter to stderr on every invocation, which would turn a genuinely
    absent object into a "present but unusable" hard failure for anyone
    debugging something else in the same shell or runner.  Every `GIT_TRACE*`
    variable is therefore dropped from this probe's environment, and only from
    this probe's: the enumerating calls in `git()` leave the environment alone,
    so tracing still works for everything it is normally turned on for.

    Nothing else is filtered.  A real diagnostic — corruption, an unreadable
    object store, a failed promisor fetch — still reaches the classifier and
    still fails closed.
    """
    return {
        name: value
        for name, value in os.environ.items()
        if not name.startswith("GIT_TRACE")
    }


def git_object(spec: str) -> tuple[str, str] | None:
    """Resolve `spec` to its (object id, object type), or None when it is absent.

    `git cat-file --batch-check` answers `<spec> missing` with exit status 0
    both when an object genuinely is not in this object store and when Git found
    it but could not read it.  The two are told apart by Git's own diagnostics:
    a genuine miss is silent, while corruption, an unreadable object store, a
    failed promisor fetch or a damaged pack is announced on stderr.  That test
    is only sound if stderr is Git's alone, which is what `probe_environment`
    arranges.

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
        env=probe_environment(),
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
    `--full-tree` is what makes that true from anywhere: without it `ls-tree`
    limits the listing to Git's current-directory prefix, which is empty only
    when this checkout happens to be the root of the repository holding its
    objects.  A copy nested inside another repository — a vendored export, a
    fixture directory, a checkout made under someone else's worktree — sits
    under a non-empty prefix, the frozen tree object has nothing under that
    prefix, and the enumeration would come back empty, reporting a perfectly
    readable authoritative tree as a manifest mismatch.  With `--full-tree` the
    listing is taken from the root of the named tree object, so the paths stay
    tree-relative and the TREE re-prefix below is unchanged.

    The per-entry reads go through `git()`, which raises on any nonzero exit and
    lets Git's own message through: a blob inside the tree that Git cannot
    inflate stops the enumeration with that error rather than producing a short
    manifest, so damage below the tree object fails closed too — as a read
    failure, never as an absence.
    """
    records = git("ls-tree", "-r", "-z", "--full-tree", frozen_tree_object()).split(b"\0")
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


def manifest_payload() -> str:
    """Produce the complete manifest bytes, before any destination is touched.

    Enumeration, serialization and a round-trip of the serialized form all
    happen here, so every way authoring can fail on its own account fails while
    the old manifest is still intact.  The round-trip is not ceremony: it is the
    same duplicate-rejecting decode `load_manifest` will perform, applied to the
    exact bytes about to be installed, so what is written is known to read back
    as what was enumerated.
    """
    data = manifest_data()
    payload = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if json.loads(payload, object_pairs_hook=unique_object) != data:
        raise ValueError(
            "serialized manifest does not decode back to the enumerated frozen tree"
        )
    return payload


def install_mode(target: Path) -> int:
    """The permission bits a freshly installed `target` should end up with.

    `tempfile` creates its file 0600 and `os.replace` carries that mode across,
    so without this a regeneration would silently narrow the manifest's
    permissions.  An existing regular file keeps exactly the mode it had; a new
    one gets the ordinary umask-derived default, read by the only means the C
    library offers — setting it and putting it straight back.
    """
    try:
        info = target.lstat()
    except FileNotFoundError:
        info = None
    if info is not None and stat.S_ISREG(info.st_mode):
        return stat.S_IMODE(info.st_mode)
    umask = os.umask(0)
    os.umask(umask)
    return 0o666 & ~umask


def fsync_directory(directory: Path) -> None:
    """Make the rename itself durable, on the platforms that can express it.

    Atomicity for a concurrent reader is already guaranteed by `os.replace`
    without this; fsyncing the directory is only about surviving a crash between
    the rename and the filesystem's own flush.  Opening a directory as a file is
    a POSIX facility that Windows does not offer, so the step is skipped there
    rather than faked.  Where it is attempted and fails, that is reported as the
    durability warning it is, and not as a failure of an installation that did
    in fact happen.
    """
    if os.name != "posix":
        return
    try:
        descriptor = os.open(directory, os.O_RDONLY)
    except OSError as exc:
        print(
            f"[tmverifier-freeze] warning: could not open {directory} to flush it: {exc}",
            file=sys.stderr,
        )
        return
    try:
        os.fsync(descriptor)
    except OSError as exc:
        print(
            f"[tmverifier-freeze] warning: could not flush {directory}: {exc}",
            file=sys.stderr,
        )
    finally:
        os.close(descriptor)


def install_file(target: Path, payload: str) -> None:
    """Put `payload` at `target` by replacement, so nothing can truncate it.

    `Path.write_text` opens the destination for truncation before it writes a
    byte, so an I/O error, a full disk or a signal partway through destroys the
    old manifest and leaves an unusable fragment in its place.  Here the bytes
    go to a fresh file created in the destination's own directory — the same
    directory, so the install is a rename within one filesystem and therefore
    atomic — and they are flushed and fsynced before that rename swaps them in.
    A reader of `target` sees either all of the old bytes or all of the new
    ones, and every failure path unlinks the temporary file it created.

    A symlinked target is replaced rather than followed: that is `os.replace`'s
    documented behaviour, and it is the safer one for a governance artifact.
    """
    temp_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=target.parent,
            prefix=f".{target.name}.",
            suffix=".tmp",
            delete=False,
        ) as handle:
            temp_path = Path(handle.name)
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temp_path, install_mode(target))
        os.replace(temp_path, target)
    except BaseException:
        if temp_path is not None:
            temp_path.unlink(missing_ok=True)
        raise
    fsync_directory(target.parent)


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
    """Describe the candidate copy the way Git would describe it.

    The manifest records Git's modes, so the filesystem side has to derive them
    by Git's rule and not by a looser one: Git calls a regular file `100755`
    when its *owner* execute bit is set and `100644` otherwise, and the group
    and other execute bits do not enter into it.  Reading any execute bit would
    report `100755` for a `0o654` file that Git — and therefore the frozen tree
    — records as `100644`, failing a checkout for a mode change Git does not
    see.  Nothing else here defers to Git: content is compared by SHA-256 of the
    bytes on disk, symlinks are hashed as their target text rather than
    followed, and anything that is neither a regular file nor a symlink is
    recorded as `special`, which no frozen entry can match.
    """
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
            mode = "100755" if info.st_mode & stat.S_IXUSR else "100644"
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
    parser.add_argument(
        "--candidate-root",
        type=Path,
        default=ROOT,
        help=(
            "filesystem tree holding the copy of the frozen subtree to compare "
            "against the manifest (default: this repository); ignored with "
            "--write-manifest, which reads Git and never the working tree"
        ),
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=MANIFEST,
        help="manifest to verify, or to regenerate with --write-manifest",
    )
    parser.add_argument(
        "--write-manifest",
        action="store_true",
        help=(
            "regenerate the manifest from the frozen tree instead of verifying "
            "a working tree; refuses unless the reviewed provenance commit "
            "resolves here and records exactly the frozen tree"
        ),
    )
    args = parser.parse_args()
    try:
        provenance = verify_provenance()
        if args.write_manifest:
            # Authoring is strict where verification is not.  A checkout that
            # has lost the reviewed commit may still verify content against
            # FROZEN_TREE, but it cannot prove the commit/tree pair a new
            # manifest would assert, so it must not be allowed to author one.
            # It reads Git alone: --candidate-root names the filesystem side of
            # verification, which has no counterpart here and is ignored.
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
            install_file(args.manifest, manifest_payload())
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
