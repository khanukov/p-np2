#!/usr/bin/env python3
"""Negative controls for the TMVerifier freeze checker.

Besides the manifest-trust and filesystem controls, this exercises the
properties the tree pin buys: the checker must still verify content in a
rewritten history where the reviewed provenance commit does not exist; it must
fail closed whenever provenance *is* available but disagrees with the pin; it
must never report a present-but-unreadable object, or a Git failure of any
other kind, as an absent one; it must not mistake Git's own tracing output for
a Git diagnostic; and manifest authoring must refuse to write at all unless the
reviewed provenance resolves and matches, and must replace its target rather
than truncate it when it does write.  This suite itself must pass in a checkout
that has lost the reviewed commit, which one control asserts by running the
whole suite inside such a repository.  All of it runs end to end against the
real checker source — unmodified, or repinned onto a synthetic object by
textual constant substitution — in real synthetic Git repositories, never
against a stand-in.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TREE = "pnp3/Complexity/TMVerifier"
SOURCE = ROOT / TREE
CHECKER = ROOT / "scripts/check_tmverifier_freeze.py"
SUITE = Path(__file__).resolve()
MANIFEST = ROOT / "spec/tmverifier_freeze.json"
VERSION_MANIFEST = ROOT / "spec/version_manifest.toml"
TARGET = Path("pnp3/Complexity/TMVerifier/TuringToolkit/GateNBodyRound.lean")

_REVIEWED = json.loads(MANIFEST.read_text(encoding="utf-8"))
FROZEN_COMMIT = _REVIEWED["frozen_commit"]
FROZEN_TREE = _REVIEWED["frozen_tree"]

# Set by the provenance-free control below on the copy of this suite it runs
# inside its own fixture, so that copy does not build the same fixture again.
NESTED_VARIABLE = "TMVERIFIER_FREEZE_TEST_NESTED"

# Run the real checker as `__main__` with one `os` primitive replaced by a
# certain failure, so a permitted write can be interrupted deterministically at
# a chosen point.  argv is <checker> <os attribute to break> <checker args...>.
ATOMIC_HARNESS = '''\
import os
import runpy
import sys

checker, broken, *arguments = sys.argv[1:]


def fail(*args, **kwargs):
    raise OSError(f"injected {broken} failure")


setattr(os, broken, fail)
sys.argv = [checker, *arguments]
runpy.run_path(checker, run_name="__main__")
'''

# Synthetic repositories are built with no global or system Git configuration so
# no filter or line-ending rule can rewrite the frozen blobs; that is what lets
# the copied subtree reproduce FROZEN_TREE byte-for-byte.
GIT_ENV = {
    **os.environ,
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_SYSTEM": os.devnull,
    "GIT_AUTHOR_NAME": "tmverifier-freeze-test",
    "GIT_AUTHOR_EMAIL": "tmverifier-freeze-test@example.invalid",
    "GIT_COMMITTER_NAME": "tmverifier-freeze-test",
    "GIT_COMMITTER_EMAIL": "tmverifier-freeze-test@example.invalid",
}


def run(
    candidate: Path | None,
    expect_ok: bool,
    manifest: Path | None = None,
    checker: Path = CHECKER,
    cwd: Path = ROOT,
    env: dict[str, str] | None = None,
    write_manifest: bool = False,
) -> str:
    command = [str(checker)]
    if candidate is not None:
        command.extend(["--candidate-root", str(candidate)])
    if manifest is not None:
        command.extend(["--manifest", str(manifest)])
    if write_manifest:
        command.append("--write-manifest")
    result = subprocess.run(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=env,
        check=False,
    )
    if (result.returncode == 0) != expect_ok:
        raise AssertionError(
            f"checker return code {result.returncode}, expected_ok={expect_ok}\n{result.stdout}"
        )
    return result.stdout


def expect_text(output: str, needle: str, label: str) -> None:
    if needle not in output:
        raise AssertionError(f"{label}: expected {needle!r} in checker output\n{output}")


def expect_no_text(output: str, needle: str, label: str) -> None:
    """Assert the checker did *not* say something — a wrong diagnosis is a bug.

    Failing closed is not enough for the object-state controls below: a checker
    that fails for the right reason and a checker that calls a damaged object
    store an absent one both exit nonzero, and only this distinguishes them.
    """
    if needle in output:
        raise AssertionError(f"{label}: unexpected {needle!r} in checker output\n{output}")


def expect_unwritten(path: Path, label: str) -> None:
    if path.exists():
        raise AssertionError(f"{label}: refused authoring still created {path}")


def listing(directory: Path) -> set[str]:
    """Every name in `directory`, so a comparison can catch temporary litter."""
    return {entry.name for entry in directory.iterdir()}


def nested() -> bool:
    """Whether this run is the one `provenance_free_suite_control` started."""
    return os.environ.get(NESTED_VARIABLE) == "1"


def fixture(parent: Path) -> Path:
    root = parent / "candidate"
    shutil.copytree(SOURCE, root / SOURCE.relative_to(ROOT), symlinks=True)
    return root


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], env=GIT_ENV, text=True
    ).strip()


def has_object(repo: Path, object_id: str) -> bool:
    """Whether `object_id` is in `repo`'s object store, failing loudly otherwise.

    `git cat-file -e` exits 0 when the object is there and 1 when it is not.
    Every other status means Git could not answer, and the fixture assertions
    built on this helper would be worthless if that were quietly recorded as a
    clean absence — the very conflation the checker itself must avoid.
    """
    result = subprocess.run(
        ["git", "-C", str(repo), "cat-file", "-e", object_id],
        env=GIT_ENV,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if result.returncode not in (0, 1):
        raise AssertionError(
            f"git cat-file -e {object_id} in {repo} failed with exit status "
            f"{result.returncode}: {result.stderr.strip()}"
        )
    return result.returncode == 0


def corrupt_loose_object(repo: Path, object_id: str) -> None:
    """Overwrite one loose object with bytes Git cannot inflate.

    This is what a damaged object store, a truncated transfer or a half-written
    object looks like from the checker's side: the object file is there, Git
    answers `missing` for it, and says so with a diagnostic on stderr.
    """
    path = repo / ".git" / "objects" / object_id[:2] / object_id[2:]
    if not path.is_file():
        raise AssertionError(f"expected a loose object to corrupt at {path}")
    path.write_bytes(b"present, unreadable, and definitely not a zlib stream\n")


def scaffold(root: Path, with_suite: bool = False) -> Path:
    """Lay out a standalone repository root holding the frozen subtree.

    The checker resolves its own repository from `__file__`, so placing a copy
    under `scripts/` is what makes the synthetic repository the one it inspects.
    `with_suite` additionally copies this suite and the version manifest it
    cross-checks, which is what lets the whole suite be run inside the fixture.
    """
    shutil.copytree(SOURCE, root / TREE, symlinks=True)
    (root / "scripts").mkdir(parents=True, exist_ok=True)
    (root / "spec").mkdir(parents=True, exist_ok=True)
    shutil.copy2(CHECKER, root / "scripts" / CHECKER.name)
    shutil.copy2(MANIFEST, root / "spec" / MANIFEST.name)
    if with_suite:
        shutil.copy2(SUITE, root / "scripts" / SUITE.name)
        shutil.copy2(VERSION_MANIFEST, root / "spec" / VERSION_MANIFEST.name)
    return root


def init_commit(root: Path, message: str) -> str:
    git(root, "init", "-q")
    git(root, "config", "core.autocrlf", "false")
    git(root, "add", "-A")
    git(root, "commit", "-q", "-m", message)
    return git(root, "rev-parse", "HEAD")


def checker_variant(destination: Path, **constants: str) -> Path:
    """Copy the checker under test, repinning named 40-hex constants.

    The body stays the real checker, so the provenance controls below drive its
    actual code path rather than a re-implementation of it.
    """
    source = CHECKER.read_text(encoding="utf-8")
    for name, value in constants.items():
        source, count = re.subn(
            rf'^{name} = "[0-9a-f]{{40}}"$',
            f'{name} = "{value}"',
            source,
            flags=re.MULTILINE,
        )
        if count != 1:
            raise AssertionError(f"could not repin {name} in the checker source")
    destination.write_text(source, encoding="utf-8")
    destination.chmod(0o755)
    return destination


def repinned_manifest(path: Path, commit: str) -> Path:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    data["frozen_commit"] = commit
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def rewritten_history_controls(parent: Path) -> None:
    """The property the tree pin buys: content checking survives a rewrite.

    `rewritten` is a squash-style history — one unrelated commit carrying the
    identical subtree bytes, with the reviewed provenance commit absent from the
    object store entirely.  `drifted` is the same construction over drifted
    bytes, and proves the pass above is real content verification rather than a
    check that quietly skips itself when provenance is missing.
    """
    rewritten = scaffold(parent / "rewritten")
    head = init_commit(rewritten, "Squashed rewrite of the whole migration branch")
    if has_object(rewritten, FROZEN_COMMIT):
        raise AssertionError("the synthetic rewrite still contains the reviewed commit")
    if git(rewritten, "rev-list", "--count", "HEAD") != "1":
        raise AssertionError("the synthetic rewrite must be a single-commit history")
    if head == FROZEN_COMMIT:
        raise AssertionError("the synthetic rewrite must land under an unrelated commit")
    if git(rewritten, "cat-file", "-t", FROZEN_TREE) != "tree":
        raise AssertionError("the synthetic rewrite does not carry the frozen tree object")
    if git(rewritten, "rev-parse", f"HEAD:{TREE}") != FROZEN_TREE:
        raise AssertionError("the synthetic rewrite subtree is not the frozen tree")
    checker = rewritten / "scripts" / CHECKER.name
    output = run(None, True, checker=checker, cwd=rewritten, env=GIT_ENV)
    expect_text(
        output, f"reviewed provenance {FROZEN_COMMIT[:12]} absent", "rewritten history"
    )
    expect_text(output, f"{len(_REVIEWED['files'])} Git objects", "rewritten history")

    # Genuine absence is enough to verify content and deliberately not enough to
    # author a manifest: the refusal must be reported and must leave the file it
    # was asked to write alone.
    fresh = rewritten / "spec" / "authored-absent.json"
    output = run(
        None,
        False,
        fresh,
        checker=checker,
        cwd=rewritten,
        env=GIT_ENV,
        write_manifest=True,
    )
    expect_text(output, "refusing to write", "rewritten history/write")
    expect_unwritten(fresh, "rewritten history/write")

    existing = rewritten / "spec" / "authored-existing.json"
    sentinel = b'{"not": "a manifest"}\n'
    existing.write_bytes(sentinel)
    run(
        None,
        False,
        existing,
        checker=checker,
        cwd=rewritten,
        env=GIT_ENV,
        write_manifest=True,
    )
    if existing.read_bytes() != sentinel:
        raise AssertionError("refused authoring overwrote an existing target")

    drifted = scaffold(parent / "drifted")
    with (drifted / TARGET).open("ab") as handle:
        handle.write(b"\n-- rewritten-history negative control\n")
    init_commit(drifted, "Squashed rewrite carrying drifted frozen bytes")
    if has_object(drifted, FROZEN_TREE):
        raise AssertionError("the drifted rewrite unexpectedly carries the frozen tree")
    output = run(
        None,
        False,
        checker=drifted / "scripts" / CHECKER.name,
        cwd=drifted,
        env=GIT_ENV,
    )
    expect_text(output, "absent from this repository", "drifted rewrite")


def provenance_controls(parent: Path) -> None:
    """Available provenance must be cross-checked, never trusted blindly.

    One repository holds the exact frozen subtree plus two deliberately wrong
    provenance commits.  Checker copies repinned onto each of them must fail;
    the copy repinned onto the matching commit must pass, and must say
    `verified` rather than merely mentioning provenance, so that a mutation
    downgrading a matching cross-check to a skip cannot survive this control.
    Every failing pin is run a second time in authoring mode, where it must be
    refused without touching the manifest it was told to write.
    """
    repo = scaffold(parent / "provenance")
    good = init_commit(repo, "Unrelated commit carrying the exact frozen subtree")
    default_branch = git(repo, "rev-parse", "--abbrev-ref", "HEAD")

    git(repo, "checkout", "-q", "-b", "divergent")
    (repo / TREE / "Unreviewed.lean").write_text("def unreviewed := 0\n", encoding="utf-8")
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "-m", "Divergent subtree")
    divergent = git(repo, "rev-parse", "HEAD")
    git(repo, "checkout", "-q", default_branch)

    git(repo, "checkout", "-q", "-b", "bare")
    git(repo, "rm", "-r", "-q", "--", TREE)
    git(repo, "commit", "-q", "-m", "No frozen subtree at all")
    bare = git(repo, "rev-parse", "HEAD")
    git(repo, "checkout", "-q", default_branch)

    if has_object(repo, FROZEN_COMMIT):
        raise AssertionError("the provenance fixture must not contain the reviewed commit")
    if git(repo, "rev-parse", f"{good}:{TREE}") != FROZEN_TREE:
        raise AssertionError("the provenance fixture does not carry the frozen tree")
    if git(repo, "rev-parse", f"{divergent}:{TREE}") == FROZEN_TREE:
        raise AssertionError("the divergent commit must record a different subtree")

    scripts = repo / "scripts"
    cases = (
        ("matching", good, True, f"reviewed provenance {good[:12]} verified"),
        ("divergent", divergent, False, "not the frozen tree"),
        ("missing-subtree", bare, False, "records no"),
        ("not-a-commit", FROZEN_TREE, False, "not a commit"),
    )
    for label, commit, expect_ok, needle in cases:
        checker = checker_variant(scripts / f"check-{label}.py", FROZEN_COMMIT=commit)
        manifest = repinned_manifest(repo / "spec" / f"manifest-{label}.json", commit)
        output = run(repo, expect_ok, manifest, checker=checker, cwd=repo, env=GIT_ENV)
        expect_text(output, needle, f"provenance/{label}")

        authored = repo / "spec" / f"authored-{label}.json"
        output = run(
            repo,
            expect_ok,
            authored,
            checker=checker,
            cwd=repo,
            env=GIT_ENV,
            write_manifest=True,
        )
        if not expect_ok:
            expect_text(output, needle, f"provenance/{label}/write")
            expect_unwritten(authored, f"provenance/{label}/write")
            continue
        # The one pin that does verify must still author the reviewed content,
        # so the refusals above are attributable to provenance alone.
        written = json.loads(authored.read_text(encoding="utf-8"))
        if written["frozen_commit"] != commit:
            raise AssertionError("authored manifest does not record the verified commit")
        if written["frozen_tree"] != FROZEN_TREE or written["files"] != _REVIEWED["files"]:
            raise AssertionError("authored manifest does not reproduce the frozen tree")


def object_state_controls(parent: Path) -> None:
    """A present-but-unreadable object is not an absent one, for either pin.

    Each pinned object gets its own repository in which that object's loose file
    is overwritten with bytes Git cannot inflate.  Git then answers `missing`
    for it — with a diagnostic — which is exactly the reply a genuinely absent
    object produces silently.  The checker must fail closed *and* must not
    diagnose absence, so restoring the old "every Git failure means absent"
    probe cannot pass these.
    """
    provenance = scaffold(parent / "corrupt-provenance")
    good = init_commit(provenance, "Exact frozen subtree under a readable commit")
    checker = checker_variant(
        provenance / "scripts" / "check-corrupt.py", FROZEN_COMMIT=good
    )
    manifest = repinned_manifest(provenance / "spec" / "manifest-corrupt.json", good)
    output = run(provenance, True, manifest, checker=checker, cwd=provenance, env=GIT_ENV)
    expect_text(output, f"reviewed provenance {good[:12]} verified", "corrupt/intact")

    corrupt_loose_object(provenance, good)
    if not has_object(provenance, good):
        raise AssertionError("the corrupted provenance object must still be present")
    output = run(provenance, False, manifest, checker=checker, cwd=provenance, env=GIT_ENV)
    expect_text(output, "present but unusable, not absent", "corrupt/provenance")
    expect_no_text(output, "absent from this history", "corrupt/provenance")

    authored = provenance / "spec" / "authored-corrupt.json"
    output = run(
        provenance,
        False,
        authored,
        checker=checker,
        cwd=provenance,
        env=GIT_ENV,
        write_manifest=True,
    )
    expect_text(output, "present but unusable, not absent", "corrupt/provenance/write")
    expect_unwritten(authored, "corrupt/provenance/write")

    tree = scaffold(parent / "corrupt-tree")
    init_commit(tree, "Exact frozen subtree with a damaged tree object")
    corrupt_loose_object(tree, FROZEN_TREE)
    if not has_object(tree, FROZEN_TREE):
        raise AssertionError("the corrupted frozen tree object must still be present")
    output = run(None, False, checker=tree / "scripts" / CHECKER.name, cwd=tree, env=GIT_ENV)
    expect_text(output, "present but unusable, not absent", "corrupt/tree")
    expect_no_text(output, "absent from this repository", "corrupt/tree")

    # Damage below the two pinned objects is not classified by the object probe
    # at all — a blob is read by the enumerating `git()` call, which raises on
    # Git's own nonzero exit.  That path has no way to answer "absent", and this
    # holds it to failing closed with Git's message rather than silently
    # producing a manifest one entry short.
    blob = scaffold(parent / "corrupt-blob")
    init_commit(blob, "Exact frozen subtree with a damaged blob inside it")
    metadata, _ = git(blob, "ls-tree", "-r", FROZEN_TREE).split("\n", 1)[0].split("\t", 1)
    _, entry_type, entry_oid = metadata.split()
    if entry_type != "blob":
        raise AssertionError(f"expected a blob as the first frozen entry, got {entry_type}")
    corrupt_loose_object(blob, entry_oid)
    output = run(None, False, checker=blob / "scripts" / CHECKER.name, cwd=blob, env=GIT_ENV)
    expect_text(output, "TMVerifier freeze check failed", "corrupt/blob")
    expect_text(output, entry_oid, "corrupt/blob")
    expect_no_text(output, "absent", "corrupt/blob")


def no_object_store_control(parent: Path) -> None:
    """Carrying the frozen bytes is not carrying the frozen tree object.

    A `git archive` export, a release tarball or any other `.git`-less copy has
    byte-identical content and no object store.  Git cannot answer at all there,
    which must be reported as the repository failure it is rather than as two
    absent objects.
    """
    export = scaffold(parent / "export")
    if (export / ".git").exists():
        raise AssertionError("the export fixture must not be a Git repository")
    env = {**GIT_ENV, "GIT_CEILING_DIRECTORIES": str(parent)}
    output = run(None, False, checker=export / "scripts" / CHECKER.name, cwd=export, env=env)
    expect_text(output, "not a git repository", "export")
    expect_no_text(output, "absent from this history", "export")
    expect_no_text(output, "absent from this repository", "export")


def authoring_controls(parent: Path) -> None:
    """A permitted write installs the manifest whole, or does not touch it.

    Provenance decides *whether* authoring may run; these controls are about
    what happens once it may.  The manifest is replaced by a rename of a fully
    written file rather than by truncating the destination, so a failure part
    way through — an I/O error, a full disk, a signal — cannot leave the
    reviewed manifest destroyed or half-rewritten.  The two failure points that
    bracket the rename are injected deterministically into the real checker:
    after the bytes reach the temporary file, and at the rename itself.  In both
    cases an existing target must come out byte-identical and the directory must
    be left with no temporary file in it.  A last control pins the other half of
    "authoring reads Git": it is given a deliberately drifted `--candidate-root`
    and must still author the frozen tree's content.
    """
    repo = scaffold(parent / "authoring")
    good = init_commit(repo, "Exact frozen subtree under a resolvable commit")
    checker = checker_variant(repo / "scripts" / "check-authoring.py", FROZEN_COMMIT=good)
    harness = parent / "atomic-harness.py"
    harness.write_text(ATOMIC_HARNESS, encoding="utf-8")
    spec = repo / "spec"

    fresh = spec / "authored-fresh.json"
    before = listing(spec)
    run(None, True, fresh, checker=checker, cwd=repo, env=GIT_ENV, write_manifest=True)
    if listing(spec) != before | {fresh.name}:
        raise AssertionError("authoring a new manifest left temporary files behind")
    authored = json.loads(fresh.read_text(encoding="utf-8"))
    if authored["frozen_tree"] != FROZEN_TREE or authored["files"] != _REVIEWED["files"]:
        raise AssertionError("authored manifest does not reproduce the frozen tree")

    existing = spec / "authored-existing.json"
    sentinel = b'{"not": "a manifest"}\n'
    for broken in ("fsync", "replace"):
        existing.write_bytes(sentinel)
        before = listing(spec)
        result = subprocess.run(
            [
                sys.executable,
                str(harness),
                str(checker),
                broken,
                "--manifest",
                str(existing),
                "--write-manifest",
            ],
            cwd=repo,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env=GIT_ENV,
            check=False,
        )
        if result.returncode == 0:
            raise AssertionError(
                f"authoring/{broken}: an injected failure was reported as success\n"
                f"{result.stdout}"
            )
        expect_text(result.stdout, f"injected {broken} failure", f"authoring/{broken}")
        if existing.read_bytes() != sentinel:
            raise AssertionError(
                f"authoring/{broken}: a failed write did not leave the existing "
                "target byte-identical"
            )
        if listing(spec) != before:
            raise AssertionError(
                f"authoring/{broken}: a failed write left a temporary file behind"
            )

    existing.write_bytes(sentinel)
    existing.chmod(0o644)
    before = listing(spec)
    run(None, True, existing, checker=checker, cwd=repo, env=GIT_ENV, write_manifest=True)
    if json.loads(existing.read_text(encoding="utf-8"))["files"] != _REVIEWED["files"]:
        raise AssertionError("a permitted write did not replace the existing target")
    if listing(spec) != before:
        raise AssertionError("replacing an existing manifest left temporary files behind")
    # The replacement installs a file created by `tempfile`, which is private by
    # default; a regeneration must not quietly narrow the manifest's mode.
    if stat.S_IMODE(existing.stat().st_mode) != 0o644:
        raise AssertionError(
            "replacing an existing manifest changed its permissions to "
            f"{stat.S_IMODE(existing.stat().st_mode):#o}"
        )

    drifted = fixture(parent / "authoring-drifted")
    with (drifted / TARGET).open("ab") as handle:
        handle.write(b"\n-- authoring must never read this\n")
    ignored = spec / "authored-ignoring-candidate.json"
    run(drifted, True, ignored, checker=checker, cwd=repo, env=GIT_ENV, write_manifest=True)
    if json.loads(ignored.read_text(encoding="utf-8"))["files"] != _REVIEWED["files"]:
        raise AssertionError("authoring read the candidate tree instead of Git")


def tracing_controls(parent: Path) -> None:
    """Git's own tracing must not be read as a Git diagnostic.

    The object probe concludes absence from a `missing` reply with nothing on
    stderr, so any `GIT_TRACE*` switch turned on to debug something else would
    otherwise make every genuinely absent object look present-but-unreadable —
    the mirror image of the conflation this checker exists to avoid, and a red
    build for anyone tracing a shell or a runner.  The probe strips those
    variables, and both halves of that are asserted here: a rewritten history
    still verifies and still reports the reviewed commit absent under tracing,
    and a corrupt object in the same repository still fails closed under
    tracing rather than being traded for an absence.
    """
    repo = scaffold(parent / "tracing")
    init_commit(repo, "Squashed rewrite carrying the exact frozen subtree")
    if has_object(repo, FROZEN_COMMIT):
        raise AssertionError("the tracing fixture must not contain the reviewed commit")
    checker = repo / "scripts" / CHECKER.name
    for variable in ("GIT_TRACE", "GIT_TRACE2"):
        output = run(None, True, checker=checker, cwd=repo, env={**GIT_ENV, variable: "1"})
        expect_text(
            output,
            f"reviewed provenance {FROZEN_COMMIT[:12]} absent",
            f"tracing/{variable}",
        )

    corrupt_loose_object(repo, FROZEN_TREE)
    output = run(
        None, False, checker=checker, cwd=repo, env={**GIT_ENV, "GIT_TRACE_SETUP": "1"}
    )
    expect_text(output, "present but unusable, not absent", "tracing/corrupt")
    expect_no_text(output, "absent from this repository", "tracing/corrupt")


def provenance_free_suite_control(parent: Path) -> None:
    """These controls must themselves pass without the reviewed commit.

    A `git clone --depth 1`, a single-branch clone and a squash-rewritten `main`
    all leave the same shape behind: the frozen tree object is present, the
    reviewed commit is not.  The checker is documented to pass there — and this
    suite runs in `scripts/check.sh` before any build, so a suite that needed
    the reviewed commit would turn every such checkout red while the freeze
    itself was perfectly intact.  The fixture is that shape exactly: one
    unrelated commit carrying the frozen bytes, the checker and this suite, with
    the reviewed commit absent from the object store.  Both are run inside it;
    the nested copy is told not to build this same fixture again.
    """
    repo = scaffold(parent / "provenance-free", with_suite=True)
    init_commit(repo, "Squashed rewrite carrying the suite and the frozen subtree")
    if has_object(repo, FROZEN_COMMIT):
        raise AssertionError("the provenance-free fixture must not contain the reviewed commit")
    if git(repo, "cat-file", "-t", FROZEN_TREE) != "tree":
        raise AssertionError("the provenance-free fixture does not carry the frozen tree object")

    output = run(None, True, checker=repo / "scripts" / CHECKER.name, cwd=repo, env=GIT_ENV)
    expect_text(
        output,
        f"reviewed provenance {FROZEN_COMMIT[:12]} absent",
        "provenance-free/checker",
    )

    result = subprocess.run(
        [sys.executable, str(repo / "scripts" / SUITE.name)],
        cwd=repo,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env={**GIT_ENV, NESTED_VARIABLE: "1"},
        check=False,
    )
    if result.returncode != 0:
        raise AssertionError(
            "this suite does not pass in a checkout without the reviewed "
            f"provenance commit\n{result.stdout}"
        )
    expect_text(result.stdout, "[tmverifier-freeze-test] OK", "provenance-free/suite")


def root_authoring_control(parent: Path) -> None:
    """Regeneration at ROOT, in whichever of the two shapes this checkout has.

    That the committed manifest is exactly what this checker would generate is
    re-proved unconditionally by every ordinary run here: `load_manifest` holds
    all four pinned scalars to the checker's own constants and every `files`
    entry to the frozen tree, in any checkout, with provenance or without.
    Authoring on top of that is deliberately stricter than verification, so this
    control asserts whichever half of the authoring contract applies to the
    checkout it finds itself in, and skips neither.  A production checkout
    resolves the reviewed commit, and then regeneration must reproduce the
    reviewed manifest exactly.  A shallow, single-branch or squash-rewritten one
    does not, and then authoring must be refused with its target untouched —
    which is the whole point of the strict guard, asserted rather than assumed.
    Authoring under matching provenance is proved in either shape regardless, by
    the synthetic fixtures in `provenance_controls` and `authoring_controls`.
    """
    generated = parent / "generated-manifest.json"
    if has_object(ROOT, FROZEN_COMMIT):
        run(None, True, generated, write_manifest=True)
        if json.loads(generated.read_text(encoding="utf-8")) != _REVIEWED:
            raise AssertionError("regenerated manifest differs from the reviewed manifest")
        return
    output = run(None, False, generated, write_manifest=True)
    expect_text(output, "refusing to write", "root authoring")
    expect_unwritten(generated, "root authoring")


def version_manifest_row_control() -> None:
    """`spec/version_manifest.toml` must track the freeze manifest's schema.

    `scripts/validate_version_manifest.py` checks only that this row's `target`
    path exists: by that validator's own documented contract the `version` of a
    `target`-only sub-table is declarative, since the referenced file carries no
    `[meta].spec_version`.  The freeze manifest does carry a machine-readable
    `schema_version`, so the real cross-check belongs here, where it keeps the
    advertised row from drifting away from the schema it describes.
    """
    with VERSION_MANIFEST.open("rb") as handle:
        row = tomllib.load(handle).get("snapshot", {}).get("tmverifier_freeze")
    if not isinstance(row, dict):
        raise AssertionError(
            f"{VERSION_MANIFEST} has no [snapshot.tmverifier_freeze] table"
        )
    expected = str(_REVIEWED["schema_version"])
    if row.get("version") != expected:
        raise AssertionError(
            "snapshot.tmverifier_freeze.version is "
            f"{row.get('version')!r}, not {expected!r} from {MANIFEST.name}"
        )
    if row.get("target") != str(MANIFEST.relative_to(ROOT)):
        raise AssertionError(
            f"snapshot.tmverifier_freeze.target is {row.get('target')!r}, "
            f"not {str(MANIFEST.relative_to(ROOT))!r}"
        )


def main() -> None:
    version_manifest_row_control()
    with tempfile.TemporaryDirectory(prefix="tmverifier-freeze-") as tmp:
        parent = Path(tmp)
        baseline = fixture(parent / "baseline")
        # This is the unconditional manifest-versus-Git check: the checker will
        # not load a manifest whose pinned scalars or whose entries disagree
        # with the frozen tree, so a green run here already says the committed
        # manifest is the one this checker generates.
        expect_text(run(baseline, True), f"{len(_REVIEWED['files'])} Git objects", "baseline")
        root_authoring_control(parent)

        exact_manifest = parent / "exact-manifest.json"
        shutil.copy2(MANIFEST, exact_manifest)
        run(baseline, True, exact_manifest)

        tampered_commit = parent / "tampered-commit.json"
        data = json.loads(MANIFEST.read_text())
        data["frozen_commit"] = "0" * 40
        tampered_commit.write_text(json.dumps(data))
        run(baseline, False, tampered_commit)

        tampered_tree = parent / "tampered-tree.json"
        data = json.loads(MANIFEST.read_text())
        data["frozen_tree"] = "0" * 40
        tampered_tree.write_text(json.dumps(data))
        run(baseline, False, tampered_tree)

        stale_schema = parent / "stale-schema.json"
        data = json.loads(MANIFEST.read_text())
        data["schema_version"] -= 1
        del data["frozen_tree"]
        stale_schema.write_text(json.dumps(data))
        run(baseline, False, stale_schema)

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

        rewritten_history_controls(parent)
        provenance_controls(parent)
        object_state_controls(parent)
        no_object_store_control(parent)
        authoring_controls(parent)
        tracing_controls(parent)
        if not nested():
            provenance_free_suite_control(parent)

    if nested():
        tail = "1 root-authoring controls, inside the caller's provenance-free fixture"
    else:
        tail = "1 root-authoring, 1 provenance-free self-hosted controls"
    print(
        "[tmverifier-freeze-test] OK: manifest trust + schema row, 4 manifest, "
        "5 filesystem, 4 rewritten-history, 8 provenance, 5 object-state, "
        f"1 no-object-store, 5 authoring, 3 tracing, {tail}"
    )


if __name__ == "__main__":
    main()
