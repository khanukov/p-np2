#!/usr/bin/env python3
"""Negative controls for the TMVerifier freeze checker.

Besides the manifest-trust and filesystem controls, this exercises the two
properties the tree pin buys: the checker must still verify content in a
rewritten history where the reviewed provenance commit does not exist, and it
must fail closed whenever provenance *is* available but disagrees with the pin.
Both are run end to end against the real checker source in real synthetic Git
repositories, never against a stand-in.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TREE = "pnp3/Complexity/TMVerifier"
SOURCE = ROOT / TREE
CHECKER = ROOT / "scripts/check_tmverifier_freeze.py"
MANIFEST = ROOT / "spec/tmverifier_freeze.json"
TARGET = Path("pnp3/Complexity/TMVerifier/TuringToolkit/GateNBodyRound.lean")

_REVIEWED = json.loads(MANIFEST.read_text(encoding="utf-8"))
FROZEN_COMMIT = _REVIEWED["frozen_commit"]
FROZEN_TREE = _REVIEWED["frozen_tree"]

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
) -> str:
    command = [str(checker)]
    if candidate is not None:
        command.extend(["--candidate-root", str(candidate)])
    if manifest is not None:
        command.extend(["--manifest", str(manifest)])
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


def fixture(parent: Path) -> Path:
    root = parent / "candidate"
    shutil.copytree(SOURCE, root / SOURCE.relative_to(ROOT), symlinks=True)
    return root


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], env=GIT_ENV, text=True
    ).strip()


def has_object(repo: Path, spec: str) -> bool:
    return (
        subprocess.run(
            ["git", "-C", str(repo), "cat-file", "-e", spec],
            env=GIT_ENV,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        ).returncode
        == 0
    )


def scaffold(root: Path) -> Path:
    """Lay out a standalone repository root holding the frozen subtree.

    The checker resolves its own repository from `__file__`, so placing a copy
    under `scripts/` is what makes the synthetic repository the one it inspects.
    """
    shutil.copytree(SOURCE, root / TREE, symlinks=True)
    (root / "scripts").mkdir(parents=True, exist_ok=True)
    (root / "spec").mkdir(parents=True, exist_ok=True)
    shutil.copy2(CHECKER, root / "scripts" / CHECKER.name)
    shutil.copy2(MANIFEST, root / "spec" / MANIFEST.name)
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
    output = run(
        None,
        True,
        checker=rewritten / "scripts" / CHECKER.name,
        cwd=rewritten,
        env=GIT_ENV,
    )
    expect_text(output, "absent from this history", "rewritten history")
    expect_text(output, f"{len(_REVIEWED['files'])} Git objects", "rewritten history")

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
    the copy repinned onto the matching commit must pass, which is what shows
    the failures come from the provenance cross-check and nothing else.
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
        ("matching", good, True, "reviewed provenance"),
        ("divergent", divergent, False, "not the frozen tree"),
        ("missing-subtree", bare, False, "records no"),
        ("not-a-commit", FROZEN_TREE, False, "not a commit"),
    )
    for label, commit, expect_ok, needle in cases:
        checker = checker_variant(scripts / f"check-{label}.py", FROZEN_COMMIT=commit)
        manifest = repinned_manifest(repo / "spec" / f"manifest-{label}.json", commit)
        output = run(repo, expect_ok, manifest, checker=checker, cwd=repo, env=GIT_ENV)
        expect_text(output, needle, f"provenance/{label}")


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
        if json.loads(generated_manifest.read_text()) != _REVIEWED:
            raise AssertionError("regenerated manifest differs from the reviewed manifest")

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

    print(
        "[tmverifier-freeze-test] OK: manifest trust + 4 manifest, 5 filesystem, "
        "2 rewritten-history, 4 provenance controls"
    )


if __name__ == "__main__":
    main()
