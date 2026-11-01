"""Pure head checks and finite text-evidence staging; no process/network API."""
import hashlib
import json
import os
from pathlib import Path
import re

PHASES = ("bootstrap", "foundations", "build", "consumers")
COMMANDS = {
    "locked-dependency-materialization",
    "checked-feature-head", "elan-installer-help", "elan-install", "lean-toolchain-install",
    "lean-version", "source-identity", "external-foundation-cache", "project-source-build",
    "fresh-public-root-audit", "public-unit-tests", "post-build-source-identity", "source-archive",
    "unpacked-source-identity", "new-external-rejection-attempt", "native-exact-R-rejections",
} | {"dependency-" + name for name in ("mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets", "aesop", "Qq", "batteries", "Cli")}
TOP = {"LAYOUT.json", "BOOTSTRAP.json", "FOUNDATIONS.json", "OWNED_OBJECTS.source-build.json",
       "CORE_CACHE.before-consumers.json", "CORE_CACHE.after-consumers.json", "CONSUMERS.json", "HEAD_IDENTITY.json"}
RECORDS = {"launch.json", "process.json", "terminal.json", "stdout.txt", "stderr.txt"}
BLOCKED = {".git", "packages", "elan", "toolchains", "bin", "cache", "__pycache__"}
MAX_OMISSIONS = 64


def require(value, message):
    if not value:
        raise ValueError(message)


def resolve_head(event_name, event, event_sha, actual_head, ref):
    require(event_name in {"pull_request", "push", "workflow_dispatch"}, "unprivileged event required")
    if event_name == "pull_request":
        expected = event.get("pull_request", {}).get("head", {}).get("sha")
    else:
        require(ref.startswith("refs/heads/") and ref not in {"refs/heads/main", "refs/heads/master"}, "non-main feature branch required")
        expected = event_sha
    for value in (expected, event_sha, actual_head):
        require(isinstance(value, str) and re.fullmatch("[0-9a-f]{40}", value) and value != "0" * 40, "literal nonzero commit SHA required")
    require(actual_head == expected, "checked-out HEAD is not exact relevant head")
    return {"event": event_name, "event_sha": event_sha, "tested_head": actual_head,
            "event_sha_is_tested_head": event_sha == actual_head,
            "scope": "PR head only, not synthetic merge" if event_name == "pull_request" else "exact feature event head"}


def phase_states(work):
    result = {}
    for phase in PHASES:
        path = Path(work) / (phase + ".COMPLETE.json")
        present = path.is_file() and not path.is_symlink()
        if present:
            try:
                value = json.loads(path.read_bytes())
                present = value.get("phase") == phase and isinstance(value.get("end"), str)
            except (ValueError, OSError, AttributeError):
                present = False
        result[phase] = "COMPLETE_MARKER_PRESENT_NOT_EXECUTOR_TERMINAL" if present else "UNKNOWN_NO_COMPLETE_MARKER"
    return result


def metadata_name(name):
    return (name in RECORDS | {"STATUS.json", "RESULT.json", "NATIVE_CHECKER_RESULTS.json"}
            or name.endswith((".source.lean.txt", ".lean.txt", ".setup.json", ".inputs.json", ".parts.json", ".imports.json", ".imports.request.json")))


def stage_evidence(work, package, output, identity, *, max_file_bytes=8*1024**2, max_total_bytes=64*1024**2, max_files=4096):
    require(all(type(n) is int and n > 0 for n in (max_file_bytes, max_total_bytes, max_files)),
            "positive integer evidence limits required (booleans rejected)")
    work, package, output = Path(work), Path(package), Path(output)
    require(not output.exists() and not output.is_symlink(), "fresh staging destination required")
    require(not work.is_symlink() and not package.is_symlink(), "real producer roots required")
    output.mkdir(parents=True)
    files, omissions = [], []
    total = 0
    omission_count = 0

    def omit(name, reason):
        nonlocal omission_count
        omission_count += 1
        if len(omissions) < MAX_OMISSIONS:
            omissions.append({"path": name[:2048], "reason": reason})

    def capture(path, base, name):
        nonlocal total
        if not path.exists() and not path.is_symlink():
            return
        if len(name.encode("utf-8")) > 2048:
            omit(name, "evidence relative name exceeds byte limit")
            return
        relative = path.relative_to(base)
        chain = [base] + [base.joinpath(*relative.parts[:i]) for i in range(1, len(relative.parts) + 1)]
        if any(p.is_symlink() for p in chain) or not path.is_file() or path.stat().st_nlink != 1:
            omit(name, "nonregular/symlink/hardlink")
            return
        size = path.stat().st_size
        if size > max_file_bytes or total + size > max_total_bytes or len(files) >= max_files:
            omit(name, "explicit evidence budget exceeded")
            return
        data = path.read_bytes()
        try:
            data.decode("utf-8")
        except UnicodeError:
            omit(name, "not UTF8 text evidence")
            return
        require(len(data) == size, "evidence changed while read")
        target = output / name
        require(not Path(name).is_absolute() and ".." not in Path(name).parts, "staged relative name")
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(data)
        files.append({"path": name, "bytes": size, "sha256": hashlib.sha256(data).hexdigest()})
        total += size

    for name in sorted(TOP | {phase + ".COMPLETE.json" for phase in PHASES}):
        capture(work / name, work, "producer/" + name)
    command_states = {}
    for label in sorted(COMMANDS):
        root = work / label
        if not root.exists() and not root.is_symlink():
            continue
        if root.is_symlink():
            omit("commands/" + label, "symlink command directory")
            continue
        for name in sorted(RECORDS):
            capture(root / name, work, "commands/" + label + "/" + name)
        terminal_name = "commands/" + label + "/terminal.json"
        terminal_staged = any(row["path"] == terminal_name for row in files)
        if not terminal_staged:
            omit(terminal_name, "executor terminal not staged: UNKNOWN")
        command_states[label] = ("TERMINAL_PRESENT_UNINTERPRETED" if terminal_staged
                                 else "STARTED_NO_TERMINAL_UNKNOWN")
    for owner in ("native-rejection-attempt", "conditional-surface-consumer"):
        for subtree in ("conditional-check", "rejection-suite", "native-conditional-consumer"):
            base = work / owner / ".lake" / subtree
            if not base.exists():
                continue
            # Check every explicit ancestor before any traversal.
            if any(p.is_symlink() for p in (work / owner, work / owner / ".lake", base)):
                omit(owner + "/" + subtree, "symlink receipt root")
                continue
            for parent, dirs, names in os.walk(base, followlinks=False):
                retained = []
                for directory in dirs:
                    path = Path(parent) / directory
                    if path.is_symlink():
                        omit(owner + "/" + subtree + "/" + directory, "symlink receipt directory")
                    elif directory not in BLOCKED and not directory.startswith("."):
                        retained.append(directory)
                dirs[:] = retained
                for name in names:
                    if metadata_name(name):
                        path = Path(parent) / name
                        destination = "attempts/" + owner + "/" + subtree + "/" + path.relative_to(base).as_posix()
                        capture(path, base, destination)
    for name in ("PACKAGE_FILES.json", "PROVENANCE.json", "lean-toolchain", "lake-manifest.json"):
        capture(package / name, package, "source-pins/" + name)
    if not (package / "PACKAGE_FILES.json").is_file():
        omit("source-pins/PACKAGE_FILES.json", "source inventory absent")
    for relative in ("ci/package_source_v1.py", "ci/native_ci_v1.py", "ci/portable_ci_data_v1.py", "ci/ci_evidence_data_v2.py",
                     "ci/export_ci_evidence_v2.py", "ConditionalSeparation/OpenProblem.lean", "ConditionalSeparation/Conditional.lean"):
        capture(package / relative, package, "control-sources/" + relative)
    result = {"schema": "bounded-native-ci-evidence-v2", "identity": identity,
              "files": files, "payload_bytes": total, "omissions": omissions,
              "omission_count": omission_count, "omission_sample_truncated": omission_count > len(omissions),
              "export_complete": omission_count == 0, "phase_states": phase_states(work), "command_states": command_states,
              "native_validation_pass": False, "R_proved": False,
              "limits": {"file_bytes": max_file_bytes, "payload_bytes": max_total_bytes, "files": max_files},
              "meaning": "Evidence export only. Missing executor/aggregate terminals remain UNKNOWN; complete markers are producer statements, not fabricated OS exits."}
    with (output / "EVIDENCE_MANIFEST.json").open("x", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    return result
