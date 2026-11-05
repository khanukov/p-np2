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
    controller = event_sha if event_name == "push" else None
    dispatch_source = False
    if event_name == "pull_request":
        expected = event.get("pull_request", {}).get("head", {}).get("sha")
    else:
        require(ref.startswith("refs/heads/") and ref not in {"refs/heads/main", "refs/heads/master"}, "non-main feature branch required")
        expected = event_sha
        if event_name == "workflow_dispatch" and event.get("inputs"):
            inputs = event["inputs"]
            require(type(inputs) is dict and set(inputs) == {"controller_sha", "source_sha"}, "dispatch input domain")
            require(inputs["controller_sha"] == event_sha, "dispatch controller differs from actual workflow revision")
            controller, expected = event_sha, inputs["source_sha"]
            dispatch_source = True
    for value in (expected, event_sha, actual_head):
        require(isinstance(value, str) and re.fullmatch("[0-9a-f]{40}", value) and value != "0" * 40, "literal nonzero commit SHA required")
    require(actual_head == expected, "checked-out HEAD is not exact relevant head")
    return {"event": event_name, "event_sha": event_sha, "tested_head": actual_head,
            "event_sha_is_tested_head": event_sha == actual_head,
            "controller_input_sha": controller,
            "scope": ("PR head only, not synthetic merge" if event_name == "pull_request" else
                      "exact dispatch source; parent must join to current PR head" if dispatch_source else "exact feature event head")}


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


def _utf8_chunks(data, limit, slots):
    """Lossless UTF8-aligned pieces; no partial export or unbounded fragment list."""
    require(type(data) is bytes and type(limit) is int and limit > 0, "fragment bytes/limit")
    require(type(slots) is int and slots > 0, "fragment slots")
    data.decode("utf-8")
    parts, start = [], 0
    while start < len(data):
        require(len(parts) < slots, "fragment file budget exceeded")
        end = min(start + limit, len(data))
        while end < len(data) and end > start and data[end] & 0xc0 == 0x80:
            end -= 1
        require(end > start, "UTF8 codepoint exceeds fragment limit")
        parts.append(data[start:end])
        start = end
    return parts


def reconstruct_text_export(output, manifest, original):
    """Read-only independent reconstruction; payload row limits exclude the one outer
    EVIDENCE_MANIFEST.json descriptor; hard physical limits include it.
    No extra per-stream descriptor files are created or hidden from file counts.
    """
    root = Path(output)
    require(root.is_absolute() and root.resolve() == root and not root.is_symlink(), "real evidence root")
    require(isinstance(manifest, dict) and manifest.get("schema") == "bounded-native-ci-evidence-v2", "evidence schema")
    limits = manifest["limits"]
    require(isinstance(limits, dict), "limits object")
    require(set(limits) == {"file_bytes", "payload_bytes", "files"}, "evidence limits schema")
    for key, ceiling in (("file_bytes", 8*1024**2), ("payload_bytes", 64*1024**2), ("files", 4096)):
        require(type(limits[key]) is int and 0 < limits[key] <= ceiling, "bounded nonboolean limits")
    require(isinstance(manifest["files"], list) and len(manifest["files"]) <= limits["files"], "payload file count")

    def relative(name):
        require(isinstance(name, str) and name and "\\" not in name and ":" not in name, "evidence relative path")
        path = Path(name)
        require(path.parts and not path.is_absolute() and path.as_posix() == name and ".." not in path.parts
                and len(name.encode("utf-8")) <= 2048, "canonical evidence name")
        return path

    pins, payloads, budget = {}, {}, 0
    for row in manifest["files"]:
        require(isinstance(row, dict) and set(row) == {"path", "bytes", "sha256"}, "payload pin schema")
        name = row["path"]; rel = relative(name)
        require(name != "EVIDENCE_MANIFEST.json", "descriptor is not payload")
        require(name not in pins and type(row["bytes"]) is int and 0 <= row["bytes"] <= limits["file_bytes"], "payload duplicate/size")
        require(isinstance(row["sha256"], str) and re.fullmatch("[0-9a-f]{64}", row["sha256"]), "payload digest")
        budget += row["bytes"]
        require(budget <= limits["payload_bytes"], "bounded payload total before reading")
        path = root / rel
        chain = [root] + [root.joinpath(*rel.parts[:i]) for i in range(1, len(rel.parts)+1)]
        require(not any(p.is_symlink() or getattr(p, "is_junction", lambda: False)() for p in chain)
                and path.is_file() and path.stat().st_nlink == 1, "regular unaliased evidence")
        require(path.stat().st_size == row["bytes"], "payload actual size")
        data = path.read_bytes(); data.decode("utf-8")
        require(len(data) == row["bytes"] and hashlib.sha256(data).hexdigest() == row["sha256"], "payload changed/hash")
        pins[name] = row; payloads[name] = data
    require(type(manifest["payload_bytes"]) is int and manifest["payload_bytes"] == sum(r["bytes"] for r in pins.values())
            and manifest["payload_bytes"] <= limits["payload_bytes"], "payload total")
    actual = set()
    for parent, dirs, names in os.walk(root, followlinks=False):
        require(not any((Path(parent)/d).is_symlink() for d in dirs), "evidence directory alias")
        for name in names:
            p = Path(parent)/name
            require(p.is_file() and not p.is_symlink() and p.stat().st_nlink == 1, "evidence file type")
            actual.add(p.relative_to(root).as_posix())
    require(actual == set(pins) | {"EVIDENCE_MANIFEST.json"}, "complete evidence filename SET")
    descriptor = root / "EVIDENCE_MANIFEST.json"
    require(descriptor.stat().st_size <= 8*1024**2 and len(pins)+1 <= 4096
            and manifest["payload_bytes"]+descriptor.stat().st_size <= 64*1024**2, "physical export limits")
    descriptor.read_bytes().decode("utf-8")
    if manifest.get("fragmented_text"):
        physical = manifest.get("physical_export")
        expected = {"files": len(pins)+1, "manifest_bytes": descriptor.stat().st_size,
                    "total_bytes": manifest["payload_bytes"]+descriptor.stat().st_size}
        require(isinstance(physical, dict) and set(physical) == set(expected)
                and all(type(physical[k]) is int for k in expected) and physical == expected, "physical export accounting")
    streams, used = {}, set()
    records = manifest.get("fragmented_text", [])
    require(isinstance(records, list), "fragment record list")
    for record in records:
        require(isinstance(record, dict) and set(record) == {"path", "bytes", "sha256", "parts"}, "fragment record schema")
        name = record["path"]; relative(name)
        require(name in {"commands/"+label+"/stdout.txt" for label in COMMANDS}
                and name not in pins and name not in streams, "fragment original identity")
        require(type(record["bytes"]) is int and limits["file_bytes"] < record["bytes"] <= limits["payload_bytes"], "fragment original size")
        require(isinstance(record["sha256"], str) and re.fullmatch("[0-9a-f]{64}", record["sha256"]), "fragment original digest")
        parts = record["parts"]
        require(isinstance(parts, list) and 2 <= len(parts) <= limits["files"]
                and parts == [name+".parts/"+f"{i:08d}.txt" for i in range(len(parts))], "fragment order/names")
        require(all(p in pins and p not in used for p in parts), "missing/reused fragment")
        used.update(parts)
        data = b"".join(payloads[p] for p in parts)
        require(len(data) == record["bytes"] and hashlib.sha256(data).hexdigest() == record["sha256"], "complete original length/hash")
        streams[name] = data
    expected_parts = {n for n in pins if re.match(r"commands/[^/]+/stdout\.txt\.parts/", n)}
    require(used == expected_parts, "unreferenced/extra fragment")
    relative(original)
    require(original in streams or original in payloads, "requested text absent")
    return streams.get(original, payloads.get(original))


def _evidence_descriptor(result):
    """Payload rows retain their limits; the one descriptor also counts against
    the absolute 8MiB/file, 64MiB/export and 4096-file export ceilings.
    """
    require(type(result["payload_bytes"]) is int and result["payload_bytes"] >= 0, "descriptor payload size")
    require(len(result["files"]) + 1 <= 4096, "physical evidence file count exceeded")
    if result.get("fragmented_text"):
        result["physical_export"] = {"files": len(result["files"])+1, "manifest_bytes": 0, "total_bytes": 0}
    for _ in range(8):
        data = (json.dumps(result, indent=2, sort_keys=True) + "\n").encode("utf-8")
        require(len(data) <= 8*1024**2, "evidence manifest descriptor exceeds 8MiB")
        physical = {"files": len(result["files"])+1, "manifest_bytes": len(data),
                    "total_bytes": result["payload_bytes"]+len(data)}
        require(physical["total_bytes"] <= 64*1024**2, "physical evidence total exceeded")
        if "physical_export" not in result or result["physical_export"] == physical:
            return data
        result["physical_export"] = physical
    raise ValueError("descriptor byte accounting did not stabilize")


def stage_evidence(work, package, output, identity, *, max_file_bytes=8*1024**2, max_total_bytes=64*1024**2, max_files=4096):
    require(all(type(n) is int and n > 0 for n in (max_file_bytes, max_total_bytes, max_files)),
            "positive integer evidence limits required (booleans rejected)")
    require(max_file_bytes <= 8*1024**2 and max_total_bytes <= 64*1024**2 and max_files <= 4096,
            "evidence payload ceilings cannot be raised")
    work, package, output = Path(work), Path(package), Path(output)
    require(not output.exists() and not output.is_symlink(), "fresh staging destination required")
    require(not work.is_symlink() and not package.is_symlink(), "real producer roots required")
    output.mkdir(parents=True)
    files, omissions = [], []
    fragmented = []
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
        before = path.stat()
        size = before.st_size
        chunkable = name in {"commands/" + label + "/stdout.txt" for label in COMMANDS}
        if (size > max_file_bytes and not chunkable) or total + size > max_total_bytes or len(files) >= max_files:
            omit(name, "explicit evidence budget exceeded")
            return
        data = path.read_bytes()
        try:
            data.decode("utf-8")
        except UnicodeError:
            omit(name, "not UTF8 text evidence")
            return
        after = path.stat()
        fields = ("st_dev", "st_ino", "st_mode", "st_nlink", "st_size", "st_mtime_ns", "st_ctime_ns")
        require(len(data) == size and all(getattr(before, k) == getattr(after, k) for k in fields)
                and not any(p.is_symlink() for p in chain), "evidence changed while read")
        if size > max_file_bytes:
            try:
                chunks = _utf8_chunks(data, max_file_bytes, max_files - len(files))
            except ValueError:
                omit(name, "explicit evidence budget exceeded")
                return
            names = [name + ".parts/" + f"{i:08d}.txt" for i in range(len(chunks))]
        else:
            chunks, names = [data], [name]
        for fragment_name, chunk in zip(names, chunks):
            target = output / fragment_name
            require(not Path(fragment_name).is_absolute() and ".." not in Path(fragment_name).parts, "staged relative name")
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open("xb") as stream:
                stream.write(chunk)
            files.append({"path": fragment_name, "bytes": len(chunk), "sha256": hashlib.sha256(chunk).hexdigest()})
            total += len(chunk)
        if size > max_file_bytes:
            fragmented.append({"path": name, "bytes": size, "sha256": hashlib.sha256(data).hexdigest(), "parts": names})

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
                     "ci/export_ci_evidence_v2.py", "ci/trusted_controls_v1.py", "ci/TRUSTED_NATIVE_CONTROLS_V1.json",
                     "ConditionalSeparation/OpenProblem.lean", "ConditionalSeparation/Conditional.lean"):
        capture(package / relative, package, "control-sources/" + relative)
    result = {"schema": "bounded-native-ci-evidence-v2", "identity": identity,
              "files": files, "payload_bytes": total, "omissions": omissions,
              "omission_count": omission_count, "omission_sample_truncated": omission_count > len(omissions),
              "export_complete": omission_count == 0, "phase_states": phase_states(work), "command_states": command_states,
              "native_validation_pass": False, "R_proved": False,
              "limits": {"file_bytes": max_file_bytes, "payload_bytes": max_total_bytes, "files": max_files},
              "meaning": "Evidence export only. Missing executor/aggregate terminals remain UNKNOWN; complete markers are producer statements, not fabricated OS exits."}
    if fragmented:
        result["fragmented_text"] = fragmented
    # Fragment metadata is embedded in the one outer descriptor, not extra files.
    descriptor = _evidence_descriptor(result)
    with (output / "EVIDENCE_MANIFEST.json").open("xb") as stream:
        stream.write(descriptor)
    return result
