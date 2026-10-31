"""PROSPECTIVE v2 tuple; stable v1 module API name, never executed locally.

Requires future exact-byte review/integration and native workflow execution.
No hidden monorepo inputs; only shipped source and its declared dependencies.
"""
import sys
if sys.flags.optimize:
    raise SystemExit("optimized native CI control rejected")
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import urllib.request
from portable_ci_data_v1 import (TOOLCHAIN, asset_for, consumer_source, install_commands,
                                  load_assets, require, unpack_installer, unpack_source,
                                  validate_lock, validate_runner)
from ci_evidence_data_v2 import resolve_head

PACKAGE = Path(__file__).resolve().parents[1]
WORK = None


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save(path, value):
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def reserve():
    free = shutil.disk_usage(WORK).free
    require(free >= 5 * 1024**3, "less than 5 GiB reserve; no cleanup or fallback")
    return free


def command(label, argv, cwd):
    """Future native execution only; complete waited receipts, no module timeout."""
    reserve()
    root = WORK / label
    root.mkdir()
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN", "PYTHONOPTIMIZE"):
        env.pop(key, None)
    env.update(PYTHONDONTWRITEBYTECODE="1", LEAN_NUM_THREADS="2")
    start = utc()
    save(root / "launch.json", {"argv": argv, "cwd": str(cwd), "start": start,
                                "LEAN_NUM_THREADS": "2", "arbitrary_module_timeout": None})
    options = {"start_new_session": True} if os.name != "nt" else {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP}
    with (root / "stdout.txt").open("xb") as out, (root / "stderr.txt").open("xb") as err:
        child = subprocess.Popen(argv, cwd=cwd, env=env, stdout=out, stderr=err, **options)
        try:
            try:
                pgid = os.getpgid(child.pid) if os.name != "nt" else None
            except ProcessLookupError:
                pgid = None
            save(root / "process.json", {"pid": child.pid, "pgid": pgid, "observed": utc()})
            rc = child.wait()
        except BaseException as original:
            try:
                if child.poll() is None:
                    if os.name != "nt":
                        try:
                            os.killpg(child.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                    else:
                        child.terminate()
                child.wait()
            except BaseException as cleanup:
                if hasattr(original, "add_note"):
                    original.add_note("cleanup also failed: " + repr(cleanup))
            raise
    save(root / "terminal.json", {"start": start, "end": utc(), "OS_exit": rc,
                                  "stdout_sha256": digest(root / "stdout.txt"), "stderr_sha256": digest(root / "stderr.txt")})
    print(json.dumps({"command": label, "OS_exit": rc, "receipt": str(root)}), flush=True)
    if rc:
        for name in ("stdout.txt", "stderr.txt"):
            print((root / name).read_text(encoding="utf-8", errors="replace")[-8192:], file=sys.stderr)
        raise RuntimeError("native command failed: " + label)
    return (root / "stdout.txt").read_text(encoding="utf-8", errors="strict")


def own_objects():
    root = PACKAGE / ".lake/build/lib/lean"
    return {p.relative_to(root).as_posix(): {"bytes": p.stat().st_size, "sha256": digest(p)}
            for p in sorted(root.rglob("*")) if p.is_file() and
            (p.name.endswith(".olean") or p.name.endswith(".olean.server") or p.name.endswith(".olean.private"))}


def exact_source():
    require((PACKAGE / "lean-toolchain").read_text().strip() == TOOLCHAIN, "exact source toolchain")
    return validate_lock((PACKAGE / "lake-manifest.json").read_bytes())


def bootstrap():
    require(not (PACKAGE / ".lake").exists(), "fresh checkout must contain zero project/dependency build inputs")
    rows = exact_source()
    actual_head = command("checked-feature-head", ["git", "rev-parse", "HEAD"], PACKAGE.parent).strip()
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_bytes())
    identity = resolve_head(os.environ["GITHUB_EVENT_NAME"], event, os.environ["GITHUB_SHA"],
                            actual_head, os.environ["GITHUB_REF"])
    require(identity["tested_head"] == os.environ["CI_EXPECTED_HEAD"], "workflow/head admission disagreement")
    identity["workflow_definition_ref"] = os.environ.get("GITHUB_WORKFLOW_REF")
    identity["workflow_definition_sha"] = os.environ.get("GITHUB_WORKFLOW_SHA")
    identity["package_source_inventory_sha256"] = digest(PACKAGE / "PACKAGE_FILES.json")
    save(WORK / "HEAD_IDENTITY.json", identity)
    system, machine = platform.system(), platform.machine()
    validate_runner(os.environ["CI_RUNNER_LABEL"], system, machine, os.environ["CI_PYTHON_ARCH"])
    require(sys.maxsize > 2**32, "native 64-bit Python required")
    row = asset_for(load_assets(PACKAGE / "ci/elan-v4.2.4.json"), system, machine)
    reserve()
    with urllib.request.urlopen(row["browser_download_url"], timeout=90) as response:
        require(response.status == 200, "official asset HTTP status")
        data = response.read(row["size"] + 1)
    # Digest and member validation precede extraction or installer execution.
    installer = unpack_installer(data, row, WORK / "verified-elan-installer")
    (WORK / row["name"]).write_bytes(data)
    if os.name != "nt":
        installer.chmod(0o700)  # Future runner-private file only, never a host source/cache.
    home = WORK / "elan"
    os.environ["ELAN_HOME"] = str(home)
    plan = install_commands(installer, home, system)
    help_text = command("elan-installer-help", plan[0], PACKAGE)
    require(all(flag in help_text for flag in ("--no-modify-path", "--default-toolchain")), "installer CLI does not match reviewed recipe")
    command("elan-install", plan[1], PACKAGE)
    command("lean-toolchain-install", plan[2], PACKAGE)
    with Path(os.environ["GITHUB_PATH"]).open("a", encoding="utf-8") as stream:
        stream.write(str(home / "bin") + "\n")
    with Path(os.environ["GITHUB_ENV"]).open("a", encoding="utf-8") as stream:
        stream.write("ELAN_HOME=" + str(home) + "\n")
    save(WORK / "BOOTSTRAP.json", {"native_system": system, "native_machine": machine,
                                   "runner": os.environ["CI_RUNNER_LABEL"], "python": sys.version,
                                   "cpu_count": os.cpu_count(), "disk_free": reserve(), "toolchain": TOOLCHAIN,
                                   "elan_asset": row, "locked_dependency_count": len(rows),
                                   "lean_archive_digest_scope": "Elan installs the exact named toolchain; this helper does not attest its downloaded archive digest against the separate release metadata."})


def foundations():
    rows = exact_source()
    version = command("lean-version", ["lake", "env", "lean", "--version"], PACKAGE)
    require("version 4.22.0-rc2" in version, "actual Lean version differs")
    require(not own_objects(), "no project object admitted before source build")
    command("source-identity", [sys.executable, "-B", "tools/workbench.py", "verify-core", "--core", str(PACKAGE)], PACKAGE)
    for row in rows:
        directory = PACKAGE / ".lake/packages" / row["name"]
        require(directory.is_dir() and not directory.is_symlink(), "fresh declared external dependency directory")
        head = command("dependency-" + row["name"], ["git", "rev-parse", "HEAD"], directory).strip()
        require(head == row["rev"], "declared external dependency commit mismatch")
    mathlib = PACKAGE / ".lake/packages/mathlib"
    # Runs in the EXTERNAL Mathlib workspace, not the project. No actions/cache,
    # no project output download, no previous project build/cache admission.
    command("external-foundation-cache", ["lake", "exe", "cache", "get"], mathlib)
    require(not own_objects(), "foundation retrieval introduced project objects")
    exact_source()
    save(WORK / "FOUNDATIONS.json", {"role": "REUSED_EXTERNAL_FOUNDATIONAL_OBJECTS_ONLY",
                                    "project_objects_before_source_build": 0,
                                    "dependency_lock_sha256": digest(PACKAGE / "lake-manifest.json")})


def build():
    exact_source()
    require(not own_objects(), "project cache would mask fresh source compilation")
    command("project-source-build", ["lake", "build", "ProofCore", "ConditionalSeparation"], PACKAGE)
    objects = own_objects()
    require(objects, "source build emitted no owned objects")
    provenance = json.loads((PACKAGE / "PROVENANCE.json").read_bytes())
    for row in provenance["modules"]:
        require(row["module"].replace(".", "/") + ".olean" in objects, "copied core module absent from source build")
    save(WORK / "OWNED_OBJECTS.source-build.json", {"role": "FRESH_NATIVE_PROJECT_SOURCE_BUILD", "objects": objects})
    command("fresh-public-root-audit", ["lake", "env", "lean", "-DwarningAsError=true", "ConditionalSeparation/KernelAudit.lean"], PACKAGE)
    command("public-unit-tests", [sys.executable, "-B", "ci/run_data_tests_v2.py", "--data-root", str(WORK / "public-unit-data")], PACKAGE)
    command("post-build-source-identity", [sys.executable, "-B", "tools/workbench.py", "verify-core", "--core", str(PACKAGE)], PACKAGE)


def external_consumers():
    # This exercises a fresh independent ATTEMPT outside the checkout against
    # the exact freshly built installed core. It is not a second cold core replay.
    before = own_objects()
    save(WORK / "CORE_CACHE.before-consumers.json", before)
    archive = WORK / "source-package.zip"
    command("source-archive", [sys.executable, "-B", "tools/workbench.py", "archive", "--core", str(PACKAGE), "--output", str(archive)], PACKAGE)
    copied = unpack_source(archive.read_bytes(), WORK / "unpacked-source-only")
    command("unpacked-source-identity", [sys.executable, "-B", str(copied / "tools/workbench.py"), "verify-core", "--core", str(copied)], copied)
    attempt = WORK / "native-rejection-attempt"
    command("new-external-rejection-attempt", [sys.executable, "-B", "tools/workbench.py", "new", str(attempt), "--core", str(PACKAGE)], PACKAGE)
    command("native-exact-R-rejections", [sys.executable, "-B", "tests/lean_rejections.py", "--attempt", str(attempt)], PACKAGE)
    # Use the read, existing Python workbench API, never an imagined install API.
    spec = importlib.util.spec_from_file_location("installed_workbench", PACKAGE / "tools/workbench.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    consumer = module.create(WORK / "conditional-surface-consumer", PACKAGE)
    template = (consumer / "Attempt.lean").read_bytes()
    (consumer / "partial-template.lean.txt").write_bytes(template)
    (consumer / "Attempt.lean").write_text(consumer_source(), encoding="utf-8")
    # Independent full-proposition mirrors are conditional, NEVER a proof of R.
    # Full proposition elaboration is internal conditional validation only here.
    proposition = """ConditionalSeparation.OpenProblem.R → ∃ k : Nat,
  UniformClassBridgeClosure.Ordinary.UniformNP
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  ¬ Pnp3.ComplexityInterfaces.PpolyDAG
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  ¬ UniformClassBridgeClosure.Ordinary.UniformP
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)))"""
    root = consumer / ".lake/native-conditional-consumer"
    root.mkdir(parents=True)
    parts = module.compile_source(consumer, root, "fresh-surface", consumer / "Attempt.lean", "Attempt", {})
    names = ["Attempt.conditional_surface", "Attempt.check_conditional_surface"]
    audit = root / "Consumer.lean"
    audit.write_text("import ConditionalSeparation.Conditional\nimport Attempt\nimport Lean\n"
                     "open Pnp4.Frontier Pnp4.Frontier.ContractExpansion\n"
                     + "".join(module.guard_body(name, proposition) for name in names), encoding="utf-8")
    module.compile_source(consumer, root, "full-conditional-guards", audit, "Consumer", {"Attempt": parts})
    import re
    raw = (root / "full-conditional-guards-compile/stdout.txt").read_text(encoding="utf-8")
    require(re.findall(r"\[CS_ROOT\] ([^\s]+)", raw) == names, "exact conditional consumer direct-root multiset")
    require(set(re.findall(r"\[CS_AXIOM\] ([^\s]+)", raw)) <= {"propext", "Classical.choice", "Quot.sound"}, "conditional consumer axiom set")
    after = own_objects()
    require(before == after, "installed owned core cache changed during fresh attempt validation")
    save(WORK / "CORE_CACHE.after-consumers.json", after)
    save(WORK / "CONSUMERS.json", {"conditional_surface_roots": names, "conditional_generic_receipts": str(root), "R_proved": False,
                                  "core_cache_identical": True, "unpacked_archive_source_identity_checked": True,
                                  "unpacked_core_cold_build_executed": False,
                                  "external_attempt_source_fresh": True})


def main():
    global WORK
    require(os.environ.get("GITHUB_ACTIONS") == "true" and os.environ.get("CI") == "true", "future native Actions context required; not a local operational launcher")
    require(len(sys.argv) == 2 and sys.argv[1] in {"bootstrap", "foundations", "build", "consumers"}, "explicit reviewed phase required")
    phase = sys.argv[1]
    temp = Path(os.environ["RUNNER_TEMP"]).resolve()
    WORK = temp / "conditional-separation-native-v2"
    if phase == "bootstrap":
        WORK.mkdir()
    else:
        require(WORK.is_dir() and not WORK.is_symlink(), "bootstrap outputs required")
    require(PACKAGE.name == "conditional_separation" and PACKAGE.is_relative_to(Path(os.environ["GITHUB_WORKSPACE"]).resolve()), "package-only checkout identity")
    unit_data = WORK / "unit-data"
    unit_data.mkdir(exist_ok=True)
    os.environ["CI_DATA_ROOT"] = str(unit_data)
    reserve()
    {"bootstrap": bootstrap, "foundations": foundations, "build": build, "consumers": external_consumers}[phase]()
    save(WORK / (phase + ".COMPLETE.json"), {"phase": phase, "end": utc(), "R_proved": False,
                                           "scope": "one actual native job only; no cross-platform inference"})
    print(json.dumps({"phase": phase, "completed": True, "evidence": str(WORK), "R_proved": False}), flush=True)


if __name__ == "__main__":
    main()
