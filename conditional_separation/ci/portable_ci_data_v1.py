"""Portable DATA operations for a prospective CI recipe; no process/network API.

Extraction never marks or executes installers. Operational CI dispatch lives in
the separately reviewable, currently unexecuted native_ci_v1.py.
"""
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import tarfile
import zipfile

TOOLCHAIN = "leanprover/lean4:v4.22.0-rc2"
LOCK_SHA = "5b19b358e6f9c81df0e5f935bd0bf483ddf4339b50f0cb1b828724d2b76dda3a"
RUNNERS = {
    "ubuntu-24.04": ("Linux", "x86_64", "x64"),
    "ubuntu-24.04-arm": ("Linux", "aarch64", "arm64"),
    "macos-15": ("Darwin", "aarch64", "arm64"),
    "macos-15-intel": ("Darwin", "x86_64", "x64"),
    "windows-2022": ("Windows", "x86_64", "x64"),
}
TRIPLES = {
    ("Linux", "x86_64"): "x86_64-unknown-linux-gnu.tar.gz",
    ("Linux", "aarch64"): "aarch64-unknown-linux-gnu.tar.gz",
    ("Darwin", "x86_64"): "x86_64-apple-darwin.tar.gz",
    ("Darwin", "aarch64"): "aarch64-apple-darwin.tar.gz",
    ("Windows", "x86_64"): "x86_64-pc-windows-msvc.zip",
}


def require(value, message):
    if not value:
        raise ValueError(message)


def read_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs)


def architecture(machine):
    value = {"x86_64": "x86_64", "amd64": "x86_64", "arm64": "aarch64", "aarch64": "aarch64"}.get(machine.lower())
    require(value is not None, "unsupported native architecture")
    return value


def validate_runner(runner, system, machine, python_arch):
    require(runner in RUNNERS, "unknown standard runner label")
    actual = (system, architecture(machine), python_arch)
    require(actual == RUNNERS[runner], "native runner/Python architecture mismatch")
    return actual[1]


def load_assets(path):
    document = read_json(Path(path).read_bytes())
    require(document["repository"] == "leanprover/elan" and document["tag_name"] == "v4.2.4", "Elan release identity")
    rows = document["assets"]
    require(len(rows) == 5 and len({row["name"] for row in rows}) == 5, "complete unique Elan asset set")
    for row in rows:
        require(row["name"] in {"elan-" + suffix for suffix in TRIPLES.values()}, "unexpected asset")
        require(type(row["size"]) is int and 0 < row["size"] < 16 * 1024 * 1024, "asset size")
        require(re.fullmatch(r"sha256:[0-9a-f]{64}", row["digest"]) is not None, "asset digest")
        require(row["browser_download_url"] == "https://github.com/leanprover/elan/releases/download/v4.2.4/" + row["name"], "official exact asset URL")
    return rows


def asset_for(rows, system, machine):
    key = (system, architecture(machine))
    require(key in TRIPLES, "unsupported native platform")
    expected = "elan-" + TRIPLES[key]
    selected = [row for row in rows if row["name"] == expected]
    require(len(selected) == 1, "exact asset absent/duplicate")
    return selected[0]


def safe_name(name):
    require(isinstance(name, str) and name and "\\" not in name and ":" not in name and "\x00" not in name, "archive name")
    pure = PurePosixPath(name)
    require(not pure.is_absolute() and pure.as_posix() == name and ".." not in pure.parts, "canonical relative archive path")
    require(all(part not in {".git", ".lake", "__pycache__", "reports"} for part in pure.parts), "excluded source component")
    require(pure.suffix.lower() not in {".olean", ".ilean", ".pyc", ".log", ".o", ".so", ".dll", ".dylib"}, "derived object in source")
    return pure


def installer_payload(data, row):
    require(type(row["size"]) is int and len(data) == row["size"], "installer byte size")
    require(row["digest"] == "sha256:" + hashlib.sha256(data).hexdigest(), "installer SHA256")
    expected = "elan-init.exe" if row["name"].endswith(".zip") else "elan-init"
    try:
        if expected.endswith(".exe"):
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                members = archive.infolist()
                require(len(members) == 1, "single installer member required")
                member = members[0]
                require(member.filename == expected and not member.is_dir() and
                        not stat.S_ISLNK(member.external_attr >> 16) and member.file_size <= 64 * 1024 * 1024, "installer ZIP member")
                payload = archive.read(member)
        else:
            with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
                members = archive.getmembers()
                require(len(members) == 1, "single installer member required")
                member = members[0]
                require(member.name == expected and member.isfile() and member.size <= 64 * 1024 * 1024, "installer tar member")
                stream = archive.extractfile(member)
                require(stream is not None, "installer data absent")
                with stream:
                    payload = stream.read(64 * 1024 * 1024 + 1)
        require(0 < len(payload) <= 64 * 1024 * 1024, "installer payload size")
        return expected, payload
    except (tarfile.TarError, zipfile.BadZipFile, EOFError) as error:
        raise ValueError("malformed installer archive") from error


def unpack_installer(data, row, destination):
    name, payload = installer_payload(data, row)
    destination = Path(destination)
    require(not destination.exists() and not destination.is_symlink(), "fresh installer destination required")
    destination.mkdir(parents=True)
    target = destination / name
    with target.open("xb") as stream:
        stream.write(payload)
    return target


def validate_lock(data):
    require(hashlib.sha256(data).hexdigest() == LOCK_SHA, "exact declared dependency lock changed")
    document = read_json(data)
    require(document["packagesDir"] == ".lake/packages" and document["name"] == "conditional_separation", "Lake package layout")
    rows = document["packages"]
    require(len(rows) == 9 and len({r["name"] for r in rows}) == 9, "complete locked dependency set")
    for row in rows:
        require(row["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", row["rev"]) is not None and
                row["url"].startswith("https://github.com/") and row["subDir"] is None, "source-only fixed Git dependency")
    return rows


def source_payloads(data):
    result = {}
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for member in archive.infolist():
                path = safe_name(member.filename)
                require(not member.is_dir() and not stat.S_ISLNK(member.external_attr >> 16), "source regular files only")
                require(str(path) not in result and member.file_size <= 16 * 1024 * 1024, "source duplicate/oversize")
                result[path.as_posix()] = archive.read(member)
    except zipfile.BadZipFile as error:
        raise ValueError("malformed source archive") from error
    require("PACKAGE_FILES.json" in result, "source inventory absent")
    inventory = read_json(result["PACKAGE_FILES.json"])
    require(set(inventory) == {"schema", "files"} and inventory["schema"] == "conditional-separation-source-files-v1", "source inventory schema")
    wanted = {"PACKAGE_FILES.json"}
    for row in inventory["files"]:
        require(isinstance(row, dict) and set(row) == {"path", "bytes", "sha256"}, "source pin schema")
        name = safe_name(row["path"]).as_posix()
        require(name not in wanted and name in result, "duplicate/missing source pin")
        require(type(row["bytes"]) is int and row["bytes"] >= 0 and len(result[name]) == row["bytes"] and
                hashlib.sha256(result[name]).hexdigest() == row["sha256"], "source digest/size mismatch")
        wanted.add(name)
    require(set(result) == wanted, "complete source archive NAME SET")
    return result


def unpack_source(data, destination):
    payloads = source_payloads(data)
    destination = Path(destination)
    require(not destination.exists() and not destination.is_symlink(), "fresh installed source destination required")
    destination.mkdir(parents=True)
    for name, payload in payloads.items():
        target = destination / Path(*PurePosixPath(name).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(payload)
    return destination


def install_commands(installer, elan_home, system):
    exe = str(Path(elan_home) / "bin" / ("elan.exe" if system == "Windows" else "elan"))
    return [[str(installer), "--help"],
            [str(installer), "-y", "--no-modify-path", "--default-toolchain", "none"],
            [exe, "toolchain", "install", TOOLCHAIN]]


def consumer_source():
    proposition = """ConditionalSeparation.OpenProblem.R → ∃ k : Nat,
  UniformClassBridgeClosure.Ordinary.UniformNP
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  ¬ Pnp3.ComplexityInterfaces.PpolyDAG
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
  ¬ UniformClassBridgeClosure.Ordinary.UniformP
    (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k)))"""
    return ("import ConditionalSeparation.Conditional\nopen Pnp4.Frontier Pnp4.Frontier.ContractExpansion\nnamespace Attempt\n"
            + "theorem conditional_surface : " + proposition + " := ConditionalSeparation.close\n"
            + "theorem check_conditional_surface : " + proposition + " := conditional_surface\n"
            + "#print axioms conditional_surface\n#print axioms check_conditional_surface\nend Attempt\n")
