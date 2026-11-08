"""Create a fresh ordinary workbench attempt containing the lengthwise interface."""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def snapshot(root, paths):
    """Read expected bytes independently of the later copy, without following links."""
    rows = []
    for path in sorted(paths):
        if path.is_symlink():
            raise ValueError("research copy cannot contain symlinks")
        if path.is_dir():
            continue
        if not path.is_file():
            raise ValueError("research source file missing or not regular")
        raw = path.read_bytes()
        rows.append({"path": path.relative_to(root).as_posix(),
                     "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    core, output = args.core.resolve(), args.output.resolve()
    if args.output.exists() or args.output.is_symlink():
        parser.error("output must be a new directory")
    source = Path(__file__).resolve().parent
    rows = snapshot(source, [source / "Attempt.lean", source / "Attempt",
                             *(source / "Attempt").rglob("*")])
    subprocess.run([sys.executable, "-B", str(core / "tools/workbench.py"),
                    "new", str(output), "--core", str(core)], check=True)
    scaffold = [r for r in snapshot(output, output.rglob("*")) if r["path"] != "Attempt.lean"]
    shutil.copyfile(source / "Attempt.lean", output / "Attempt.lean")
    shutil.copytree(source / "Attempt", output / "Attempt")
    if snapshot(output, output.rglob("*")) != sorted(scaffold + rows, key=lambda r: Path(r["path"])):
        raise ValueError("research copy differs from pre-copy source snapshot")
    (output / "RESEARCH_SOURCE_MANIFEST.json").write_text(
        json.dumps({"status": "PARTIAL_INTERFACE_NOT_PROOF_OF_R", "files": rows},
                   indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"attempt": str(output), "source_files": len(rows),
                      "status": "PARTIAL_INTERFACE_NOT_PROOF_OF_R"}))


if __name__ == "__main__":
    main()
