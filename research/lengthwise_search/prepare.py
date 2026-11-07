"""Create a fresh ordinary workbench attempt containing the lengthwise interface."""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    core, output = args.core.resolve(), args.output.resolve()
    if args.output.exists() or args.output.is_symlink():
        parser.error("output must be a new directory")
    subprocess.run([sys.executable, "-B", str(core / "tools/workbench.py"),
                    "new", str(output), "--core", str(core)], check=True)
    source = Path(__file__).resolve().parent
    shutil.copyfile(source / "Attempt.lean", output / "Attempt.lean")
    shutil.copytree(source / "Attempt", output / "Attempt")
    rows = []
    for path in sorted(output.rglob("*.lean")):
        if path.name == "lakefile.lean":
            continue
        raw = path.read_bytes()
        rows.append({"path": path.relative_to(output).as_posix(),
                     "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()})
    (output / "RESEARCH_SOURCE_MANIFEST.json").write_text(
        json.dumps({"status": "PARTIAL_INTERFACE_NOT_PROOF_OF_R", "files": rows},
                   indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"attempt": str(output), "source_files": len(rows),
                      "status": "PARTIAL_INTERFACE_NOT_PROOF_OF_R"}))


if __name__ == "__main__":
    main()
