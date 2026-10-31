"""PROSPECTIVE best-effort native CI staging entry; never run by preflight."""
import sys
if sys.flags.optimize:
    raise SystemExit("optimized evidence export rejected")
import json
import os
from pathlib import Path
from ci_evidence_data_v2 import stage_evidence


def main():
    if os.environ.get("GITHUB_ACTIONS") != "true" or os.environ.get("CI") != "true":
        raise SystemExit("future native Actions context required")
    package = Path(__file__).resolve().parents[1]
    temp = Path(os.environ["RUNNER_TEMP"]).resolve()
    work = temp / "conditional-separation-native-v2"
    identity = {"event": os.environ.get("GITHUB_EVENT_NAME"), "expected_head": os.environ.get("CI_EXPECTED_HEAD"),
                "native_validation_status": "UNKNOWN_UNTIL_ACTUAL_RECEIPTS_AND_JOB_RESULTS_VERIFIED"}
    path = work / "HEAD_IDENTITY.json"
    if path.is_file() and not path.is_symlink():
        identity["head_admission_record"] = json.loads(path.read_bytes())
    path = package.parent / "SOURCE_MATERIALIZATION.json"
    if path.is_file() and not path.is_symlink():
        record = json.loads(path.read_bytes())
        if record.get("schema") != "package-source-blobs-v1" or record.get("head") != os.environ.get("CI_EXPECTED_HEAD"):
            raise ValueError("materialization/head evidence disagreement")
        identity["source_materialization_record"] = record
    result = stage_evidence(work, package, temp / "conditional-separation-evidence-v2", identity)
    print(json.dumps({"export_complete": result["export_complete"], "files": len(result["files"]),
                      "omissions": len(result["omissions"]), "phase_states": result["phase_states"],
                      "native_validation_pass": False}), flush=True)
    return 0 if result["export_complete"] else 1


if __name__ == "__main__":
    sys.exit(main())
