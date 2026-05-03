#!/usr/bin/env bash
# Coordinator-driven worker driver — Research Governance v0.1, MVP-0.2.
#
# One Pilot-Wave-0 cycle, mediated by the local Coordinator service:
#
#   1. GET  /v1/task     → assignment_id + candidate_id + seed_pack
#   2. Stage a candidate package under ${WORKER_SCRATCH}/<candidate_id>/
#      by copying pnp3/Candidates/_template/.  This is a SYNTHETIC
#      stage in MVP-0.2: real Generator workers will replace this with
#      actual research math; here we only exercise the verifier+
#      submission path.
#   3. Run scripts/verify_candidate.sh on the staged candidate.
#   4. POST /v1/result with the AttemptLedgerEntry payload (the
#      Coordinator merges into outputs/attempts.jsonl atomically).
#   5. On success, clean up the staged candidate.
#
# This driver is intentionally minimal.  Real worker implementations
# will be more elaborate (per-role logic, content-hash dedup before
# step 1, retry logic, etc.).  MVP-0.2 ships this driver mainly so
# the e2e test in coordinator/test_coordinator.py can spawn N
# instances of it concurrently.
#
# Usage:
#   scripts/run_worker.sh \
#     --worker-id gen-test-001 \
#     --role gen \
#     --coordinator http://127.0.0.1:8765 \
#     [--seed-pack fp3b1_log_width_hardwiring] \
#     [--scratch /tmp/worker_$$]
#
# Exits 0 on a clean cycle; non-zero on any HTTP / verifier failure.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

WORKER_ID=""
ROLE=""
COORDINATOR=""
SEED_PACK=""
SCRATCH=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worker-id)   shift; WORKER_ID="$1"; shift ;;
    --role)        shift; ROLE="$1"; shift ;;
    --coordinator) shift; COORDINATOR="$1"; shift ;;
    --seed-pack)   shift; SEED_PACK="$1"; shift ;;
    --scratch)     shift; SCRATCH="$1"; shift ;;
    -h|--help)
      sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \?//'
      exit 0
      ;;
    *)
      echo "[run_worker] unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

if [[ -z "${WORKER_ID}" || -z "${ROLE}" || -z "${COORDINATOR}" ]]; then
  echo "[run_worker] FAIL: --worker-id, --role, --coordinator are required" >&2
  exit 2
fi

if command -v uuidgen >/dev/null 2>&1; then
  RUN_UUID="$(uuidgen)"
else
  RUN_UUID="$(cat /proc/sys/kernel/random/uuid 2>/dev/null \
              || echo "${RANDOM}-${RANDOM}-${RANDOM}-${RANDOM}")"
fi

SCRATCH="${SCRATCH:-/tmp/worker_${WORKER_ID}_${RUN_UUID}}"
mkdir -p "${SCRATCH}"
cleanup() { rm -rf "${SCRATCH}" 2>/dev/null || true; }
trap cleanup EXIT

# ---------------------------------------------------------------------------
# Step 1: GET /v1/task
# ---------------------------------------------------------------------------

TASK_URL="${COORDINATOR}/v1/task?role=${ROLE}&worker_id=${WORKER_ID}"
if [[ -n "${SEED_PACK}" ]]; then
  TASK_URL="${TASK_URL}&seed_pack=${SEED_PACK}"
fi

TASK_JSON="$(curl -fsS "${TASK_URL}" 2>"${SCRATCH}/task_err.log" || true)"
if [[ -z "${TASK_JSON}" ]]; then
  echo "[run_worker] FAIL: GET /v1/task returned empty / error" >&2
  cat "${SCRATCH}/task_err.log" >&2 || true
  exit 1
fi
echo "${TASK_JSON}" >"${SCRATCH}/task.json"

ASSIGNMENT_ID="$(python3 -c '
import json, sys
print(json.load(sys.stdin)["assignment_id"])
' < "${SCRATCH}/task.json")"
CANDIDATE_ID="$(python3 -c '
import json, sys
print(json.load(sys.stdin)["candidate_id"])
' < "${SCRATCH}/task.json")"
SEED_PACK_ID="$(python3 -c '
import json, sys
print(json.load(sys.stdin)["seed_pack_id"])
' < "${SCRATCH}/task.json")"

echo "[run_worker] assignment=${ASSIGNMENT_ID}"\
     "candidate=${CANDIDATE_ID} seed_pack=${SEED_PACK_ID}"

# ---------------------------------------------------------------------------
# Step 2: stage the candidate (SYNTHETIC for MVP-0.2)
# ---------------------------------------------------------------------------

STAGE="${SCRATCH}/candidate_${CANDIDATE_ID}"
mkdir -p "${STAGE}"
# Copy the template files; real Generator workers replace proof.lean
# with synthesised candidate Lean code.
cp pnp3/Candidates/_template/proof.lean              "${STAGE}/proof.lean"
cp pnp3/Candidates/_template/manifest.toml           "${STAGE}/manifest.toml"
cp pnp3/Candidates/_template/sketch.md               "${STAGE}/sketch.md"
cp pnp3/Candidates/_template/barrier_certificate.md  "${STAGE}/barrier_certificate.md"
cp pnp3/Candidates/_template/self_attack.md          "${STAGE}/self_attack.md"
cp pnp3/Candidates/_template/critic_report.md        "${STAGE}/critic_report.md"

# ---------------------------------------------------------------------------
# Step 3: run verify_candidate.sh
# ---------------------------------------------------------------------------

RESULT_JSON="${SCRATCH}/result.json"
# Use a per-worker VERIFY_TMP_DIR (Phase A) under our scratch.
export VERIFY_TMP_DIR="${SCRATCH}/verify_tmp"
mkdir -p "${VERIFY_TMP_DIR}"

set +e
scripts/verify_candidate.sh \
  --candidate "${STAGE}" \
  --full \
  --json "${RESULT_JSON}" \
  > "${SCRATCH}/verify.log" 2>&1
VERIFIER_RC=$?
set -e

if [[ ! -f "${RESULT_JSON}" ]]; then
  echo "[run_worker] FAIL: verify_candidate produced no JSON" >&2
  tail -10 "${SCRATCH}/verify.log" >&2 || true
  # Release the lease so the coordinator can re-assign.
  curl -fsS -X POST -d "{\"assignment_id\":\"${ASSIGNMENT_ID}\",\"worker_id\":\"${WORKER_ID}\"}" \
       "${COORDINATOR}/v1/release" >/dev/null 2>&1 || true
  exit 1
fi

VERIFIER_STATUS="$(python3 -c '
import json, sys
print(json.load(sys.stdin)["status"])
' < "${RESULT_JSON}")"
echo "[run_worker] verifier_status=${VERIFIER_STATUS}"

# ---------------------------------------------------------------------------
# Step 4: POST /v1/result
# ---------------------------------------------------------------------------

# Build the AttemptLedgerEntry payload.  candidate_id is filled by the
# coordinator from the assignment record, but we set it here too so
# validation can run server-side on a complete shape.
NOW="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
case "${VERIFIER_STATUS}" in
  PASS_SHAPE_ONLY) AS_VERIFIER_STATUS="PASS_SHAPE_ONLY" ;;
  FAIL_*)          AS_VERIFIER_STATUS="FAIL" ;;
  PASS)            AS_VERIFIER_STATUS="PASS" ;;
  *)               AS_VERIFIER_STATUS="FAIL" ;;
esac

ATTEMPT_BODY="$(python3 - "${CANDIDATE_ID}" "${AS_VERIFIER_STATUS}" \
                "${NOW}" <<'PY'
import json, sys
candidate_id, status, now = sys.argv[1], sys.argv[2], sys.argv[3]
print(json.dumps({
    "candidate_id": candidate_id,
    "method_family": "ac0_locality_support",
    "verifier_status": status,
    "critic_status": "not_run",
    "applicable_spec_version": "0.1.0",
    "attack_suite_version": "0.1.0",
    "created_at": now,
}))
PY
)"

SUBMIT_BODY="$(python3 - "${ASSIGNMENT_ID}" "${WORKER_ID}" \
               "${ATTEMPT_BODY}" <<'PY'
import json, sys
asn, wid, attempt = sys.argv[1], sys.argv[2], json.loads(sys.argv[3])
print(json.dumps({
    "assignment_id": asn,
    "worker_id": wid,
    "attempt": attempt,
}))
PY
)"

SUBMIT_RESPONSE="$(curl -fsS -X POST \
  -H "Content-Type: application/json" \
  -d "${SUBMIT_BODY}" \
  "${COORDINATOR}/v1/result" 2>"${SCRATCH}/submit_err.log" || true)"

if [[ -z "${SUBMIT_RESPONSE}" ]]; then
  echo "[run_worker] FAIL: POST /v1/result returned empty / error" >&2
  cat "${SCRATCH}/submit_err.log" >&2 || true
  exit 1
fi

ATTEMPT_ID="$(printf '%s' "${SUBMIT_RESPONSE}" | python3 -c '
import json, sys
print(json.load(sys.stdin).get("attempt_id", ""))
')"

if [[ -z "${ATTEMPT_ID}" ]]; then
  echo "[run_worker] FAIL: server response missing attempt_id" >&2
  echo "${SUBMIT_RESPONSE}" >&2
  exit 1
fi

echo "[run_worker] OK attempt_id=${ATTEMPT_ID} verifier_status=${VERIFIER_STATUS}"
exit 0
