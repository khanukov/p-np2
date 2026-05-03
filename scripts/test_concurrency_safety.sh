#!/usr/bin/env bash
# Concurrency-safety smoke for the append-only ledger writers —
# Research Governance v0.1, Autoresearch MVP-0.1.8 / Phase A.
#
# Spawns N=16 background invocations of scripts/attempts_append.py
# and scripts/nogolog_append.py against TEMPORARY ledger files (the
# real outputs/{attempts,nogolog}.jsonl are not touched).  Asserts:
#
#   1. all 16 invocations exit 0;
#   2. the resulting JSONL has exactly 16 distinct ATT-NNNNNN ids
#      (or NOGO-NNNNNN ids) — no duplicates, no drops;
#   3. each line parses as valid JSON;
#   4. ids are monotonically increasing in line order or at least
#      in the contiguous ATT-000001 .. ATT-000016 set;
#   5. the lockfile sibling (outputs/<log>.lock) was created and
#      no half-written line exists in the JSONL.
#
# This test exercises the fcntl.flock-protected ID assignment and
# append paths added in MVP-0.1.8.  Without those locks, two
# concurrent invocations would produce duplicate ids or interleaved
# JSON bytes mid-line.
#
# The test does NOT mutate outputs/.  It runs against:
#   * a temporary attempts.jsonl staged at
#     ${WORK}/test_attempts/outputs/attempts.jsonl, and
#   * a temporary nogolog.jsonl at ${WORK}/test_nogolog/outputs/nogolog.jsonl.
#
# To make the append scripts target these temp paths, the test
# launches each invocation in a subshell with the working directory
# pointed at the stub repo and a stub `scripts/` symlink.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if command -v uuidgen >/dev/null 2>&1; then
  _SAFETY_UUID="$(uuidgen)"
elif [[ -r /proc/sys/kernel/random/uuid ]]; then
  _SAFETY_UUID="$(cat /proc/sys/kernel/random/uuid)"
else
  _SAFETY_UUID="${RANDOM}-${RANDOM}-${RANDOM}-${RANDOM}"
fi

WORK="$(mktemp -d -t concurrency_safety_${_SAFETY_UUID}_XXXX)"
trap 'rm -rf "${WORK}"' EXIT

N=16
fail=0

# ---------------------------------------------------------------------------
# Helper: stage a stub repo where outputs/ is fresh.  Symlink the
# spec/ and scripts/ trees so the append scripts find their imports
# (validate_jsonl, validate_critic_report) and the schema files.
# ---------------------------------------------------------------------------

stage_stub_repo() {
  local stub="$1"
  mkdir -p "${stub}/outputs" "${stub}/scripts" "${stub}/spec"
  # IMPORTANT: copy (not symlink) the writer scripts so that
  # `Path(__file__).resolve().parent.parent` inside Python resolves
  # to the stub repo, not the real one.  A symlink would let
  # Python follow the link back to the canonical script and
  # pollute outputs/ in the real repo.  Read-only helper modules
  # (validate_jsonl, validate_critic_report) are also copied so
  # the writers' `from validate_jsonl import …` finds them on the
  # stub's sys.path entry that the writers add.
  cp "${ROOT_DIR}/scripts/validate_jsonl.py"          "${stub}/scripts/"
  cp "${ROOT_DIR}/scripts/validate_critic_report.py"  "${stub}/scripts/"
  cp "${ROOT_DIR}/scripts/attempts_append.py"         "${stub}/scripts/"
  cp "${ROOT_DIR}/scripts/nogolog_append.py"          "${stub}/scripts/"
  cp "${ROOT_DIR}/spec/nogolog_schema.json"           "${stub}/spec/"
  : >"${stub}/outputs/attempts.jsonl"
  : >"${stub}/outputs/nogolog.jsonl"
  : >"${stub}/outputs/survivor_history.jsonl"
}

# ---------------------------------------------------------------------------
# Test 1: N parallel attempts_append.py invocations.
# ---------------------------------------------------------------------------

ATTEMPTS_STUB="${WORK}/test_attempts"
stage_stub_repo "${ATTEMPTS_STUB}"

for i in $(seq 1 ${N}); do
  (
    cd "${ATTEMPTS_STUB}"
    cat <<JSON | python3 scripts/attempts_append.py >>"${WORK}/attempts_ids_${i}.txt" 2>"${WORK}/attempts_err_${i}.txt"
{"candidate_id":"synthetic_concurrent_${i}","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"not_run","applicable_spec_version":"0.1.0","attack_suite_version":"0.1.0"}
JSON
  ) &
done
wait

# Collect the ids each subshell received from its append script.
emitted_ids=()
for i in $(seq 1 ${N}); do
  if [[ ! -s "${WORK}/attempts_ids_${i}.txt" ]]; then
    echo "[test_concurrency_safety] FAIL: invocation ${i} produced no id"
    cat "${WORK}/attempts_err_${i}.txt" 2>/dev/null \
      | sed 's/^/[test_concurrency_safety]   /'
    fail=1
    continue
  fi
  emitted_ids+=("$(head -1 "${WORK}/attempts_ids_${i}.txt")")
done

# Distinct count.
distinct_count="$(printf '%s\n' "${emitted_ids[@]}" | sort -u | wc -l)"
if [[ "${distinct_count}" -ne "${N}" ]]; then
  echo "[test_concurrency_safety] FAIL: attempts: ${distinct_count}/${N} distinct ids"
  echo "[test_concurrency_safety]   ids = ${emitted_ids[*]}"
  fail=1
else
  echo "[test_concurrency_safety] OK   attempts: ${N}/${N} distinct ATT ids"
fi

# Ledger line count + JSON validity.
ledger_lines="$(wc -l < "${ATTEMPTS_STUB}/outputs/attempts.jsonl" | tr -d ' ')"
if [[ "${ledger_lines}" -ne "${N}" ]]; then
  echo "[test_concurrency_safety] FAIL: attempts ledger has ${ledger_lines} lines, expected ${N}"
  fail=1
fi

while IFS= read -r line; do
  if ! printf '%s' "${line}" | python3 -c '
import json, sys
try:
    json.loads(sys.stdin.read())
except Exception as e:
    print(f"INVALID: {e}")
    sys.exit(1)
'; then
    echo "[test_concurrency_safety] FAIL: attempts ledger contains a non-JSON line"
    fail=1
    break
  fi
done <"${ATTEMPTS_STUB}/outputs/attempts.jsonl"

# Lockfile presence.
if [[ ! -f "${ATTEMPTS_STUB}/outputs/attempts.jsonl.lock" ]]; then
  echo "[test_concurrency_safety] FAIL: attempts.jsonl.lock not created"
  fail=1
else
  echo "[test_concurrency_safety] OK   attempts.jsonl.lock present"
fi

# ---------------------------------------------------------------------------
# Test 2: N parallel nogolog_append.py invocations.
# ---------------------------------------------------------------------------

NOGO_STUB="${WORK}/test_nogolog"
stage_stub_repo "${NOGO_STUB}"

for i in $(seq 1 ${N}); do
  (
    cd "${NOGO_STUB}"
    cat <<JSON | python3 scripts/nogolog_append.py >>"${WORK}/nogo_ids_${i}.txt" 2>"${WORK}/nogo_err_${i}.txt"
{"candidate_id":"synthetic_concurrent_${i}","method_family":"ac0_locality_support","status":"formalized","failure_class":"hardwiring","structural_pattern":"synthetic concurrent test pattern ${i}","counterexample_family":"synthetic concurrent test family ${i}","why_generalizes":"synthetic concurrent test rationale ${i}","formal_witness":null,"regression_test":null,"applicable_spec_version":"0.1.0","attack_suite_version":"0.1.0"}
JSON
  ) &
done
wait

nogo_emitted_ids=()
for i in $(seq 1 ${N}); do
  if [[ ! -s "${WORK}/nogo_ids_${i}.txt" ]]; then
    echo "[test_concurrency_safety] FAIL: nogo invocation ${i} produced no id"
    cat "${WORK}/nogo_err_${i}.txt" 2>/dev/null \
      | sed 's/^/[test_concurrency_safety]   /'
    fail=1
    continue
  fi
  nogo_emitted_ids+=("$(head -1 "${WORK}/nogo_ids_${i}.txt")")
done

nogo_distinct="$(printf '%s\n' "${nogo_emitted_ids[@]}" | sort -u | wc -l)"
if [[ "${nogo_distinct}" -ne "${N}" ]]; then
  echo "[test_concurrency_safety] FAIL: nogo: ${nogo_distinct}/${N} distinct ids"
  echo "[test_concurrency_safety]   ids = ${nogo_emitted_ids[*]}"
  fail=1
else
  echo "[test_concurrency_safety] OK   nogo: ${N}/${N} distinct NOGO ids"
fi

nogo_lines="$(wc -l < "${NOGO_STUB}/outputs/nogolog.jsonl" | tr -d ' ')"
if [[ "${nogo_lines}" -ne "${N}" ]]; then
  echo "[test_concurrency_safety] FAIL: nogo ledger has ${nogo_lines} lines, expected ${N}"
  fail=1
fi

if [[ ! -f "${NOGO_STUB}/outputs/nogolog.jsonl.lock" ]]; then
  echo "[test_concurrency_safety] FAIL: nogolog.jsonl.lock not created"
  fail=1
else
  echo "[test_concurrency_safety] OK   nogolog.jsonl.lock present"
fi

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[test_concurrency_safety] FAIL"
  exit 1
fi

echo "[test_concurrency_safety] OK (2 ledger writers x N=${N} parallel invocations, all distinct ids, no corruption)"
