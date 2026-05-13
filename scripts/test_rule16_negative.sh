#!/usr/bin/env bash
# Dedicated Rule-16 negative control —
# Research Governance v0.1, Autoresearch MVP-0.1.2.
#
# Confirms that scripts/check_candidate_rule16.sh fires SPECIFICALLY
# on hidden-payload patterns when a candidate-shape directory
# contains them, without depending on earlier gates (size policy,
# refuted-route check, etc.) failing first.  The audit observed
# that hidden-payload candidates often failed at source_theorem_size
# BEFORE Rule-16 scanning was reached, hiding the diagnostic.
#
# Each fixture is a transient `pnp3/Candidates/<name>_smoke_$$/`
# directory containing exactly one Lean file with one Rule-16-
# violating construct.  We invoke check_candidate_rule16.sh
# (NOT verify_candidate.sh, NOT check.sh) and assert:
#
#   * exit non-zero;
#   * stdout contains the [rule16] FAIL marker;
#   * stdout cites the violating pattern.
#
# After each fixture the staging dir is removed.  Trap-based
# cleanup ensures the dir never persists across runs.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

CANDIDATES_ROOT="pnp3/Candidates"

# Concurrency hardening (MVP-0.1.8 / Phase A): UUID-suffixed
# staging directories.  PID alone is insufficient in containerized
# environments where PID reuse is common.
if command -v uuidgen >/dev/null 2>&1; then
  _STAGE_UUID="$(uuidgen)"
elif [[ -r /proc/sys/kernel/random/uuid ]]; then
  _STAGE_UUID="$(cat /proc/sys/kernel/random/uuid)"
else
  _STAGE_UUID="${RANDOM}-${RANDOM}-${RANDOM}-${RANDOM}"
fi

active_stage=""

cleanup() {
  if [[ -n "${active_stage}" && -d "${active_stage}" ]]; then
    rm -rf "${active_stage}"
  fi
}
trap cleanup EXIT

fail=0

# Helper: run one negative-control case.
#   $1 = short name (e.g. "class_payload")
#   $2 = expected log-substring marker (e.g. "class[[:space:]]+")
#   $3 = Lean source body to write into proof.lean
run_case() {
  local name="$1"
  local marker="$2"
  local body="$3"
  active_stage="${CANDIDATES_ROOT}/rule16_smoke_${name}_$$_${_STAGE_UUID}"
  mkdir -p "${active_stage}"
  printf '%s\n' "${body}" >"${active_stage}/proof.lean"

  set +e
  output="$(scripts/check_candidate_rule16.sh 2>&1)"
  rc=$?
  set -e

  rm -rf "${active_stage}"
  active_stage=""

  if [[ "${rc}" -eq 0 ]]; then
    echo "[test_rule16_negative] FAIL: case ${name}: guard returned 0,"
    echo "[test_rule16_negative]   expected non-zero (Rule-16 hard reject)"
    echo "${output}"
    fail=1
    return
  fi
  if ! grep -q "\[rule16\] FAIL" <(printf '%s' "${output}"); then
    echo "[test_rule16_negative] FAIL: case ${name}: guard returned ${rc}"
    echo "[test_rule16_negative]   but '[rule16] FAIL' marker not in output"
    echo "${output}"
    fail=1
    return
  fi
  if ! grep -q -E -- "${marker}" <(printf '%s' "${output}"); then
    echo "[test_rule16_negative] FAIL: case ${name}: guard returned ${rc}"
    echo "[test_rule16_negative]   but pattern marker"
    echo "[test_rule16_negative]   '${marker}' not in output"
    echo "${output}"
    fail=1
    return
  fi
  echo "[test_rule16_negative] OK   ${name} (Rule-16 fired as expected)"
}

# ---------------------------------------------------------------------------
# Case 1: class with hidden payload field.
# ---------------------------------------------------------------------------

run_case "class_hidden_payload" "class\\[\\[:space:\\]\\]\\+" \
'-- Synthetic Rule-16 violation: typeclass-payload channel.
class FakeGapProvider where
  miracle : True'

# ---------------------------------------------------------------------------
# Case 2: instance declaration.
# ---------------------------------------------------------------------------

run_case "instance_payload" "instance\\[\\[:space:\\]\\]" \
'-- Synthetic Rule-16 violation: instance-as-payload channel.
class TrivBox where
  unbox : True

instance : TrivBox where
  unbox := trivial'

# ---------------------------------------------------------------------------
# Case 3: opaque definition.
# ---------------------------------------------------------------------------

run_case "opaque_payload" "opaque\\[\\[:space:\\]\\]\\+" \
'-- Synthetic Rule-16 violation: opaque seal.
opaque hiddenWitness : True'

# ---------------------------------------------------------------------------
# Case 4: Fact <P> argument anywhere in code.
# ---------------------------------------------------------------------------

run_case "fact_payload" "Fact" \
'-- Synthetic Rule-16 violation: Fact <P> argument.
def consume (h : Fact True) : True := h.elim id'

# ---------------------------------------------------------------------------
# Case 5 (negative-of-negative control): a CLEAN candidate with no
# Rule-16 violations should NOT cause check_candidate_rule16.sh to
# fail (it should pass with [rule16] OK).  This guards against
# false-positive over-rejection from the new fixture machinery.
# ---------------------------------------------------------------------------

active_stage="${CANDIDATES_ROOT}/rule16_smoke_clean_$$_${_STAGE_UUID}"
mkdir -p "${active_stage}"
cat >"${active_stage}/proof.lean" <<'LEAN'
-- A deliberately Rule-16-CLEAN candidate stub.
-- No class, no instance, no opaque, no Fact, no default_instance,
-- no attribute [instance].  Just a plain `theorem`.
theorem trivial_lemma : True := trivial
LEAN

set +e
output_clean="$(scripts/check_candidate_rule16.sh 2>&1)"
rc_clean=$?
set -e

rm -rf "${active_stage}"
active_stage=""

if [[ "${rc_clean}" -ne 0 ]]; then
  echo "[test_rule16_negative] FAIL: clean candidate was rejected"\
       "(rc=${rc_clean}); the negative-control fixture is over-eager."
  echo "${output_clean}"
  fail=1
else
  echo "[test_rule16_negative] OK   clean candidate accepted (no false positives)"
fi

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[test_rule16_negative] FAIL"
  exit 1
fi

echo "[test_rule16_negative] OK (4 hidden-payload patterns rejected,"\
     "1 clean candidate accepted)"
