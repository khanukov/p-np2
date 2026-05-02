#!/usr/bin/env bash
# Bad-case smoke test for outputs/attempts.jsonl validator —
# Research Governance v0.1, Autoresearch MVP-0.1.1.
#
# Asserts that scripts/validate_jsonl.py::validate_attempt rejects
# the three Critic-state pass-traps that the audit identified:
#
#   1. critic_status = "pass" with no critic_report_path field;
#   2. critic_status = "pass" with critic_report_path pointing at a
#      non-existent file;
#   3. critic_status = "pass" with critic_report_path pointing at the
#      empty template (pnp3/Candidates/_template/critic_report.md).
#
# Also asserts that legitimate not_run / completed-pass cases pass.
#
# This test does NOT mutate outputs/attempts.jsonl.  It exercises the
# validator directly on synthetic JSONL fragments via a temporary
# file.  If the validator regresses (i.e. starts accepting any of the
# three bad cases), this test exits non-zero and scripts/check.sh
# fails.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

WORK="$(mktemp -d)"
trap 'rm -rf "${WORK}"' EXIT

fail=0

# Helper: write a single-line attempts.jsonl to ${WORK}/<name>.jsonl
# and run the validator.  $1 = name, $2 = expect-fail/expect-pass,
# $3 = JSON line.
run_case() {
  local name="$1"
  local expect="$2"
  local body="$3"
  # Place each fixture in its own subdirectory so the basename is
  # `attempts.jsonl`, which makes scripts/validate_jsonl.py dispatch
  # to the AttemptLedgerEntry validator (basename-based).
  local dir="${WORK}/${name}"
  mkdir -p "${dir}"
  local file="${dir}/attempts.jsonl"
  printf '%s\n' "${body}" >"${file}"
  set +e
  output="$(python3 scripts/validate_jsonl.py "${file}" 2>&1)"
  rc=$?
  set -e
  if [[ "${expect}" == "expect-fail" ]]; then
    if [[ "${rc}" -eq 0 ]]; then
      echo "[test_attempts_validator] FAIL: case ${name} should have"\
           "been rejected but validator returned 0"
      printf '  output: %s\n' "${output}"
      fail=1
    else
      echo "[test_attempts_validator] OK   ${name} (rejected as expected)"
    fi
  else
    if [[ "${rc}" -ne 0 ]]; then
      echo "[test_attempts_validator] FAIL: case ${name} should have"\
           "been accepted but validator returned ${rc}"
      printf '  output: %s\n' "${output}"
      fail=1
    else
      echo "[test_attempts_validator] OK   ${name} (accepted as expected)"
    fi
  fi
}

# ---------------------------------------------------------------------------
# Bad case 1: pass + no critic_report_path field.
# ---------------------------------------------------------------------------

run_case "pass_no_path" "expect-fail" \
'{"id":"ATT-999001","candidate_id":"synthetic","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"pass","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}'

# ---------------------------------------------------------------------------
# Bad case 2: pass + critic_report_path → nonexistent file.
# ---------------------------------------------------------------------------

run_case "pass_nonexistent_path" "expect-fail" \
'{"id":"ATT-999002","candidate_id":"synthetic","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"pass","critic_report_path":"pnp3/Candidates/__nonexistent__/critic_report.md","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}'

# ---------------------------------------------------------------------------
# Bad case 3: pass + critic_report_path → empty template.
# ---------------------------------------------------------------------------

run_case "pass_template_path" "expect-fail" \
'{"id":"ATT-999003","candidate_id":"synthetic","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"pass","critic_report_path":"pnp3/Candidates/_template/critic_report.md","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}'

# ---------------------------------------------------------------------------
# Bad case 4: fail + missing critic_break_class.
# ---------------------------------------------------------------------------

run_case "fail_no_break_class" "expect-fail" \
'{"id":"ATT-999004","candidate_id":"synthetic","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"fail","critic_report_path":"pnp3/Candidates/_template/critic_report.md","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}'

# ---------------------------------------------------------------------------
# Good case 1: PASS_SHAPE_ONLY + critic_status=not_run + path to template
# (this is the Verifier-only / Critic-not-yet-run state).
# ---------------------------------------------------------------------------

run_case "passshape_notrun_template" "expect-pass" \
'{"id":"ATT-999005","candidate_id":"synthetic","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"not_run","critic_report_path":"pnp3/Candidates/_template/critic_report.md","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}'

# ---------------------------------------------------------------------------
# Good case 2: PASS_SHAPE_ONLY + critic_status=not_run, no path at all.
# ---------------------------------------------------------------------------

run_case "passshape_notrun_no_path" "expect-pass" \
'{"id":"ATT-999006","candidate_id":"synthetic","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"not_run","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}'

# ---------------------------------------------------------------------------
# Good case 3: FAIL + verifier_failure_class populated + critic_status=not_run.
# ---------------------------------------------------------------------------

run_case "fail_with_class_notrun" "expect-pass" \
'{"id":"ATT-999007","candidate_id":"synthetic","method_family":"ac0_locality_support","verifier_status":"FAIL","verifier_failure_class":"refuted_route","critic_status":"not_run","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}'

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[test_attempts_validator] FAIL"
  exit 1
fi

echo "[test_attempts_validator] OK (4 bad cases rejected, 3 good cases accepted)"
