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
# Positive controls (Audit follow-up MVP-0.1.7): a real, completed,
# non-template Critic report MUST be ACCEPTED when cited by an
# attempts.jsonl entry with critic_status = pass / fail.  Without
# these positive cases, the validator could (a) reject all template
# reports correctly, but (b) silently reject all real reports too —
# and the bad-case-only test surface would not catch that.
# ---------------------------------------------------------------------------

# Stage a synthetic completed Critic report at a path that lives
# OUTSIDE pnp3/Candidates/ (so no other guards run against it) but
# at a stable repo-relative location the validator can resolve.
POS_DIR="${WORK}/pos_critic"
mkdir -p "${POS_DIR}"

cat >"${POS_DIR}/critic_report_pass.md" <<'PASS'
# Critic report — `synthetic_positive_control_pass`

## Attack 1: Hidden-payload attack

- **status:** `no break found`
- **summary:** Synthetic positive control: candidate has no class/instance/Fact/opaque payload.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 2: Hardwiring attack

- **status:** `no break found`
- **summary:** Synthetic positive control: candidate's source theorem fixes width.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 3: KnownGuards-factorization attack

- **status:** `no break found`
- **summary:** Synthetic positive control: candidate does not factor through any accepted guard.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 4: Natural-proof / relativization / algebrization barrier audit

- **status:** `no break found`
- **summary:** Synthetic positive control: barrier certificate addresses Razborov-Rudich, BGS, AW.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 5: Collapse-not-contradiction audit

- **status:** `no break found`
- **summary:** Synthetic positive control: source theorem produces a direct circuit lower bound.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 6: Vacuity / source-theorem rephrasing audit

- **status:** `no break found`
- **summary:** Synthetic positive control: source theorem is structurally distinct from refuted predicates.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Verdict

- **critic_status:** `pass`
- **dominant_break_class:** `null`
- **dominant_break_section:** `null`
- **next_recommended_action:** `Synthetic positive control; do not act.`
PASS

cat >"${POS_DIR}/critic_report_fail.md" <<'FAIL_RPT'
# Critic report — `synthetic_positive_control_fail`

## Attack 1: Hidden-payload attack

- **status:** `no break found`
- **summary:** Synthetic positive control fail variant: no payload attack succeeded.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 2: Hardwiring attack

- **status:** `break found`
- **summary:** Synthetic positive control fail variant: a log-width truth-table hardwired family satisfies the candidate filter while being structurally hardwired.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 3: KnownGuards-factorization attack

- **status:** `attack not applicable`
- **summary:** Synthetic positive control fail variant: not investigated because attack 2 already broke the candidate.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 4: Natural-proof / relativization / algebrization barrier audit

- **status:** `attack not applicable`
- **summary:** Synthetic positive control fail variant: not investigated because attack 2 already broke the candidate.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 5: Collapse-not-contradiction audit

- **status:** `attack not applicable`
- **summary:** Synthetic positive control fail variant: not investigated because attack 2 already broke the candidate.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Attack 6: Vacuity / source-theorem rephrasing audit

- **status:** `attack not applicable`
- **summary:** Synthetic positive control fail variant: not investigated because attack 2 already broke the candidate.
- **evidence:**
    - synthetic positive-control fixture; references intentional.

## Verdict

- **critic_status:** `fail`
- **dominant_break_class:** `hardwiring`
- **dominant_break_section:** `2`
- **next_recommended_action:** `Synthetic positive control; do not act.`
FAIL_RPT

# Compute the repo-relative path for the JSONL entries.  validate_jsonl.py
# resolves critic_report_path relative to the repo root.
POS_DIR_REL="$(realpath --relative-to="${ROOT_DIR}" "${POS_DIR}")"

# ---------------------------------------------------------------------------
# Positive case A: critic_status=pass + completed non-template report.
# ---------------------------------------------------------------------------

run_case "completed_pass_real_report" "expect-pass" \
"$(printf '{"id":"ATT-999008","candidate_id":"synthetic_pos_pass","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"pass","critic_report_path":"%s/critic_report_pass.md","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}' "${POS_DIR_REL}")"

# ---------------------------------------------------------------------------
# Positive case B: critic_status=fail + completed non-template report,
# with critic_break_class agreeing with the report's dominant_break_class.
# ---------------------------------------------------------------------------

run_case "completed_fail_real_report" "expect-pass" \
"$(printf '{"id":"ATT-999009","candidate_id":"synthetic_pos_fail","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"fail","critic_break_class":"hardwiring","critic_report_path":"%s/critic_report_fail.md","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}' "${POS_DIR_REL}")"

# ---------------------------------------------------------------------------
# Negative case (cross-check): critic_status=fail with critic_break_class
# DISAGREEING with the report's dominant_break_class MUST be rejected.
# This pins the agreement check.
# ---------------------------------------------------------------------------

run_case "completed_fail_disagree_class" "expect-fail" \
"$(printf '{"id":"ATT-999010","candidate_id":"synthetic_disagree","method_family":"ac0_locality_support","verifier_status":"PASS_SHAPE_ONLY","critic_status":"fail","critic_break_class":"vacuity","critic_report_path":"%s/critic_report_fail.md","applicable_spec_version":"0.1.2","attack_suite_version":"0.1.0","created_at":"2026-05-02T00:00:00Z"}' "${POS_DIR_REL}")"

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[test_attempts_validator] FAIL"
  exit 1
fi

echo "[test_attempts_validator] OK (5 bad cases rejected, 5 good cases accepted)"
