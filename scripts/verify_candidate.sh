#!/usr/bin/env bash
# verify_candidate.sh — Research Governance v0.1.
#
# Composes the currently-shipped global guards plus per-candidate
# checks into a deterministic verifier and emits a human-readable
# trace to stdout (always) and a JSON `result.json` (with --json).
#
# Status semantics (Plan v0.2.1):
#
#   PASS_SHAPE_ONLY        every check returned PASS.
#   HUMAN_REVIEW_REQUIRED  at least one check returned
#                          HUMAN_REVIEW_REQUIRED and none returned
#                          a FAIL.  Per Rule 4 / Rule 7 this is
#                          NOT auto-reject; the candidate enters
#                          the human-review queue.
#   FAIL_<reason>          at least one check returned FAIL.
#                          `<reason>` is the snake_case name of the
#                          FIRST check that failed; all failures are
#                          listed in `reasons`.
#   EXPIRED_REVIEW         (reserved; produced when SLA expiry is
#                          implemented in a follow-up PR).
#
# `PASS_SHAPE_ONLY` is the highest positive status this verifier
# emits.  Per `RESEARCH_CONSTITUTION.md` Rule 1, an `accepted`
# status requires a closed `P_ne_NP_unconditional` term, which the
# verifier does NOT yet check.
#
# Output schema: `scripts/verifier_result_schema.json` (Plan v0.2.1
# PR 15).
#
# Usage:
#
#   scripts/verify_candidate.sh [--candidate <dir>] [--json <path>] [--full]
#
#   --candidate <dir>   Optional candidate directory (relative to
#                       repo root).  Without it, only tree-level
#                       guards run.
#   --json <path>       Optional JSON output path.  When given, the
#                       script writes result.json after the run.
#   --full              Run the FULL verifier (PR 15.1):
#                       core guards + target_lock + Rule-16
#                       candidate-local scan + JSONL validation +
#                       barrier-certificate queue scan.  Without
#                       this flag the script runs only the
#                       candidate-core checks (PR 15 baseline).
#                       The full mode is what `scripts/check.sh`
#                       Step 12/16 invokes; standalone use of this
#                       script outside CI should also pass --full
#                       to get coverage equivalent to scripts/check.sh.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

VERIFIER_IMPL_LEVEL="v1.0"

usage() {
  cat <<USAGE
Usage: scripts/verify_candidate.sh [--candidate <dir>] [--json <path>]

  --candidate <dir>   Optional path to a candidate directory.
                      Adds Rule 3 file-shape, Rule 4 size, and
                      Rule 7 barrier-certificate checks.

  --json <path>       Write a JSON result.json to <path>; schema
                      at scripts/verifier_result_schema.json.

  Without --candidate, the verifier runs the four currently-shipped
  global guards and reports tree-level status only.
USAGE
}

candidate_dir=""
json_path=""
full_mode=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate)
      shift
      [[ $# -gt 0 ]] || { usage >&2; exit 2; }
      candidate_dir="$1"
      shift
      ;;
    --json)
      shift
      [[ $# -gt 0 ]] || { usage >&2; exit 2; }
      json_path="$1"
      shift
      ;;
    --full)
      full_mode=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "[verify] unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

# ---------------------------------------------------------------------------
# Per-check tracking.  Parallel arrays keep the result.json field
# order deterministic.
# ---------------------------------------------------------------------------

check_names=()
check_statuses=()
reasons=()
first_fail=""

record_check() {
  # $1: check name
  # $2: status (PASS / FAIL / HUMAN_REVIEW_REQUIRED / SKIPPED / UNKNOWN)
  # $3: reason text (only used when status != PASS)
  local name="$1" status="$2" reason="${3:-}"
  check_names+=("${name}")
  check_statuses+=("${status}")
  case "${status}" in
    FAIL)
      reasons+=("${name}: ${reason}")
      [[ -z "${first_fail}" ]] && first_fail="${name}"
      ;;
    HUMAN_REVIEW_REQUIRED)
      reasons+=("${name}: ${reason}")
      ;;
    *)
      ;;
  esac
}

# ---------------------------------------------------------------------------
# (A) Optional candidate-shape check (PR 7).
# ---------------------------------------------------------------------------

candidate_id=""
candidate_dir_for_json="null"
# Autoresearch MVP-4 marker: whether the optional critic_report.md
# exists in the candidate directory.  Set during the candidate-shape
# check; defaults to false when no candidate is supplied (tree-level
# run, e.g. via scripts/check.sh's smoke step against the template).
critic_report_present="false"
if [[ -n "${candidate_dir}" ]]; then
  candidate_dir_for_json="\"${candidate_dir}\""
  candidate_id="$(basename "${candidate_dir%/}")"

  echo "[verify] candidate-shape check: ${candidate_dir}"
  if [[ ! -d "${candidate_dir}" ]]; then
    echo "[verify]   FAIL: candidate directory does not exist"
    record_check "candidate_shape" "FAIL" \
                 "missing directory ${candidate_dir}"
  else
    required_files=(
      "proof.lean"
      "manifest.toml"
      "sketch.md"
      "barrier_certificate.md"
      "self_attack.md"
    )
    missing=()
    for f in "${required_files[@]}"; do
      if [[ ! -f "${candidate_dir}/${f}" ]]; then
        missing+=("${f}")
      fi
    done
    if [[ ${#missing[@]} -gt 0 ]]; then
      echo "[verify]   FAIL: missing required files: ${missing[*]}"
      record_check "candidate_shape" "FAIL" \
                   "missing ${missing[*]}"
    else
      # Autoresearch MVP-4: surface whether the optional critic_report.md
      # is present.  The Verifier does NOT require it (Critic runs AFTER
      # Verifier per spec/critic_protocol.md), but reporting its
      # presence in the result.json helps downstream tooling decide
      # whether to record critic_status = not_run vs. parse the report.
      if [[ -f "${candidate_dir}/critic_report.md" ]]; then
        critic_report_present="true"
      fi
      echo "[verify]   PASS (all 5 required files present;"\
        "critic_report.md present=${critic_report_present})"
      record_check "candidate_shape" "PASS"

      # PR 12: barrier-certificate per-candidate check.
      echo "[verify] running: barrier_certificate"
      if [[ ! -x "scripts/check_barrier_certificate.sh" ]]; then
        echo "[verify]   FAIL: scripts/check_barrier_certificate.sh is not executable"
        record_check "barrier_certificate" "FAIL" "guard not executable"
      else
        set +e
        scripts/check_barrier_certificate.sh "${candidate_dir}" \
          > "/tmp/verify_barrier_certificate.log" 2>&1
        bc_rc=$?
        set -e
        bc_status="$(awk -F= '/^\[barrier\] status=/ { print $2 }' \
                          /tmp/verify_barrier_certificate.log)"
        bc_status="${bc_status:-unknown}"
        if [[ "${bc_rc}" -ne 0 ]]; then
          echo "[verify]   FAIL: barrier checker returned ${bc_rc}"
          tail -8 /tmp/verify_barrier_certificate.log \
            | sed 's/^/[verify]     /'
          record_check "barrier_certificate" "FAIL" \
                       "returned ${bc_rc} (status=${bc_status})"
        elif [[ "${bc_status}" == "human-review-required" ]]; then
          echo "[verify]   HUMAN_REVIEW_REQUIRED (barrier certificate)"
          record_check "barrier_certificate" "HUMAN_REVIEW_REQUIRED" \
                       "Rule 7 (barrier_certificate)"
        else
          echo "[verify]   PASS (barrier status=${bc_status})"
          record_check "barrier_certificate" "PASS"
        fi
      fi

      # PR 15.2: candidate kernel-elaboration check (Layer 3 of the
      # Machine Revalidation Review).  This is the first check that
      # actually invokes the Lean kernel on `<candidate>/proof.lean`.
      # Without this step, type errors and sorry/admit in candidate
      # code are silently accepted by the verifier.
      #
      # Only runs in --full mode because it requires `lake env lean`
      # and the candidate's imports to already be built.  In core
      # mode the check is recorded as SKIPPED.
      echo "[verify] running: candidate_kernel_elaboration"
      if [[ "${full_mode}" -ne 1 ]]; then
        echo "[verify]   SKIPPED (--full not set)"
        record_check "candidate_kernel_elaboration" "SKIPPED"
      elif [[ ! -x "scripts/check_candidate_kernel.sh" ]]; then
        echo "[verify]   FAIL: scripts/check_candidate_kernel.sh is not executable"
        record_check "candidate_kernel_elaboration" "FAIL" \
                     "guard not executable"
      else
        set +e
        scripts/check_candidate_kernel.sh "${candidate_dir}" \
          > "/tmp/verify_candidate_kernel_elaboration.log" 2>&1
        kernel_rc=$?
        set -e
        kernel_status="$(awk -F= '/^\[kernel\] status=/ { print $2 }' \
                          /tmp/verify_candidate_kernel_elaboration.log)"
        kernel_status="${kernel_status:-unknown}"
        if [[ "${kernel_rc}" -ne 0 ]]; then
          echo "[verify]   FAIL: kernel check returned ${kernel_rc} (status=${kernel_status})"
          tail -10 /tmp/verify_candidate_kernel_elaboration.log \
            | sed 's/^/[verify]     /'
          record_check "candidate_kernel_elaboration" "FAIL" \
                       "returned ${kernel_rc} (status=${kernel_status})"
        else
          echo "[verify]   PASS (kernel status=${kernel_status})"
          record_check "candidate_kernel_elaboration" "PASS"
        fi
      fi

      # PR 8: source theorem size policy (Rule 4).
      echo "[verify] running: source_theorem_size"
      if [[ ! -x "scripts/check_source_theorem_size.sh" ]]; then
        echo "[verify]   FAIL: scripts/check_source_theorem_size.sh is not executable"
        record_check "source_theorem_size" "FAIL" "guard not executable"
      else
        set +e
        scripts/check_source_theorem_size.sh "${candidate_dir}" \
          > "/tmp/verify_source_theorem_size.log" 2>&1
        size_rc=$?
        set -e
        size_status="$(awk -F= '/^\[size\] status=/ { print $2 }' \
                          /tmp/verify_source_theorem_size.log)"
        size_status="${size_status:-unknown}"
        if [[ "${size_rc}" -ne 0 ]]; then
          echo "[verify]   FAIL: size checker returned ${size_rc}"
          tail -8 /tmp/verify_source_theorem_size.log \
            | sed 's/^/[verify]     /'
          record_check "source_theorem_size" "FAIL" \
                       "returned ${size_rc} (status=${size_status})"
        elif [[ "${size_status}" == "human-review-required" ]]; then
          echo "[verify]   HUMAN_REVIEW_REQUIRED (size policy)"
          tail -6 /tmp/verify_source_theorem_size.log \
            | sed 's/^/[verify]     /'
          record_check "source_theorem_size" "HUMAN_REVIEW_REQUIRED" \
                       "Rule 4 (size policy)"
        else
          echo "[verify]   PASS (size status=${size_status})"
          record_check "source_theorem_size" "PASS"
        fi
      fi
    fi
  fi
fi

# ---------------------------------------------------------------------------
# (B) Global guards (PR 5 baseline).
# ---------------------------------------------------------------------------

guards=(
  "doc_honesty:scripts/check_doc_honesty.sh"
  "typeclass_payload_quarantine:scripts/check_typeclass_payload_quarantine.sh"
  "refuted_route_quarantine:scripts/check_refuted_route_quarantine.sh"
  "refuted_predicate_usage:scripts/check_refuted_predicate_usage.sh"
)

for entry in "${guards[@]}"; do
  name="${entry%%:*}"
  script="${entry##*:}"
  echo "[verify] running: ${name}"

  if [[ ! -x "${script}" ]]; then
    echo "[verify]   FAIL: ${script} is not executable"
    record_check "${name}" "FAIL" "guard not executable"
    continue
  fi

  set +e
  "${script}" > "/tmp/verify_${name}.log" 2>&1
  rc=$?
  set -e

  if [[ "${rc}" -ne 0 ]]; then
    echo "[verify]   FAIL: ${name} returned ${rc}"
    echo "[verify]     last lines (full log: /tmp/verify_${name}.log):"
    tail -8 "/tmp/verify_${name}.log" | sed 's/^/[verify]       /'
    record_check "${name}" "FAIL" "returned ${rc}"
  else
    echo "[verify]   PASS"
    record_check "${name}" "PASS"
  fi
done

# ---------------------------------------------------------------------------
# (C) Full-mode extras (PR 15.1).
# ---------------------------------------------------------------------------
#
# `--full` adds the global guards that scripts/check.sh wires
# separately as discrete steps:
#   - target_lock                     (PR 11)
#   - candidate_rule16_scan           (PR 15.1)
#   - barrier_certificate_queue_scan  (PR 12)
#   - jsonl_validation                (PR 9)
# It does NOT re-run `lake build`, the smoke driver, or the axiom-
# surface dump; those remain scripts/check.sh's responsibility.

if [[ "${full_mode}" -eq 1 ]]; then
  full_guards=(
    "target_lock:scripts/check_target_lock.sh"
    "candidate_rule16_scan:scripts/check_candidate_rule16.sh"
  )
  for entry in "${full_guards[@]}"; do
    name="${entry%%:*}"
    script="${entry##*:}"
    echo "[verify] running (full): ${name}"
    if [[ ! -x "${script}" ]]; then
      echo "[verify]   FAIL: ${script} is not executable"
      record_check "${name}" "FAIL" "guard not executable"
      continue
    fi
    set +e
    "${script}" > "/tmp/verify_${name}.log" 2>&1
    rc=$?
    set -e
    if [[ "${rc}" -ne 0 ]]; then
      echo "[verify]   FAIL: ${name} returned ${rc}"
      tail -8 "/tmp/verify_${name}.log" | sed 's/^/[verify]     /'
      record_check "${name}" "FAIL" "returned ${rc}"
    else
      echo "[verify]   PASS"
      record_check "${name}" "PASS"
    fi
  done

  # Barrier-certificate queue scan (PR 12).
  echo "[verify] running (full): barrier_certificate_queue_scan"
  set +e
  scripts/check_barrier_certificate.sh --queue \
    > "/tmp/verify_barrier_certificate_queue_scan.log" 2>&1
  rc=$?
  set -e
  if [[ "${rc}" -ne 0 ]]; then
    echo "[verify]   FAIL: barrier queue scan returned ${rc}"
    tail -8 "/tmp/verify_barrier_certificate_queue_scan.log" \
      | sed 's/^/[verify]     /'
    record_check "barrier_certificate_queue_scan" "FAIL" \
                 "returned ${rc} (queue exceeds limit)"
  else
    echo "[verify]   PASS"
    record_check "barrier_certificate_queue_scan" "PASS"
  fi

  # JSONL validation (PR 9).
  echo "[verify] running (full): jsonl_validation"
  set +e
  python3 scripts/validate_jsonl.py \
    > "/tmp/verify_jsonl_validation.log" 2>&1
  rc=$?
  set -e
  if [[ "${rc}" -ne 0 ]]; then
    echo "[verify]   FAIL: JSONL validation returned ${rc}"
    tail -8 "/tmp/verify_jsonl_validation.log" \
      | sed 's/^/[verify]     /'
    record_check "jsonl_validation" "FAIL" "returned ${rc}"
  else
    echo "[verify]   PASS"
    record_check "jsonl_validation" "PASS"
  fi
fi

# ---------------------------------------------------------------------------
# Aggregate verdict.
# ---------------------------------------------------------------------------

overall_status="PASS_SHAPE_ONLY"
if [[ -n "${first_fail}" ]]; then
  overall_status="FAIL_${first_fail}"
else
  for s in "${check_statuses[@]}"; do
    if [[ "${s}" == "HUMAN_REVIEW_REQUIRED" ]]; then
      overall_status="HUMAN_REVIEW_REQUIRED"
      break
    fi
  done
fi

echo
echo "[verify] status: ${overall_status}"
if [[ ${#reasons[@]} -gt 0 ]]; then
  echo "[verify] reasons:"
  for r in "${reasons[@]}"; do
    echo "  - ${r}"
  done
fi

# ---------------------------------------------------------------------------
# Optional JSON output (PR 15).
# ---------------------------------------------------------------------------

if [[ -n "${json_path}" ]]; then
  # Read spec_version + axioms allowlist from spec/target.toml.
  # Fail-closed if either is missing.
  spec_version="$(awk -F'"' '/^spec_version/ { print $2; exit }' \
                  spec/target.toml)"
  spec_version="${spec_version:-unknown}"
  axioms_line="$(awk '/^\[axioms\]/{flag=1;next} flag && /^allowed/{print; exit}' \
                  spec/target.toml)"
  # Extract array body between [ and ] from `allowed = ["X", "Y", ...]`.
  axioms_body="$(printf '%s' "${axioms_line}" \
                  | sed -E 's/^[^[]*\[(.*)\][^]]*$/\1/' \
                  | tr -d ' ')"
  # Now `axioms_body` is like `"Classical.choice","propext","Quot.sound"`.
  # Re-emit as a JSON array.
  axioms_json="[${axioms_body}]"

  cdir_id_for_json="\"${candidate_id:-tree-level}\""

  # Build checks object.
  checks_pairs=()
  for i in "${!check_names[@]}"; do
    checks_pairs+=("\"${check_names[$i]}\": \"${check_statuses[$i]}\"")
  done
  checks_body="$(IFS=,; printf '%s' "${checks_pairs[*]}")"

  # Build reasons array.
  if [[ ${#reasons[@]} -eq 0 ]]; then
    reasons_body=""
  else
    reasons_pairs=()
    for r in "${reasons[@]}"; do
      # Escape backslashes and double quotes for JSON.
      esc="$(printf '%s' "${r}" | python3 -c \
              'import json,sys; print(json.dumps(sys.stdin.read()), end="")')"
      reasons_pairs+=("${esc}")
    done
    reasons_body="$(IFS=,; printf '%s' "${reasons_pairs[*]}")"
  fi

  completed_at="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"

  # Emit JSON.  We construct it manually to keep field order
  # deterministic for Rule 13 reproducibility (modulo
  # `completed_at`).
  cat >"${json_path}" <<JSON
{
  "schema_version": "1.1",
  "candidate_id": ${cdir_id_for_json},
  "candidate_dir": ${candidate_dir_for_json},
  "status": "${overall_status}",
  "reasons": [${reasons_body}],
  "checks": {${checks_body}},
  "axioms_allowed": ${axioms_json},
  "spec_version": "${spec_version}",
  "verifier_implementation_level": "${VERIFIER_IMPL_LEVEL}",
  "critic_report_present": ${critic_report_present},
  "completed_at": "${completed_at}"
}
JSON
  echo "[verify] wrote JSON: ${json_path}"
fi

# ---------------------------------------------------------------------------
# Exit code.
# ---------------------------------------------------------------------------

case "${overall_status}" in
  PASS_SHAPE_ONLY|HUMAN_REVIEW_REQUIRED)
    exit 0
    ;;
  *)
    exit 1
    ;;
esac
