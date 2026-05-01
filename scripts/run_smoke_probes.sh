#!/usr/bin/env bash
# Smoke-probe driver — Research Governance v0.1, PR 5.
#
# Executes the cases declared in `bench/SmokeProbe/expected_results.json`:
#
#   - For each `kind = "rejected"` probe:
#       1. copy probe_file → staging_path (a forbidden zone)
#       2. run the named guard
#       3. assert non-zero exit AND log contains expected_log_marker
#       4. remove staging_path
#
#   - For the `kind = "accepted_shape_only"` probe:
#       1. (probe lives permanently in bench/SmokeProbe/; no staging)
#       2. run every guard listed in `guards_to_run_clean`
#       3. assert each returns 0
#
# Cleanup: a bash EXIT trap removes any staged probe file that was
# left behind, even on early failure.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[smoke] Missing required dependency: rg (ripgrep)." >&2
  exit 127
fi
if ! command -v jq >/dev/null 2>&1; then
  echo "[smoke] Missing required dependency: jq." >&2
  exit 127
fi

probes_json="bench/SmokeProbe/expected_results.json"
if [[ ! -f "${probes_json}" ]]; then
  echo "[smoke] Missing ${probes_json}" >&2
  exit 1
fi

# Cleanup trap: remove any staged file we created.
declare -a staged_files=()
cleanup() {
  for f in "${staged_files[@]:-}"; do
    [[ -n "${f}" ]] && rm -f "${f}"
  done
}
trap cleanup EXIT

total=0
passed=0
failed=0
fail_log=()

# ---------------------------------------------------------------------------
# Rejected probes.
# ---------------------------------------------------------------------------

while IFS= read -r line; do
  total=$((total + 1))
  case_id="$(echo "${line}" | jq -r '.case_id')"
  probe_file="$(echo "${line}" | jq -r '.probe_file')"
  staging_path="$(echo "${line}" | jq -r '.staging_path')"
  guard="$(echo "${line}" | jq -r '.guard')"
  expected_marker="$(echo "${line}" | jq -r '.expected_log_marker')"

  echo "[smoke] running rejected probe: ${case_id}"

  if [[ ! -f "${probe_file}" ]]; then
    echo "[smoke]   FAIL: missing probe file ${probe_file}"
    failed=$((failed + 1))
    fail_log+=("${case_id}: missing probe file")
    continue
  fi
  if [[ ! -x "${guard}" ]]; then
    echo "[smoke]   FAIL: guard ${guard} is not executable"
    failed=$((failed + 1))
    fail_log+=("${case_id}: guard not executable")
    continue
  fi

  cp "${probe_file}" "${staging_path}"
  staged_files+=("${staging_path}")

  set +e
  guard_output="$("${guard}" 2>&1)"
  guard_exit=$?
  set -e

  rm -f "${staging_path}"

  if [[ "${guard_exit}" -ne 0 \
        && "${guard_output}" == *"${expected_marker}"* ]]; then
    echo "[smoke]   PASS (guard exit=${guard_exit}, marker matched)"
    passed=$((passed + 1))
  else
    echo "[smoke]   FAIL"
    echo "[smoke]     expected: non-zero exit AND marker '${expected_marker}'"
    echo "[smoke]     actual:   exit=${guard_exit}"
    echo "[smoke]     last output lines:"
    echo "${guard_output}" | tail -8 | sed 's/^/[smoke]       /'
    failed=$((failed + 1))
    fail_log+=("${case_id}: marker not matched (exit=${guard_exit})")
  fi
done < <(jq -c '.probes[] | select(.kind == "rejected")' "${probes_json}")

# ---------------------------------------------------------------------------
# Accepted-shape-only probe.
# ---------------------------------------------------------------------------

while IFS= read -r line; do
  total=$((total + 1))
  case_id="$(echo "${line}" | jq -r '.case_id')"
  probe_file="$(echo "${line}" | jq -r '.probe_file')"
  expected_status="$(echo "${line}" | jq -r '.expected_status')"

  echo "[smoke] running accepted probe: ${case_id} (expected ${expected_status})"

  if [[ ! -f "${probe_file}" ]]; then
    echo "[smoke]   FAIL: missing probe file ${probe_file}"
    failed=$((failed + 1))
    fail_log+=("${case_id}: missing probe file")
    continue
  fi

  all_clean=1
  while IFS= read -r guard; do
    if [[ ! -x "${guard}" ]]; then
      echo "[smoke]   FAIL: guard ${guard} is not executable"
      all_clean=0
      continue
    fi
    set +e
    "${guard}" > "/tmp/smoke_${case_id}_$(basename "${guard}" .sh).log" 2>&1
    rc=$?
    set -e
    if [[ "${rc}" -ne 0 ]]; then
      echo "[smoke]   FAIL: ${guard} returned ${rc} on tree containing ${probe_file}"
      tail -8 "/tmp/smoke_${case_id}_$(basename "${guard}" .sh).log" \
        | sed 's/^/[smoke]     /'
      all_clean=0
    fi
  done < <(echo "${line}" | jq -r '.guards_to_run_clean[]')

  if [[ "${all_clean}" -eq 1 ]]; then
    echo "[smoke]   PASS_SHAPE_ONLY"
    passed=$((passed + 1))
  else
    failed=$((failed + 1))
    fail_log+=("${case_id}: not all guards clean")
  fi
done < <(jq -c '.probes[] | select(.kind == "accepted_shape_only")' "${probes_json}")

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

echo
echo "[smoke] summary: ${passed}/${total} probes passed"

if [[ "${failed}" -ne 0 ]]; then
  echo "[smoke] failures:"
  for r in "${fail_log[@]:-}"; do
    [[ -n "${r}" ]] && echo "  - ${r}"
  done
  echo
  echo "[smoke] FAIL"
  exit 1
fi

echo "[smoke] OK"
