#!/usr/bin/env bash
# verify_candidate.sh — Research Governance v0.1, PR 5 MVP.
#
# Composes the currently-shipped global guards into a single
# verification entrypoint and emits a human-readable status to stdout.
# This is the seed of the Verifier v1 specified in PR 15; PR 8/11/12
# extend it with size-checker, target-lock, and barrier-certificate
# checks, and PR 15 finalises the JSON output schema.
#
# Current MVP semantics:
#
#   - The script does NOT take a candidate-specific path argument.
#     `pnp3/Candidates/` is not yet populated; the global guards
#     already scan the whole tree.  When PR 7 introduces the
#     candidate template and PR 12 adds barrier-certificate checks,
#     this script will gain a `--candidate <dir>` mode.
#
#   - Status semantics:
#       PASS_SHAPE_ONLY  every guard returned 0
#       FAIL             at least one guard returned non-zero
#
#     `PASS_SHAPE_ONLY` is the only positive result this MVP can
#     emit; per `RESEARCH_CONSTITUTION.md` Rule 1, an `accepted`
#     status requires a closed `P_ne_NP_unconditional` term, which
#     this script does NOT verify.
#
#   - Output: human-readable. PR 15 introduces a JSON `result.json`
#     output following `scripts/verifier_result_schema.json`.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

guards=(
  "doc_honesty:scripts/check_doc_honesty.sh"
  "typeclass_payload_quarantine:scripts/check_typeclass_payload_quarantine.sh"
  "refuted_route_quarantine:scripts/check_refuted_route_quarantine.sh"
  "refuted_predicate_usage:scripts/check_refuted_predicate_usage.sh"
)

reasons=()
overall_status="PASS_SHAPE_ONLY"

for entry in "${guards[@]}"; do
  name="${entry%%:*}"
  script="${entry##*:}"
  echo "[verify] running: ${name}"

  if [[ ! -x "${script}" ]]; then
    echo "[verify]   FAIL: ${script} is not executable"
    reasons+=("${name}: guard not executable")
    overall_status="FAIL"
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
    reasons+=("${name}: returned ${rc} (see /tmp/verify_${name}.log)")
    overall_status="FAIL"
  else
    echo "[verify]   PASS"
  fi
done

echo
echo "[verify] status: ${overall_status}"
if [[ ${#reasons[@]} -gt 0 ]]; then
  echo "[verify] reasons:"
  for r in "${reasons[@]}"; do
    echo "  - ${r}"
  done
  exit 1
fi
exit 0
