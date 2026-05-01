#!/usr/bin/env bash
# verify_candidate.sh — Research Governance v0.1, PR 5 + PR 7 MVP.
#
# Composes the currently-shipped global guards into a single
# verification entrypoint and emits a human-readable status to stdout.
# Optional `--candidate <dir>` mode also checks per-candidate file
# layout (per pnp3/Candidates/README.md and RESEARCH_CONSTITUTION.md
# Rule 3).
#
# This is the seed of the Verifier v1 specified in PR 15; PR 8 / 11 /
# 12 extend it with size-checker, target-lock, and barrier-
# certificate checks, and PR 15 finalises the JSON output schema.
#
# Status semantics (current MVP):
#
#   PASS_SHAPE_ONLY        every shape check and every guard returned 0
#   FAIL_<reason>          at least one check failed
#
# `PASS_SHAPE_ONLY` is the only positive result this MVP can emit;
# per `RESEARCH_CONSTITUTION.md` Rule 1, an `accepted` status
# requires a closed `P_ne_NP_unconditional` term, which this script
# does NOT verify.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

usage() {
  cat <<USAGE
Usage: scripts/verify_candidate.sh [--candidate <dir>]

  --candidate <dir>   Optional path (relative to repo root) to a
                      candidate directory; the verifier additionally
                      checks the Rule 3 file layout (proof.lean,
                      manifest.toml, sketch.md, barrier_certificate.md,
                      self_attack.md).

  Without --candidate, the verifier runs the four currently-shipped
  global guards and reports tree-level status only.
USAGE
}

candidate_dir=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate)
      shift
      [[ $# -gt 0 ]] || { usage >&2; exit 2; }
      candidate_dir="$1"
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

reasons=()
overall_status="PASS_SHAPE_ONLY"

# ---------------------------------------------------------------------------
# (A) Optional candidate-shape check (PR 7).
# ---------------------------------------------------------------------------

if [[ -n "${candidate_dir}" ]]; then
  echo "[verify] candidate-shape check: ${candidate_dir}"
  if [[ ! -d "${candidate_dir}" ]]; then
    echo "[verify]   FAIL: candidate directory does not exist"
    reasons+=("candidate-shape: missing directory ${candidate_dir}")
    overall_status="FAIL"
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
      reasons+=("candidate-shape: missing ${missing[*]}")
      overall_status="FAIL"
    else
      echo "[verify]   PASS (all 5 required files present)"
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

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

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
