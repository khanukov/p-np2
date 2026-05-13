#!/usr/bin/env bash
# Barrier-certificate checker — Research Governance v0.1, PR 12.
#
# Two modes:
#
#   scripts/check_barrier_certificate.sh <candidate-dir>
#       Per-candidate check.  Verifies that the candidate ships a
#       `barrier_certificate.md` and that its `manifest.toml`
#       declares all required `[barriers]` keys.  Emits a status
#       suitable for `scripts/verify_candidate.sh` to consume.
#
#   scripts/check_barrier_certificate.sh --queue
#       Queue-size mode (run from `scripts/check.sh`).  Walks every
#       `pnp3/Candidates/<*>/<*>/manifest.toml` (skipping the
#       `_template/` directory and any path with a leading `_`) and
#       counts how many candidates currently have
#       `[barriers].natural_proof = "unknown-human-review"`.  Fails
#       if the count exceeds
#       `spec/target.toml::[human_review].candidate_queue_limit`
#       (currently 3).
#
# SLA expiry (>14 days, per
# `spec/target.toml::[human_review].candidate_sla_days`) is NOT
# implemented in PR 12.  It requires a per-candidate intake
# timestamp that the manifest does not yet carry.  Adding the
# timestamp + an SLA scan is a follow-up task.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v jq >/dev/null 2>&1; then
  echo "[barrier] Missing required dependency: jq." >&2
  exit 127
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "[barrier] Missing required dependency: python3." >&2
  exit 127
fi

queue_limit=3   # spec/target.toml::[human_review].candidate_queue_limit

required_barrier_keys=(
  "relativization"
  "natural_proof"
  "algebrization"
  "hardwiring_checked"
  "collapse_not_contradiction_checked"
)

# ---------------------------------------------------------------------------
# Per-candidate mode.
# ---------------------------------------------------------------------------

run_per_candidate() {
  local candidate_dir="$1"

  echo "[barrier] candidate=${candidate_dir}"

  if [[ ! -d "${candidate_dir}" ]]; then
    echo "[barrier] FAIL: candidate directory not found"
    exit 1
  fi

  local cert_file="${candidate_dir}/barrier_certificate.md"
  if [[ ! -f "${cert_file}" ]]; then
    echo "[barrier] FAIL: missing ${cert_file}"
    echo "status=missing-barrier-certificate"
    exit 1
  fi

  local manifest_file="${candidate_dir}/manifest.toml"
  if [[ ! -f "${manifest_file}" ]]; then
    echo "[barrier] FAIL: missing ${manifest_file}"
    echo "status=missing-manifest"
    exit 1
  fi

  local json
  if ! json="$(python3 scripts/parse_manifest.py "${candidate_dir}")"; then
    echo "[barrier] FAIL: cannot parse ${manifest_file}"
    echo "status=manifest-parse-error"
    exit 1
  fi
  if echo "${json}" | jq -e '.error' >/dev/null 2>&1; then
    echo "[barrier] FAIL: manifest parser reports an error"
    echo "${json}"
    exit 1
  fi

  local missing=()
  for key in "${required_barrier_keys[@]}"; do
    if ! echo "${json}" \
         | jq -e --arg k "${key}" \
              '.barriers | has($k)' >/dev/null 2>&1; then
      missing+=("${key}")
    fi
  done
  if [[ ${#missing[@]} -gt 0 ]]; then
    echo "[barrier] FAIL: manifest [barriers] missing keys: ${missing[*]}"
    echo "status=manifest-incomplete"
    exit 1
  fi

  local np
  np="$(echo "${json}" | jq -r '.barriers.natural_proof')"
  local rl
  rl="$(echo "${json}" | jq -r '.barriers.relativization')"
  local al
  al="$(echo "${json}" | jq -r '.barriers.algebrization')"

  echo "[barrier] manifest [barriers]:"
  echo "[barrier]   natural_proof  = ${np}"
  echo "[barrier]   relativization = ${rl}"
  echo "[barrier]   algebrization  = ${al}"

  local hr=0
  if [[ "${np}" == "unknown-human-review" \
        || "${rl}" == "unknown-human-review" \
        || "${al}" == "unknown-human-review" ]]; then
    hr=1
  fi
  if [[ "${hr}" -eq 1 ]]; then
    echo "[barrier] status=human-review-required"
  else
    echo "[barrier] status=ok"
  fi
  echo "[barrier] OK"
  # Per Plan v0.2.1 §"PR 12" AC: human-review-required is NOT an
  # auto-reject. Both `ok` and `human-review-required` exit 0.
  exit 0
}

# ---------------------------------------------------------------------------
# Queue-size mode.
# ---------------------------------------------------------------------------

run_queue_scan() {
  local count=0
  local hr_candidates=()

  shopt -s nullglob
  for dir in pnp3/Candidates/*/; do
    local base
    base="$(basename "${dir}")"
    # Skip the underscore-prefixed template + any future scratch dirs.
    case "${base}" in
      _*) continue ;;
    esac
    if [[ ! -f "${dir}manifest.toml" ]]; then
      continue
    fi
    local json
    json="$(python3 scripts/parse_manifest.py "${dir%/}" 2>/dev/null || true)"
    if [[ -z "${json}" ]] || echo "${json}" | jq -e '.error' >/dev/null 2>&1; then
      continue
    fi
    local np rl al
    np="$(echo "${json}" | jq -r '.barriers.natural_proof  // "ok"')"
    rl="$(echo "${json}" | jq -r '.barriers.relativization // "ok"')"
    al="$(echo "${json}" | jq -r '.barriers.algebrization  // "ok"')"
    if [[ "${np}" == "unknown-human-review" \
          || "${rl}" == "unknown-human-review" \
          || "${al}" == "unknown-human-review" ]]; then
      count=$((count + 1))
      hr_candidates+=("${dir}")
    fi
  done

  echo "[barrier] queue scan:"
  echo "[barrier]   open human-review-required candidates: ${count}"
  echo "[barrier]   queue limit                         : ${queue_limit}"
  if [[ "${count}" -gt 0 ]]; then
    echo "[barrier]   members:"
    for c in "${hr_candidates[@]}"; do
      echo "[barrier]     ${c}"
    done
  fi
  if [[ "${count}" -gt "${queue_limit}" ]]; then
    echo "[barrier] FAIL: human-review queue exceeds limit ${queue_limit}"
    echo "[barrier]   See spec/target.toml::[human_review].candidate_queue_limit"
    echo "[barrier]   and RESEARCH_CONSTITUTION.md Rule 7."
    exit 1
  fi
  echo "[barrier] OK"
  exit 0
}

# ---------------------------------------------------------------------------
# Argument dispatch.
# ---------------------------------------------------------------------------

if [[ $# -eq 0 ]]; then
  echo "usage: $0 <candidate-dir> | --queue" >&2
  exit 2
fi

case "$1" in
  --queue)
    run_queue_scan
    ;;
  *)
    run_per_candidate "$1"
    ;;
esac
