#!/usr/bin/env bash
# Candidate kernel-elaboration check — Research Governance v0.1, PR 15.2.
#
# Closes the Layer-3 gap identified by the v0.1 Machine Revalidation
# Review: candidate `proof.lean` files were never elaborated through
# the Lean kernel, so type errors and `sorry`/`admit` were silently
# accepted by `verify_candidate.sh`.
#
# Usage:
#
#   scripts/check_candidate_kernel.sh <candidate-dir>
#       Directory mode: looks for `<candidate-dir>/proof.lean` and
#       elaborates it through `lake env lean`.
#
#   scripts/check_candidate_kernel.sh --probe <file>
#       Probe mode: elaborates a standalone `<file>` (used by smoke
#       probes that stage a single .lean file outside any candidate
#       directory).
#
# Exit codes (Plan v0.2.1 + Machine Revalidation):
#   0   `status=ok`        : `lake env lean` succeeded with no errors,
#                            no `sorry`, no `admit`.
#   1   `status=kernel-error`     : lake env lean exited non-zero.
#   1   `status=sorry-admit`      : output mentions `uses 'sorry'` /
#                                   `uses 'admit'`.
#   1   `status=elaboration-error`: output contains `error:` lines
#                                   even though lake's exit code was
#                                   masked by something else.
#   1   `status=missing-proof`    : proof.lean / probe file absent.
#   2   misuse                    : wrong argument count.
# 127   missing toolchain         : `lake` not on PATH.
#
# Output markers (consumed by `scripts/run_smoke_probes.sh` and
# `scripts/verify_candidate.sh`):
#
#   [kernel] candidate=<dir-or-file>
#   [kernel] running: lake env lean <file>
#   [kernel] status=<ok|kernel-error|sorry-admit|elaboration-error|missing-proof>
#
# Limitations (acceptable for PR 15.2 MVP):
#
#   * Imports must already be built into `.lake/build/lib/lean/`.
#     The verifier is intended to run after `lake build PnP3 Pnp4`,
#     so this is fine in CI.  Standalone runs of this script outside
#     CI need a recent `lake build` first.
#   * Module path of the elaborated file is not enforced; the
#     candidate may use any namespace.  This is fine because the
#     kernel still rejects ill-typed terms.
#   * Probe mode is stateless: a single .lean file is elaborated in
#     isolation; no candidate-shape / manifest checks.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <candidate-dir> | --probe <file>" >&2
  exit 2
fi

mode="dir"
target=""
case "$1" in
  --probe)
    [[ $# -eq 2 ]] || { echo "usage: $0 --probe <file>" >&2; exit 2; }
    mode="probe"
    target="$2"
    ;;
  *)
    [[ $# -eq 1 ]] || { echo "usage: $0 <candidate-dir>" >&2; exit 2; }
    target="$1"
    ;;
esac

if ! command -v lake >/dev/null 2>&1; then
  echo "[kernel] Missing required dependency: lake (Lean toolchain)." >&2
  exit 127
fi

# Resolve proof file.
proof_file=""
if [[ "${mode}" == "dir" ]]; then
  if [[ ! -d "${target}" ]]; then
    echo "[kernel] candidate=${target}"
    echo "[kernel] FAIL: candidate directory not found"
    echo "[kernel] status=missing-proof"
    exit 1
  fi
  proof_file="${target}/proof.lean"
else
  if [[ ! -f "${target}" ]]; then
    echo "[kernel] candidate=${target}"
    echo "[kernel] FAIL: probe file not found"
    echo "[kernel] status=missing-proof"
    exit 1
  fi
  proof_file="${target}"
fi

if [[ ! -f "${proof_file}" ]]; then
  echo "[kernel] candidate=${target}"
  echo "[kernel] FAIL: missing ${proof_file}"
  echo "[kernel] status=missing-proof"
  exit 1
fi

echo "[kernel] candidate=${target}"
echo "[kernel] running: lake env lean ${proof_file}"

log_file="/tmp/check_candidate_kernel.log"

set +e
lake env lean "${proof_file}" > "${log_file}" 2>&1
rc=$?
set -e

# Lake's exit code is the primary signal; non-zero means the kernel
# rejected the file outright.
if [[ "${rc}" -ne 0 ]]; then
  echo "[kernel] FAIL: lake env lean exited ${rc}"
  echo "[kernel] last lines (full log: ${log_file}):"
  tail -10 "${log_file}" | sed 's/^/[kernel]   /'
  echo "[kernel] status=kernel-error"
  exit 1
fi

# `sorry` / `admit` produce *warnings*, not errors, so lake exits 0.
# We catch them explicitly.
if grep -q "uses 'sorry'\|uses 'admit'" "${log_file}"; then
  echo "[kernel] FAIL: candidate proof.lean uses sorry or admit"
  grep "uses 'sorry'\|uses 'admit'" "${log_file}" | head -5 \
    | sed 's/^/[kernel]   /'
  echo "[kernel] status=sorry-admit"
  exit 1
fi

# Defensive: scan for any line beginning with `error:` even though lake
# returned 0 (e.g. linker errors masked by tee).
if grep -q "^error:" "${log_file}" \
   || grep -qE "^[^[:space:]]+:[0-9]+:[0-9]+: error:" "${log_file}"; then
  echo "[kernel] FAIL: lean reported errors despite zero exit code"
  grep -E "^error:|: error:" "${log_file}" | head -5 \
    | sed 's/^/[kernel]   /'
  echo "[kernel] status=elaboration-error"
  exit 1
fi

echo "[kernel] status=ok"
exit 0
