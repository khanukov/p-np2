#!/usr/bin/env bash
# Negative control for the frozen TMVerifier tree guard.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CHECKER="${ROOT_DIR}/scripts/check_tmverifier_freeze.sh"
TARGET="${ROOT_DIR}/pnp3/Complexity/TMVerifier/TuringToolkit/GateNBodyRound.lean"

if [[ ! -x "${CHECKER}" ]]; then
  echo "Missing executable freeze checker: ${CHECKER}" >&2
  exit 1
fi

"${CHECKER}"

backup="$(mktemp)"
cp "${TARGET}" "${backup}"
restore() {
  cp "${backup}" "${TARGET}"
  rm -f "${backup}"
}
trap restore EXIT

printf '\n-- freeze negative control\n' >>"${TARGET}"
if "${CHECKER}" >/tmp/tmverifier_freeze_negative.log 2>&1; then
  echo "Freeze checker accepted a modified TMVerifier source." >&2
  exit 1
fi

restore
trap - EXIT
"${CHECKER}"
echo "[tmverifier-freeze-test] OK"
