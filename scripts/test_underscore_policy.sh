#!/usr/bin/env bash
# Underscore-policy smoke for scripts/check_candidate_rule16.sh —
# Research Governance v0.1, Autoresearch MVP-0.1.3.
#
# Asserts the underscore-skip allowlist is exactly `_template`:
#
#   pnp3/Candidates/_template/   → silently skipped (no FAIL)
#   pnp3/Candidates/_evil/       → FAIL with the underscore-policy
#                                  marker
#   pnp3/Candidates/_scratch/    → FAIL likewise
#
# The previous behaviour silently skipped any `_*` directory, which
# allowed a malicious worker to bypass Rule 16 by naming their
# candidate `_evil/`.  This test stages a transient `_evil/` dir
# under `pnp3/Candidates/`, runs the guard, asserts it failed with
# the right marker, and removes the staging dir.
#
# The test does NOT mutate any committed artifact:
# `pnp3/Candidates/_evil/` is created at run start and removed in a
# trap, regardless of pass/fail.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

# Stage path: must be under pnp3/Candidates/ for the guard to scan
# it (the guard hard-codes `candidates_root=pnp3/Candidates`).
STAGE="pnp3/Candidates/_evil_smoke_$$"

cleanup() {
  rm -rf "${STAGE}"
}
trap cleanup EXIT

mkdir -p "${STAGE}"

# Put a deliberately Rule-16-violating Lean stub in the staged dir
# so that, IF the underscore-skip bypass is in effect (the bug we
# fixed), the file would be silently ignored.  With the fix in
# place, the directory itself triggers FAIL before the file is even
# read.
cat >"${STAGE}/proof.lean" <<'LEAN'
-- Synthetic hidden-payload stub.  Should NEVER be reached by the
-- candidate-Rule-16 scan because the dir lives under an
-- underscore-prefixed component that is NOT in the allowlist.
class FakeGapProvider where
  miracle : True
LEAN

fail=0

set +e
output="$(scripts/check_candidate_rule16.sh 2>&1)"
rc=$?
set -e

if [[ "${rc}" -eq 0 ]]; then
  echo "[test_underscore_policy] FAIL: scripts/check_candidate_rule16.sh"
  echo "[test_underscore_policy]   returned 0 with ${STAGE}/ present;"
  echo "[test_underscore_policy]   the underscore-policy guard did not"
  echo "[test_underscore_policy]   detect the bypass."
  echo "${output}"
  fail=1
elif ! grep -q "forbidden underscore-prefixed candidate" \
            <(printf '%s' "${output}"); then
  echo "[test_underscore_policy] FAIL: guard returned non-zero (${rc})"
  echo "[test_underscore_policy]   but the expected marker"
  echo "[test_underscore_policy]   'forbidden underscore-prefixed candidate'"
  echo "[test_underscore_policy]   was missing from its output."
  echo "${output}"
  fail=1
else
  echo "[test_underscore_policy] OK   _evil_smoke_$$ rejected with"\
       "underscore-policy marker"
fi

# Sanity: with the staged dir removed, the guard should pass on the
# baseline tree (which only contains `_template` under
# pnp3/Candidates/).  This catches accidental over-rejection.
rm -rf "${STAGE}"
trap - EXIT

set +e
output2="$(scripts/check_candidate_rule16.sh 2>&1)"
rc2=$?
set -e

if [[ "${rc2}" -ne 0 ]]; then
  echo "[test_underscore_policy] FAIL: baseline tree (with _template"
  echo "[test_underscore_policy]   only) was unexpectedly rejected"
  echo "[test_underscore_policy]   (rc=${rc2}).  Underscore-policy"
  echo "[test_underscore_policy]   over-tightened?"
  echo "${output2}"
  fail=1
else
  echo "[test_underscore_policy] OK   baseline tree accepted"\
       "(_template is allowlisted)"
fi

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[test_underscore_policy] FAIL"
  exit 1
fi

echo "[test_underscore_policy] OK (1 forbidden underscore dir rejected,"\
     "1 allowed underscore dir accepted)"
