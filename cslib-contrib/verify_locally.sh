#!/usr/bin/env bash
# Verify the drafted P/coP/NP layer against a real CSLib checkout.
#
# Why this exists: the sandbox that drafted these files has no path to the actual
# Lean 4 toolchain (leanprover/lean4 is distributed exclusively via GitHub Releases,
# which that session's GitHub access is not scoped to reach) or to CSLib's own repo
# (leanprover/cslib, a different GitHub owner than the one this campaign's sessions
# are scoped to). Every review up to this point was manual, against downloaded
# sources, with no compiler. Run this on a machine with normal internet access to
# get the first real answer: does it actually build?
#
# Needs: git, curl. Installs elan (Lean's toolchain manager) if not already present.
#
#   bash verify_locally.sh [/path/to/scratch/dir]
#
set -euo pipefail

WORKDIR="${1:-$(mktemp -d)}"
CSLIB_DIR="$WORKDIR/cslib"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "==> scratch directory: $WORKDIR"
mkdir -p "$WORKDIR"

if ! command -v elan >/dev/null 2>&1; then
  echo "==> elan not found, installing"
  if command -v apt-get >/dev/null 2>&1 && apt-cache show elan >/dev/null 2>&1; then
    sudo apt-get update && sudo apt-get install -y elan
  else
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
    source "$HOME/.elan/env"
  fi
else
  echo "==> elan already present: $(elan --version)"
fi

echo "==> cloning leanprover/cslib (shallow, main)"
git clone --depth 1 https://github.com/leanprover/cslib "$CSLIB_DIR"
cd "$CSLIB_DIR"

echo "==> pinned toolchain: $(cat lean-toolchain)"
elan toolchain install "$(cat lean-toolchain | sed 's/^leanprover\///')" || true

echo "==> copying the drafted files into place"
cp "$HERE/lean/Cslib/Foundations/Data/BiTape.lean" \
   "$CSLIB_DIR/Cslib/Foundations/Data/BiTape.lean"
cp "$HERE/lean/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean" \
   "$CSLIB_DIR/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean"
mkdir -p "$CSLIB_DIR/Cslib/Computability/Complexity"
cp "$HERE/lean/Cslib/Computability/Complexity/Defs.lean" \
   "$CSLIB_DIR/Cslib/Computability/Complexity/Defs.lean"
cp "$HERE/lean/Cslib/Computability/Complexity/Relabel.lean" \
   "$CSLIB_DIR/Cslib/Computability/Complexity/Relabel.lean"
cp "$HERE/lean/Cslib/Computability/Complexity/WellFormed.lean" \
   "$CSLIB_DIR/Cslib/Computability/Complexity/WellFormed.lean"
cp "$HERE/lean/Cslib/Computability/Complexity/NP.lean" \
   "$CSLIB_DIR/Cslib/Computability/Complexity/NP.lean"

echo "==> registering new files in Cslib.lean"
lake exe mk_all || echo "WARN: mk_all failed — you may need to add the four new Complexity/*.lean imports to Cslib.lean by hand"

echo "==> fetching precompiled Mathlib cache (this is the slow step if it misses; expect several GB)"
lake exe cache get

STATUS=0
run_step() {
  local name="$1"; shift
  echo
  echo "==> $name: $*"
  if "$@"; then
    echo "PASS: $name"
  else
    echo "FAIL: $name"
    STATUS=1
  fi
}

run_step "build"      lake build
run_step "test"       lake test
run_step "lint"       lake lint
run_step "lint-style" lake exe lint-style --fix
run_step "mk_all"     lake exe mk_all
run_step "shake"      lake shake --add-public --keep-implied --keep-prefix --fix

echo
if [ "$STATUS" -eq 0 ]; then
  echo "=================================================="
  echo " ALL CHECKS PASSED — safe to open PR-1 per STATUS.md"
  echo "=================================================="
else
  echo "=================================================="
  echo " SOME CHECKS FAILED — fix the reported errors before opening any PR."
  echo " The manual review in STATUS.md/RISKS_*.md lists the specific spots"
  echo " most likely to need adjustment; start there."
  echo "=================================================="
fi
echo "Checked out at: $CSLIB_DIR"
exit "$STATUS"
