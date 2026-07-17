#!/usr/bin/env bash
# Prepare and push the tm1-complexity branch to the khanukov/mathlib4 fork.
# Run this on your own machine (needs: git; GitHub push access to the fork).
#
#   bash prepare_branch.sh
#
# NOTE (2026-07-17): the branch has already been pushed (tm1-complexity,
# single commit authored by Dmitry Khanukov, based on master 2026-07-16).
# This script is kept only as a fallback to recreate it from scratch;
# running it will overwrite nothing (plain push fails on divergence).
set -euo pipefail

FORK="git@github.com:khanukov/mathlib4.git"   # or https://github.com/khanukov/mathlib4.git
BRANCH="tm1-complexity"
RAW="https://raw.githubusercontent.com/khanukov/p-np2/claude/p-vs-np-approaches-q6p57c/mathlib-contrib/TM1Complexity.lean"

workdir=$(mktemp -d)
echo "==> cloning fork (shallow) into $workdir"
git clone --depth 1 "$FORK" "$workdir/mathlib4"
cd "$workdir/mathlib4"
git checkout -b "$BRANCH"

echo "==> adding TM1Complexity.lean"
curl -fsSL -o Mathlib/Computability/TuringMachine/TM1Complexity.lean "$RAW"

echo "==> registering the module in Mathlib.lean"
python3 - <<'EOF'
s = open("Mathlib.lean").read()
old = ("public import Mathlib.Computability.TuringMachine.StackTuringMachine\n"
       "public import Mathlib.Computability.TuringMachine.Tape")
new = ("public import Mathlib.Computability.TuringMachine.StackTuringMachine\n"
       "public import Mathlib.Computability.TuringMachine.TM1Complexity\n"
       "public import Mathlib.Computability.TuringMachine.Tape")
assert old in s, "Mathlib.lean layout changed; insert the import line manually (sorted)"
open("Mathlib.lean", "w").write(s.replace(old, new))
print("registered")
EOF

git add Mathlib/Computability/TuringMachine/TM1Complexity.lean Mathlib.lean
# Commit message follows mathlib's commit conventions
# (https://leanprover-community.github.io/contribute/commit.html):
# imperative mood, lowercase subject, scope = directory without Mathlib/.
git commit --author="Dmitry Khanukov <dmitry@dwelly.group>" \
  -m "feat(Computability/TuringMachine): add step counting and complexity classes P/NP for TM1

Implements the proposal of #35366 for the TM1 model: fuel-based
execution runN with a bridge theorem to the relational semantics
StateTransition.eval, time-bounded decision DecidesInTime, lightweight
polynomial bounds, and the classes InP/InNP with Fintype finite
control. Proves P is contained in NP, and additionally that P is
closed under complement (InP.compl / inP_compl_iff) via the
halt-rewriting transformation Stmt.mapHalt, with zero time overhead."

echo "==> pushing"
git push -u origin "$BRANCH"

echo
echo "Done. Open a PR: https://github.com/khanukov/mathlib4/pull/new/$BRANCH"
echo "PR body: mathlib-contrib/PR_DESCRIPTION.md"
