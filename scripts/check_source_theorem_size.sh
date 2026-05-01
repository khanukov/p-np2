#!/usr/bin/env bash
# SourceTheorem size checker (MVP) — Research Governance v0.1, PR 8.
#
# Implements the size-policy check from
# `spec/source_theorem_size_policy.md` at MVP_GREP_FALLBACK level: no
# Lean AST, no `pp.all` rendering, no transitive-def BFS.  The MVP is
# heuristic but useful as a regression watchdog; PR 15 ships the full
# AST-aware version.
#
# Usage:
#
#   scripts/check_source_theorem_size.sh <candidate-dir>
#
# Inputs:
#   <candidate-dir>/proof.lean          Lean source (required)
#   <candidate-dir>/manifest.toml       must declare
#                                       [source].theorem and [source].bridge
#                                       (required)
#
# Outputs (stdout):
#   k_stmt_actual=<n>  k_stmt_limit=40
#   k_exp_actual=<n>   k_exp_limit=200
#   status=<ok|human-review-required|refuted-import|missing-source-theorem>
#
# Exit codes (Plan v0.2.1 §"PR 8" acceptance criteria):
#   0   `ok` and `human-review-required` (size policy violation is NOT
#       an auto-reject per Rule 4)
#   1   `refuted-import` (delegated by name-grep), missing source
#       theorem, or any other hard error.
#
# MVP semantics (heuristic):
#   - K_stmt: count non-blank, non-comment lines from the line that
#     begins `theorem <source.theorem>` or `def <source.theorem>` or
#     `structure <source.theorem>` to the FIRST subsequent line
#     containing `:=` or `where` (inclusive). For one-line `def Name :
#     Prop := True`, this is 1 line.
#   - K_exp: count of all non-blank, non-comment lines in the entire
#     candidate `proof.lean` after the awk comment-stripper. This is
#     a loose upper bound; PR 15 replaces it with proper BFS.
#
# Refuted-import detection: this script does NOT duplicate
# `scripts/check_refuted_predicate_usage.sh`. PR 4a's guard already
# hard-fails when a refuted-predicate name appears in
# `pnp3/Candidates/`. The verifier (`scripts/verify_candidate.sh`)
# composes the two checks and reports `refuted-import` when the PR 4a
# guard fires inside a candidate.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <candidate-dir>" >&2
  exit 2
fi

candidate_dir="$1"
proof_file="${candidate_dir}/proof.lean"
manifest_file="${candidate_dir}/manifest.toml"

if [[ ! -f "${proof_file}" ]]; then
  echo "[size] FAIL: missing ${proof_file}"
  exit 1
fi
if [[ ! -f "${manifest_file}" ]]; then
  echo "[size] FAIL: missing ${manifest_file}"
  exit 1
fi

# ---------------------------------------------------------------------------
# Read source.theorem from manifest.toml (TOML-light parser).
# ---------------------------------------------------------------------------
#
# Looks for the line `theorem = "..."` inside the `[source]` table.
# Tolerant of arbitrary whitespace.

source_theorem="$(awk '
  /^\[/ { in_source = ($0 ~ /^\[source\]/) ? 1 : 0; next }
  in_source && /^[[:space:]]*theorem[[:space:]]*=/ {
    sub(/^[^"]*"/, "")
    sub(/".*$/, "")
    print
    exit
  }
' "${manifest_file}")"

if [[ -z "${source_theorem}" ]]; then
  echo "[size] FAIL: manifest.toml has no [source].theorem entry"
  exit 1
fi

# ---------------------------------------------------------------------------
# Strip Lean comments and produce a line-aligned view of proof.lean.
# ---------------------------------------------------------------------------
#
# Same awk stripper used by `scripts/check_refuted_predicate_usage.sh`.
# `/- ... -/` block comments are removed; `--` line comments are
# stripped after the block-comment pass.

stripped="$(mktemp)"
trap 'rm -f "${stripped}"' EXIT

awk '
  BEGIN { in_block = 0 }
  {
    line = $0
    out  = ""
    i    = 1
    n    = length(line)
    while (i <= n) {
      if (in_block) {
        j = index(substr(line, i), "-/")
        if (j == 0) { i = n + 1 }
        else        { in_block = 0; i = i + j + 1 }
      } else {
        j = index(substr(line, i), "/-")
        if (j == 0) {
          out = out substr(line, i)
          i = n + 1
        } else {
          out = out substr(line, i, j - 1)
          in_block = 1
          i = i + j + 1
        }
      }
    }
    k = index(out, "--")
    if (k > 0) out = substr(out, 1, k - 1)
    print out
  }
' "${proof_file}" > "${stripped}"

# ---------------------------------------------------------------------------
# K_exp_actual — non-blank, non-comment lines.
# ---------------------------------------------------------------------------

k_exp_actual="$(awk 'NF > 0 { c++ } END { print c+0 }' "${stripped}")"

# ---------------------------------------------------------------------------
# K_stmt_actual — find the source theorem block.
# ---------------------------------------------------------------------------
#
# Match `theorem <name>`, `def <name>`, or `structure <name>` at the
# start of a non-blank line. Then continue until the FIRST line
# containing `:=` or `where` (inclusive). One-line definitions like
# `def F : Prop := True` count as 1.

k_stmt_actual="$(awk -v target="${source_theorem}" '
  BEGIN { in_stmt = 0; lines = 0; found = 0 }
  function trim(s) { sub(/^[[:space:]]+/, "", s); sub(/[[:space:]]+$/, "", s); return s }
  {
    line = $0
    if (!in_stmt) {
      # Look for opening declaration of the target name.
      pattern = "^[[:space:]]*(theorem|def|noncomputable[[:space:]]+def|abbrev|structure|inductive|class)[[:space:]]+" target "([[:space:]:({]|$)"
      if (match(line, pattern)) {
        in_stmt = 1
        found  = 1
        lines  = 1
        if (line ~ /:=/ || line ~ /where[[:space:]]*$/ || line ~ /where[[:space:]]*--/) {
          print lines
          in_stmt = 0
          exit
        }
      }
      next
    }
    # Inside the statement block.
    if (trim(line) != "") {
      lines++
    }
    if (line ~ /:=/ || line ~ /where[[:space:]]*$/) {
      print lines
      in_stmt = 0
      exit
    }
    # Heuristic terminator: a top-level `theorem`, `def`, `end`, or
    # `namespace` line ends the block before we found `:=`.
    if (line ~ /^(theorem|def|abbrev|structure|inductive|class|namespace|end)[[:space:]]/) {
      print lines - 1
      in_stmt = 0
      exit
    }
  }
  END {
    if (!found) {
      print -1
    } else if (in_stmt) {
      # Reached EOF without hitting `:=`/`where`/another decl.
      # Report the line count for a best-effort upper bound.
      print lines
    }
    # If a `print lines; exit` already fired in the loop, awk passes
    # through this block; `in_stmt` was reset to 0 there to keep the
    # END branch silent.
  }
' "${stripped}")"

if [[ "${k_stmt_actual}" == "-1" || -z "${k_stmt_actual}" ]]; then
  echo "[size] FAIL: source theorem '${source_theorem}' not found in ${proof_file}"
  echo "status=missing-source-theorem"
  exit 1
fi

# ---------------------------------------------------------------------------
# Compare against limits from spec/target.toml::[source_theorem_size].
# ---------------------------------------------------------------------------

k_stmt_limit=40
k_exp_limit=200

status="ok"
if [[ "${k_stmt_actual}" -gt "${k_stmt_limit}" \
      || "${k_exp_actual}" -gt "${k_exp_limit}" ]]; then
  status="human-review-required"
fi

echo "[size] candidate=${candidate_dir}"
echo "[size] source_theorem=${source_theorem}"
echo "[size] k_stmt_actual=${k_stmt_actual} k_stmt_limit=${k_stmt_limit}"
echo "[size] k_exp_actual=${k_exp_actual} k_exp_limit=${k_exp_limit}"
echo "[size] status=${status}"
echo "[size] implementation_level=MVP_GREP_FALLBACK"

# Plan v0.2.1 §"PR 8" AC: status `human-review-required` is NOT an
# auto-reject. Both `ok` and `human-review-required` exit 0.
exit 0
