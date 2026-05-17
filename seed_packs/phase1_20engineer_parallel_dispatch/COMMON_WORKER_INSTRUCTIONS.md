# Common worker instructions — Phase 1 wave 1 synthesis (A11)

You are the **A11 synthesis engineer**. Wave 1 audits (A01–A10) are complete and merged to main. A11 is the only active task: it reads all 10 audit reports and produces an operator-decision memo for wave 2.

Active task ID: **A11 only.**

L01, L02, B01, B02, B03, K01, K02, X01, X02 are **blocked** pending A11 + operator decision. Do not dispatch them.

If you see references in other documents to `E<NN>` IDs, ignore them — they predate the 2026-05-17 plan reduction.

This file is binding. Violations result in operator rejection.

---

## 1. Identity and scope

The active task is **A11**. Don't pick any other task; the deferred task files (L01..L02, B01..B03, K01..K02, X01..X02) exist as record for A11 to read, not for direct dispatch.

Your branch name **must** follow this convention:

```
khanukov/phase1-<ID>-<short-handle>
```

Example: `khanukov/phase1-A07-codex-gpt55` or `khanukov/phase1-X01-claudeopus`.

Your PR title:

```
Phase 1 <ID>: <task title from README.md task list>
```

---

## 2. Required reading (universal)

Before you start:

1. **`RESEARCH_CONSTITUTION.md`** — binding discipline.
2. **`seed_packs/phase1_20engineer_parallel_dispatch/README.md`** — phase overview, dependencies, acceptance criteria.
3. **`seed_packs/phase1_20engineer_parallel_dispatch/AUDIT_2026-05-17_PLAN_REDUCTION.md`** — context for why this wave is reduced.
4. **`seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md`** — context for the broader phase. Read §3 (what was accomplished), §6 (the gap), §11 (honest framing). Full FP3b history is not required.
5. **Your specific task file** at `seed_packs/phase1_20engineer_parallel_dispatch/tasks/<ID>_*.md`.

If your task is X01 (touches Lean):

6. **`pnp3/Complexity/Interfaces.lean`** — trust-root types you must import but never modify.
7. **`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`** — TM model used in the bridge.
8. **`seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_gpt55.md`** — V4 of the D0 scoping, which X01 implements.
9. **`seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md`** — synthesis memo with the chosen design.

Audit tasks (A02, A07, A08, A09, A10) only need the files they are auditing, plus the universal items above.

---

## 3. Universal forbidden scope

The following are **forbidden across all 6 tasks**. Violations are operator-rejection-level.

### 3.1 Trust-root edits (HARD FORBIDDEN)

- `pnp3/Complexity/Interfaces.lean` — read only.
- `pnp3/Complexity/PsubsetPpolyInternal/**` — read only.
- `pnp3/Magnification/UnconditionalResearchGap.lean` — read only.
- `pnp3/Barrier/**` — read only.
- `pnp3/Magnification/AuditRoutes/**` — read only.
- `pnp3/Magnification/*_Partial.lean` — read only this wave.
- `pnp3/Magnification/FinalResult*.lean` — read only (A02 audits these; does **not** edit them).
- `pnp3/LowerBounds/*_Partial.lean` — read only this wave.
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` — read only.
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` — read only.
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean` — read only.
- `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` — read only.
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage*.lean` (R1-B, R1-B1, R1-B2a) — read only.

If your task **appears** to require trust-root edits, you have **misread the task**. Re-read your task file; the deliverable is always at a new file path.

### 3.2 Forbidden Lean constructs (X01 only; audits produce no Lean)

In every Lean file you write or modify:

- ❌ `sorry`
- ❌ `admit`
- ❌ `axiom`
- ❌ `opaque`
- ❌ `Fact` (typeclass-payload pattern)
- ❌ `Classical.choose` in core definitions (acceptable in derived proofs only if standard exponent extraction; document explicitly)
- ❌ `decide` in places that take more than ~1 second to elaborate
- ❌ `native_decide`

### 3.3 Forbidden registry / spec edits

- ❌ `outputs/nogolog.jsonl` — no new entries (A09 audits; does not append).
- ❌ `outputs/attempts.jsonl` — no edits.
- ❌ `spec/known_guards.toml` — no edits.
- ❌ `spec/wave_*.toml` — no edits.
- ❌ Any `Candidates/` directory — no creation.
- ❌ `ProvenanceFilter_v1` — no promotion to `accepted` status.

### 3.4 Forbidden language in code or commits

- ❌ `SourceTheorem` / `gap_from_*` / `ResearchGapWitness` / `NP_not_subset_PpolyDAG` / `P_ne_NP` — no construction, no claim.
- ❌ FP-4 work — gated separately.
- ❌ "Proves P ≠ NP" / "advances P-vs-NP" — never in commit messages, PR descriptions, code comments, or audit reports.
- ❌ Any unconditional complexity separation claim.

This wave is **infrastructure + operator situational awareness only**. Do not overclaim.

---

## 4. Universal acceptance criteria

These apply to **every** task. Your task file adds task-specific items on top.

### 4.1 For audit tasks (A02, A07, A08, A09, A10)

1. **Markdown report** at exact path `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/<ID>_<area>_<handle>.md`.
2. **No Lean edits anywhere.** Run `git diff origin/main -- "*.lean"` → must be empty.
3. **No edits to `outputs/`, `spec/`, or `Candidates/`.**
4. Report must include required sections per your task file (typically: file inventory, signature surface, gap inventory, recommendations, honest caveats).
5. Claims about file state must be reproducible from the cited commit SHA.

### 4.2 For X01

1. `lake build PnP3 Pnp4` — must pass from the repository root.
2. `./scripts/check.sh` — must pass.
3. `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` — must return **no output** across the whole repo.
4. New Lean modules at exact paths specified in `tasks/X01_polytimeverifierspec_bridge.md`.
5. Doc-comment at top of each new module: states D0 scoping reference, declares infrastructure-only scope (not P ≠ NP progress).

### 4.3 Shared-file conventions for X01

X01 needs additions to three project-shared files:

- `lakefile.lean` — one `Glob.one` line per new module.
- `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` — one `check_<name>` wrapper per public signature in your task's "Expected signatures" list.
- `pnp4/Pnp4/Tests/AxiomsAudit.lean` — one `#print axioms` line per theorem in your task.

**You apply these patches directly in your PR.** Within wave 1 X01 is the only Lean task, so no parallel-merge collision is expected. If a collision arises with concurrent operator-side work, rebase rather than retarget.

### 4.4 Module documentation (X01)

Every new Lean module must have a `/-! ... -/` doc-comment at the top stating:

- The D0 scoping reference (V4 chosen, `d367652`).
- That this is infrastructure, **not** a proof of any unconditional complexity statement.
- That the bridge enables resumability of the contract-expansion track and does not itself advance `NP_not_subset_PpolyDAG`.

Example template:

```
/-!
# PolyTimeVerifierSpec

Implementation of the polynomial-time verifier spec + bridge to `NP_TM`,
per D0 polynomial-time formalism scoping (V4 selected, `d367652`) and the
four-way synthesis memo (`d3676520`).

**Scope:** infrastructure bridge for the contract-expansion track. This module
defines a typed surface that consumes verifiable polynomial-time data and
produces an `NP_TM L` witness. It does **not** by itself reduce
`SearchMCSPWeakLowerBound`, construct `ResearchGapWitness`, or advance
`NP_not_subset_PpolyDAG`.
-/
```

### 4.5 Trust-root unchanged (all tasks)

After your work:

- `git diff origin/main pnp3/Complexity/Interfaces.lean` must be empty.
- `git diff origin/main pnp3/Barrier/` must be empty.
- `git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean` must be empty.
- `git diff origin/main pnp3/Magnification/AuditRoutes/` must be empty.
- For audit tasks: `git diff origin/main -- "*.lean"` must be empty.

If any of these diffs is non-empty for your task, the PR will be rejected.

---

## 5. Self-attack discipline

Before opening your PR, run a 10-minute self-attack:

1. **Read your own deliverable as an adversary.** For audits: are file-state claims actually reproducible from cited SHAs, or did you accidentally over-summarize? For X01: is the bridge a renaming, or does it actually produce an `NP L` witness consuming concrete polynomial-time data?
2. **Check that you did not formalize a circular interface.** A `PolyTimeVerifierSpec` with a field `proven_in_NP : Prop` would technically compile but is circular. The bridge must genuinely extract poly-time verification data, not assert membership.
3. **Verify `#print axioms`.** New X01 theorems should depend only on standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) plus whatever the D0 memo authorizes.
4. **Check the test surface compiles.** `lake build` on the test files specifically.
5. **Verify doc-comment honesty.** No "this module proves a step toward P ≠ NP" language.

If self-attack reveals problems, fix them or write a `failures/<ID>_<handle>.md` report (§10).

---

## 6. Cross-engineer coordination

You don't coordinate with other engineers directly. The operator does.

- If another engineer's PR lands first and conflicts with your file paths, **do not** retarget. Report via failure report.
- If you need a definition from another engineer's pending work, **do not** assume it will land. Write your task self-containedly.

Within this wave the only Lean task is X01, so audit/audit collisions cannot occur (different markdown paths), and audit/X01 collisions cannot occur (audits produce no Lean).

---

## 7. Time budget

Each task has an estimated time in the README task list. If you exceed 1.5× the estimate without a clean deliverable, **stop and write a structured failure report** (§10).

Don't grind past 1.5× — operator wants signals about infeasibility, not heroic effort on an under-scoped task.

---

## 8. Required commands

### For audit tasks

```bash
git diff origin/main -- "*.lean"                                # must be empty
git diff origin/main pnp3/Barrier/                              # must be empty
git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean  # must be empty
ls seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/  # your report must appear
```

### For X01

```bash
lake build PnP3 Pnp4
./scripts/check.sh
rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4                # must be empty
git diff origin/main pnp3/Complexity/Interfaces.lean            # must be empty
git diff origin/main pnp3/Barrier/                              # must be empty
git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean  # must be empty
```

All commands must succeed (or for `rg` / `git diff`, return empty).

---

## 9. PR submission

1. Push your branch: `git push -u origin khanukov/phase1-<ID>-<handle>`.
2. Open PR to `main`.
3. PR title: `Phase 1 <ID>: <task title>`.
4. PR description uses §12 template.

Do **not** request review unless your self-attack (§5) is clean.

---

## 10. Failure protocol

If you cannot complete your task within scope, write a failure report at:

`seed_packs/phase1_20engineer_parallel_dispatch/failures/<ID>_<handle>.md`

With **exactly four sections**:

1. **What was attempted.** Concrete approach; high-level recipe; time spent.
2. **Where it broke.** Lean error verbatim (X01) or precise audit-scope obstruction (audits).
3. **Local vs global obstruction.**
   - `Local`: another engineer with a different approach might succeed.
   - `Global`: the task as specified is unimplementable in the current repo state; needs operator scope revision.
4. **What an integrator must know.** Specific recipe for redispatching or pivoting.

PR the failure report only (no Lean changes). Operator decides on redispatch.

---

## 11. Honest reporting

Every PR description **must** include a "Honest caveats" line. Examples of good caveats:

- "The audit covers the 24 files in `AlgorithmsToLowerBounds/` at SHA `<x>`; one file (`<name>`) was skimmed not deep-read."
- "X01's toy verifier uses the empty language to keep `runTimeBound` trivially provable; a non-trivial language is left for follow-up."
- "The `Classical.choose` in line 84 extracts the polynomial exponent from `polyBound_poly`; standard usage."
- "I did not verify all 24 `#print axioms` outputs match; I sampled 4 representative ones."

Dishonest framing to avoid:

- ❌ "This module advances toward P ≠ NP."
- ❌ "Audit complete." (when sections are skimmed)
- ❌ "No caveats." (when there are clearly limitations)

Honest framing is **rewarded**. Operator merges honest partial completions; rejects dishonest "complete" claims.

---

## 12. Universal output format (for your PR description)

```text
Task: <ID> <title>
Engineer handle: <your-handle>
Branch: khanukov/phase1-<ID>-<handle>
Commit: <sha>

Files added/modified:
  - <list>

Acceptance criteria (universal):
  [x] No trust-root edits (verified via git diff)
  [x] Audit-only: no Lean edits (git diff origin/main -- "*.lean" empty)
      OR Lean-task: lake build PnP3 Pnp4 → green;
                    ./scripts/check.sh → green;
                    rg sorry|admit -g"*.lean" pnp3 pnp4 → empty;
                    lakefile.lean updated with Glob.one line(s);
                    smoke test in AlgorithmsToLowerBoundsSurfaceTests.lean;
                    #print axioms entries in AxiomsAudit.lean
  [x] Module/report doc-comment honestly describes scope

Acceptance criteria (task-specific):
  [x] / [ ] <each item from your task file>

For X01 — Lean signatures landed:
  - <name> : <type>
  - ...

For audits — Report sections:
  - File inventory: <count> files, <LOC> total
  - Signature surface: <summary>
  - Gap inventory: <summary>
  - Recommendations: <summary>

Honest caveats:
  - <list any place where deliverable falls short of literal task spec, or where
    you took a design liberty>

Commands run:
  - <list per §8>

Self-attack notes:
  - <what you checked and concluded during your 10-minute adversarial review>

Scope violations: none / <list>
```

---

## 13. Final reminders

- **This wave is infrastructure + operator situational awareness**, not P ≠ NP progress. Don't overclaim.
- **Trust-root files are read-only.** No exceptions.
- **Honest partial completion is good**; dishonest "complete" is rejected.
- **Time-box at 1.5× the estimate.** If exceeding, write a failure report.
- **Self-attack before submitting.** 10 minutes minimum.
- **One task per engineer.** Don't grab multiple.
- **The only active ID is A11.** All other task files in `tasks/` are wave-1 record (A01–A10 completed and merged) or wave-2 candidates blocked on A11 (L01–L02, B01–B03, K01–K02, X01–X02). Do not pick any of them.

Good luck. Reduced wave is intentional — fewer, higher-yield tasks for faster operator decision.
