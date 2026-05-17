# Common worker instructions — Phase 1 A11-gated dispatch

You are assigned **one authorised `<TASK_ID>`** in an A11-gated dispatch. Read this file once before starting your specific task file at `tasks/<TASK_ID>_*.md`. Current authorised dispatch is P1P-01 and P1P-02 only; follow-up tasks require explicit operator authorisation.

This is binding. Violations result in operator rejection.

---

## 1. Identity and scope

Pick **one** authorised `<TASK_ID>`. Don't take more than one. Don't change tasks mid-flight. No implementation task may start without an explicit operator prompt after A11/P1P documentation is in place.

Your branch name **must** follow this convention:

```
khanukov/phase1-<TASK_ID>-<short-handle>
```

Example: `khanukov/phase1-P1P-01-codex-gpt55`

Your PR title:

```
Phase 1 <TASK_ID>: <task title from README.md task list>
```

---

## 2. Required reading (universal)

Before you start:

1. **`RESEARCH_CONSTITUTION.md`** — binding discipline.
2. **`seed_packs/phase1_20engineer_parallel_dispatch/README.md`** — phase overview, dependencies, acceptance criteria.
3. **`seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md`** — context for why this phase exists. Read §3 (what was accomplished), §6 (the gap), §11 (honest framing). You do not need to read the full FP3b history; the retrospective is sufficient.
4. **Your specific task file** at `seed_packs/phase1_20engineer_parallel_dispatch/tasks/<TASK_ID>_*.md`.

If your task touches pnp3 / pnp4 Lean code:

5. **`pnp3/Complexity/Interfaces.lean`** — trust-root types you must import but never modify.
6. **`pnp4/Pnp4/AlgorithmsToLowerBounds/BasicCircuitClasses.lean`** — pnp4 `CircuitFamilyClass` and `BitVec` conventions.

If your authorised task touches barrier files (for example B01-B03):

7. **`pnp3/Barrier/NaturalProofs.lean`, `pnp3/Barrier/Relativization.lean`, `pnp3/Barrier/Algebrization.lean`, `pnp3/Barrier/Bypass.lean`** — existing trust-root barrier interfaces. **Read only; do not modify.** Your new content goes under `pnp4/Pnp4/Barriers/`.

If your authorised task touches kill-machine infra (for example K01-K02):

8. **`outputs/nogolog.jsonl`** — existing NoGoLog entries (NOGO-000005 through 000009). Read structure; do not append.

If your authorised task touches contract_expansion (for example X01-X02):

9. **`pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean`**
10. **`pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean`**
11. **`pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`**
12. **`pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`** for `NP_TM` interface (read only).

## 2.1 A11 dispatch gate

A11 synthesis is required before any Phase 1+ / L / B / K / X implementation wave. Current authorised dispatch:

- P1P-01
- P1P-02
- follow-up tasks only by explicit operator authorisation.

No implementation task may start without an explicit operator prompt after A11/P1P documentation is in place. The old broad concurrent dispatch model is superseded.

| Task(s) | A11 status | Dispatch implication |
| --- | --- | --- |
| B02 | Cancelled as written | Do not dispatch without a replacement scope. |
| B03 | Cancelled as written | Do not dispatch without a replacement scope. |
| B01 | Rewrite required | Redispatch only after concrete barrier-certificate criteria are approved. |
| K01 | Rewrite required | Redispatch only after the NoGo/manual-classification scope is corrected. |
| K02 | Hold until governance repair | Hold until README/COMMON and related governance repairs land. |
| X01 | Hold pending no-faking / NP-interface review | Do not implement until the bridge cannot accept staged placeholders and the interface review is complete. |
| X02 | Rewrite after parser convention design | Wait for P1P-02 parser convention design before any implementation scope. |
| L01/L02 | Downgrade to markdown | Treat as literature/interface alignment documents, not Lean implementation tasks. |

---

## 3. Universal forbidden scope

The following are **forbidden across all tasks**. Violations are operator-rejection-level.

### 3.1 Trust-root edits (HARD FORBIDDEN)

- `pnp3/Complexity/Interfaces.lean` — read only.
- `pnp3/Complexity/PsubsetPpolyInternal/**` — read only.
- `pnp3/Magnification/UnconditionalResearchGap.lean` — read only.
- `pnp3/Barrier/**` — read only. New barriers go under `pnp4/Pnp4/Barriers/`.
- `pnp3/Magnification/AuditRoutes/**` — read only. Existing audit routes are frozen.
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` — read only.
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` — read only.
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean` — read only.
- `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` — read only.

If your task **appears** to require trust-root edits, you have **misread the task**. Re-read your task file; the deliverable is always in a new file path.

### 3.2 Forbidden Lean constructs

In every Lean file you write or modify:

- ❌ `sorry`
- ❌ `admit`
- ❌ `axiom` (unless your task file **explicitly** authorizes it; none do in Phase 1)
- ❌ `opaque`
- ❌ `Fact` (typeclass-payload pattern; forbidden by Rule 16)
- ❌ `Classical.choose` in core definitions (acceptable in derived proofs only if standard exponent extraction; document explicitly)
- ❌ `decide` in places that take more than ~1 second to elaborate
- ❌ `native_decide`

### 3.3 Forbidden registry / spec edits

- ❌ `outputs/nogolog.jsonl` — no new entries.
- ❌ `outputs/attempts.jsonl` — no edits.
- ❌ `spec/known_guards.toml` — no edits.
- ❌ `spec/wave_*.toml` — no edits.
- ❌ Any `Candidates/` directory — no creation.
- ❌ `ProvenanceFilter_v1` — no promotion to `accepted` status.

### 3.4 Forbidden language in code or commits

- ❌ `SourceTheorem` / `gap_from_*` / `ResearchGapWitness` / `NP_not_subset_PpolyDAG` / `P_ne_NP` — no construction, no claim.
- ❌ FP-4 work — gated separately.
- ❌ "Proves P ≠ NP" / "advances P-vs-NP" — never in commit messages, PR descriptions, or code comments.
- ❌ Any unconditional complexity separation claim.

Phase 1 is **infrastructure only**. Do not overclaim.

---

## 4. Universal acceptance criteria

These apply to **every** task. Your task file adds task-specific items on top.

### 4.1 Build hygiene

1. `lake build PnP3 Pnp4` — must pass from the repository root.
2. `./scripts/check.sh` — must pass.
3. `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` — must return **no output** across the whole repo (not just your files).

### 4.2 File placement

Your new Lean module(s) **must** be at the exact path(s) specified in your task file. If your task specifies:

```
pnp4/Pnp4/Literature/AtseriasMuller2025/Definitions.lean
```

then you create exactly that file. Don't reorganize.

### 4.3 Lakefile registration

Every new Lean module you create must be added to `lakefile.lean` via one `Glob.one` line:

```
Glob.one `Pnp4.Literature.AtseriasMuller2025.Definitions,
```

Match the existing pattern in `lakefile.lean`.

### 4.4 Test surface

For every public theorem or structure your task lists in "Expected signatures":

1. Add one `check_<name>` wrapper to `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`:

   ```
   def check_<name> : <signature> := <expression>
   ```

   This lets the test surface verify the name is accessible from a separate module.

2. Add one `#print axioms` line for each **theorem** (not every definition) to `pnp4/Pnp4/Tests/AxiomsAudit.lean`. Match existing patterns.

### 4.5 Module documentation

Every new Lean module must have a `/-! ... -/` doc-comment at the top stating:

- The literature source (paper, year, arXiv/DOI), if Phase A.
- That this is infrastructure, **not** a proof of any unconditional complexity statement.
- That the contents may be used by future kill-machine routes but do not themselves advance P-vs-NP.

Example template:

```
/-!
# <Module title>

Formalization of <theorem name> from <Author Year> (<verifiable identifier>).

**Scope:** infrastructure for the kill-machine and future audit routes. This
module proves a specific literature theorem (or stages it as a typed surface);
it does not by itself reduce `SearchMCSPWeakLowerBound`, construct
`VerifiedNPDAGLowerBoundSource`, or advance `NP_not_subset_PpolyDAG`.
-/
```

### 4.6 No `Classical.choose` in literature definitions

For authorised Phase A/L/X-style tasks:

- The **structure definitions** and **theorem statements** must be free of `Classical.choose`.
- The `def` instances and theorem **proofs** may use `Classical.choose` **only** if it's a standard polynomial-exponent extraction (e.g., `Classical.choose h.polyBound_poly` where `h.polyBound_poly : ∃ c, ...`).
- Such use must be documented in a 1-line comment.

For authorised Phase B tasks:

- Razborov-Rudich barrier may use `Classical.choose` in the construction of the diagonal adversary (this is mathematically necessary). Document it.

### 4.7 Trust-root unchanged

After your work:

- `git diff origin/main pnp3/Complexity/Interfaces.lean` must be empty.
- `git diff origin/main pnp3/Barrier/` must be empty.
- `git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean` must be empty.

If your `git diff` shows changes to these files, your PR will be rejected. No exceptions.

---

## 5. Self-attack discipline

Before opening your PR, you **must** run a 10-minute self-attack:

1. **Read your own deliverable as if you were an adversary trying to falsify it.** Is there a way the theorem you proved is vacuous? Does it accidentally smuggle a stronger assumption than the literature requires?

2. **Check that you did not formalize a circular interface.** A structure with field `proven_NP_not_subset_PpolyDAG : Prop` would technically compile but is circular. If your task involves bridging literature to a target like `NP_TM`, ensure the bridge is genuine, not a renaming.

3. **Verify your `#print axioms` output is clean.** New theorems should only depend on standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) plus the explicit literature axioms your task authorizes. If you see unexpected axioms, debug before submitting.

4. **Check the test surface compiles.** `lake build` on the test files specifically.

5. **Verify the doc-comment honestly describes what you proved.** No "this module proves a step toward P ≠ NP" language.

If self-attack reveals problems, fix them or write a `failures/<TASK_ID>_<handle>.md` report (see §10 below).

---

## 6. Cross-engineer coordination

You don't coordinate with other engineers directly. The operator does.

- If another engineer's PR lands first and conflicts with your file paths, **do not** retarget. Report via failure report.
- If you need a definition from another engineer's pending work, **do not** assume it will land. Write your task self-containedly; the operator will resolve dependencies during integration.

---

## 7. Time budget

Each task has an estimated time in the README task list. If you exceed 1.5× the estimate without a clean Lean module to show, **stop and write a structured failure report** (see §10).

Don't grind past 1.5× — the operator wants signals about infeasibility, not heroic effort on an under-scoped task.

---

## 8. Required commands

Run before opening your PR:

```bash
lake build PnP3 Pnp4
./scripts/check.sh
rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4
git diff origin/main pnp3/Complexity/Interfaces.lean       # must be empty
git diff origin/main pnp3/Barrier/                          # must be empty
git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean  # must be empty
```

All commands must succeed (or for `rg` and `git diff`, return empty).

---

## 9. PR submission

1. Push your branch only if explicitly instructed by the operator: `git push -u origin khanukov/phase1-<TASK_ID>-<handle>`.
2. Open PR to `main`.
3. PR title: `Phase 1 <TASK_ID>: <task title>`.
4. PR description must include the structured output template from the README §"Output template — every PR".
5. Tag the PR with an appropriate `<TASK_ID>`/phase label if labels are configured.

Do **not** request review unless your self-attack (§5) is clean.

---

## 10. Failure protocol

If you cannot complete your task within scope, write a failure report:

`seed_packs/phase1_20engineer_parallel_dispatch/failures/<TASK_ID>_<handle>.md`

With **exactly four sections**:

1. **What was attempted.** Concrete Lean code tried; high-level approach; time spent.
2. **Where it broke.** Lean error verbatim, or precise mathematical / interface obstruction.
3. **Local vs global obstruction.**
   - `Local`: another engineer with a different approach might succeed; the task as specified is feasible.
   - `Global`: the task as specified is unimplementable in the current repo state; needs operator scope revision.
4. **What an integrator must know.** Specific recipe for redispatching or pivoting.

PR the failure report only (no Lean changes). Operator decides on redispatch or scope revision.

---

## 11. Honest reporting

Every PR description **must** include a "Honest caveats" line. Examples of good honest caveats:

- "The theorem proves the bound for the codec-induced case only; the abstract-encoding case remains as a `Prop`-staged obligation."
- "The `Classical.choose` in line 84 extracts the polynomial exponent from `polyBound_poly`; this is standard but introduces `Classical.choice` into the axiom surface."
- "The structure has 9 fields; 3 are real `∀`-quantified theorems, 6 are `Prop` placeholders for future runtime / serialization work."
- "I did not verify that the literature theorem holds verbatim; I formalized the statement under the assumption that AM 2025 v1 §2 Theorem 1 is correctly stated in the arXiv PDF."

Examples of dishonest framing to avoid:

- ❌ "This module advances toward P ≠ NP."
- ❌ "Successfully formalized AM 2025 Theorem 1." (when only the statement is typed, not proved)
- ❌ "No caveats." (when there are clearly staged obligations)

Honest framing is **rewarded**. The operator merges honest partial completions; the operator rejects dishonest "complete" claims.

---

## 12. Universal output format (for your PR description)

```text
Task: <TASK_ID> <title>
Engineer handle: <your-handle>
Branch: khanukov/phase1-<TASK_ID>-<handle>
Commit: <sha>

Files added/modified:
  - <list>

Acceptance criteria (universal):
  [x] lake build PnP3 Pnp4 → green
  [x] ./scripts/check.sh → green
  [x] rg sorry|admit -g"*.lean" pnp3 pnp4 → empty
  [x] No trust-root edits (verified via git diff)
  [x] lakefile.lean updated with one Glob.one line
  [x] Smoke test in AlgorithmsToLowerBoundsSurfaceTests.lean
  [x] #print axioms entries in AxiomsAudit.lean
  [x] Module doc-comment honestly describes scope

Acceptance criteria (task-specific):
  [x] / [ ] <each item from your task file>

Lean signatures landed:
  - <name> : <type>
  - ...

Honest caveats:
  - <list any place where deliverable falls short of literal task spec, or where
    you took a design liberty>

Commands run:
  - lake build PnP3 Pnp4 → <status>
  - ./scripts/check.sh → <status>
  - rg sorry|admit -g*.lean pnp3 pnp4 → <status>
  - git diff origin/main pnp3/Complexity/Interfaces.lean → empty
  - git diff origin/main pnp3/Barrier/ → empty
  - git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean → empty

Self-attack notes:
  - <what you checked and concluded during your 10-minute adversarial review>

Scope violations: none / <list>
```

---

## 13. Final reminders

- **Phase 1 is infrastructure**, not P ≠ NP progress. Don't overclaim.
- **Trust-root files are read-only.** No exceptions.
- **Honest partial completion is good**; dishonest "complete" is rejected.
- **Time-box at 1.5× the estimate.** If exceeding, write a failure report.
- **Self-attack before submitting.** 10 minutes minimum.
- **One task per engineer.** Don't grab multiple.

Good luck. The kill-machine framework relies on each engineer producing exactly what their task file specifies — no more, no less.
