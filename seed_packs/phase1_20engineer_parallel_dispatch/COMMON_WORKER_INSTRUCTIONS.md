# Common worker instructions — Phase 1 A11-gated dispatch (post-P1P-02L₂)

You are assigned **one authorised `<TASK_ID>`** in an A11-gated dispatch. Read this file once before starting your specific task file at `tasks/<TASK_ID>_*.md` (for legacy tasks) or `docs/<TASK_ID>_*.md` (for P1P design/review tasks).

**Wave-1 status:** A01–A10 audits + A11 synthesis complete. P1P-01 governance + P1P-02 design + P1P-02L real parser + P1P-02L₂ encoder/length-convention/RuntimeAwarePrefixParser wiring all landed. Current planned next: **P1P-02L₃ canonical round-trip** (operator-authorised only).

This file is binding. Violations result in operator rejection. If you see references in other documents to `E<NN>` IDs, ignore them — they predate the 2026-05-17 plan reduction. Use the `<TASK_ID>` naming convention throughout.

---

## 1. Identity and scope

Pick **one** authorised `<TASK_ID>`. Don't take more than one. Don't change tasks mid-flight. No implementation task may start without an explicit operator prompt.

Your branch name **must** follow this convention:

```
khanukov/phase1-<TASK_ID>-<short-handle>
```

Example: `khanukov/phase1-P1P-02L3-codex-gpt55`.

Your PR title:

```
Phase 1 <TASK_ID>: <task title>
```

## 1.1 A11 dispatch gate (current task status)

A11 synthesis is the governing decision. Current authorised dispatch:

- P1P track (P1P-01 → P1P-02 → P1P-02L → P1P-02L₂) — already landed.
- **P1P-02L₃** — canonical parse-encode round-trip — operator-authorised only.
- Follow-up markdown-only tasks (P1P-03/04/05 hygiene work) — operator-authorised only.

No L/B/K/X implementation dispatch is authorised. Per-task status (from A11):

| Task(s) | A11 status | Dispatch implication |
| --- | --- | --- |
| B02 | Cancelled as written | Do not dispatch without a replacement scope. |
| B03 | Cancelled as written | Do not dispatch without a replacement scope. |
| B01 | Rewrite required | Redispatch only after concrete barrier-certificate criteria are approved. |
| K01 | Rewrite required | Redispatch only after the NoGo/manual-classification scope is corrected. |
| K02 | Hold | Hold until further governance repair lands. |
| X01 | Hold pending no-faking / NP-interface review | Do not implement until the bridge cannot accept staged placeholders and the interface review is complete. |
| X02 | Rewrite after parser convention design | P1P-02L/L₂ now provide the parser; X02 should be redesigned around them if reactivated. |
| L01/L02 | Downgrade to markdown | Treat as literature/interface alignment documents, not Lean implementation tasks. |

---

## 2. Required reading (universal)

Before you start:

1. **`RESEARCH_CONSTITUTION.md`** — binding discipline.
2. **`seed_packs/phase1_20engineer_parallel_dispatch/README.md`** — phase overview, landed work, A11 status.
3. **`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_codex.md`** — A11 synthesis verdict and the binding dispatch decision.
4. **Your specific task file** at `seed_packs/phase1_20engineer_parallel_dispatch/{tasks,docs}/<TASK_ID>_*.md`.

If your task is on the P1P contract-expansion parser track:

5. **`pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean`** — R1-B abstract language and `PrefixParser` interface (read only).
6. **`pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean`** — R1-B1 NP-verifier budget interface (read only).
7. **`pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`** — R1-B2a runtime/codec interfaces (read only).
8. **`pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean`** — landed P1P-02L/L₂ parser + encoder + length convention (read; extend by adding new theorems, do not edit existing definitions without explicit operator approval).
9. **`seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_02_prefix_parser_convention_gpt55.md`** — parser convention design.
10. **`seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_02L_operator_review_claudeopus.md`** — operator review identifying P1P-02L₃ as the next step.

If your task touches pnp3 / pnp4 Lean code:

11. **`pnp3/Complexity/Interfaces.lean`** — trust-root types you must import but never modify.
12. **`pnp4/Pnp4/AlgorithmsToLowerBounds/BasicCircuitClasses.lean`** — pnp4 `CircuitFamilyClass` and `BitVec` conventions.

If your authorised task touches barrier files (for example B01-B03 after rewrite):

13. **`pnp3/Barrier/NaturalProofs.lean`, `Relativization.lean`, `Algebrization.lean`, `Bypass.lean`** — existing trust-root barrier interfaces. **Read only; do not modify.** New content goes under `pnp4/Pnp4/Barriers/`.

If your authorised task touches kill-machine infra (for example K01-K02 after rewrite):

14. **`outputs/nogolog.jsonl`** — existing NoGoLog entries. Read structure; do not append.

---

## 3. Universal forbidden scope

The following are **forbidden across all tasks**. Violations are operator-rejection-level.

### 3.1 Trust-root edits (HARD FORBIDDEN)

- `pnp3/Complexity/Interfaces.lean` — read only.
- `pnp3/Complexity/PsubsetPpolyInternal/**` — read only.
- `pnp3/Magnification/UnconditionalResearchGap.lean` — read only.
- `pnp3/Barrier/**` — read only.
- `pnp3/Magnification/AuditRoutes/**` — read only.
- `pnp3/Magnification/*_Partial.lean` — read only.
- `pnp3/Magnification/FinalResult*.lean` — read only.
- `pnp3/LowerBounds/*_Partial.lean` — read only.
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` — read only.
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` — read only.
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean` — read only.
- `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` — read only.
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage*.lean` (R1-B, R1-B1, R1-B2a) — read only.

If your task **appears** to require trust-root edits, you have **misread the task**. Re-read your task file; the deliverable is always at a new file path or as new declarations appended to `PrefixParserConvention.lean`.

### 3.2 Forbidden Lean constructs

In every Lean file you write or modify:

- ❌ `sorry`
- ❌ `admit`
- ❌ `axiom`
- ❌ `opaque`
- ❌ `Fact` (typeclass-payload pattern)
- ❌ `Classical.choose` in core parser/encoder definitions (acceptable in derived proofs only if standard exponent extraction; document explicitly)
- ❌ `decide` in places that take more than ~1 second to elaborate
- ❌ `native_decide`
- ❌ `noncomputable def` for any parser, encoder, or core data definition (the parser must remain computable — A11 anti-faking discipline)

### 3.3 Forbidden registry / spec edits

- ❌ `outputs/nogolog.jsonl` — no new entries (P1P-03 may propose anchor repairs as a markdown plan; actual JSONL edits require separate operator-authorised task).
- ❌ `outputs/attempts.jsonl` — no edits.
- ❌ `spec/known_guards.toml` — no edits.
- ❌ `spec/wave_*.toml` — no edits.
- ❌ Any `Candidates/` directory — no creation.
- ❌ `ProvenanceFilter_v1` — no promotion to `accepted` status.

### 3.4 Forbidden language in code or commits

- ❌ `SourceTheorem` / `gap_from_*` / `ResearchGapWitness` / `NP_not_subset_PpolyDAG` / `P_ne_NP` — no construction, no claim.
- ❌ `VerifiedNPDAGLowerBoundSource` construction (consuming the type is OK; instantiating it is not).
- ❌ `PrefixExtensionLanguage_in_NP` — no claim.
- ❌ FP-4 work — gated separately.
- ❌ "Proves P ≠ NP" / "advances P-vs-NP" — never in commit messages, PR descriptions, code comments, or audit reports.
- ❌ Any unconditional complexity separation claim.

This phase is **infrastructure + operator situational awareness only**. Do not overclaim.

---

## 4. Universal acceptance criteria

These apply to **every** task. Your task file adds task-specific items on top.

### 4.1 For markdown-only tasks (audits, design notes, operator reviews)

1. Markdown report at exact path specified in your task file.
2. No Lean edits anywhere. Run `git diff origin/main -- "*.lean"` → must be empty.
3. No edits to `outputs/`, `spec/`, or `Candidates/`.
4. Report must include required sections per your task file.
5. Claims about file state must be reproducible from the cited commit SHA.

### 4.2 For Lean tasks (P1P-02L₃ or similar)

1. `lake build PnP3 Pnp4` — must pass from the repository root.
2. `./scripts/check.sh` — must pass.
3. `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` — must return **no output** across the whole repo.
4. New Lean definitions/theorems at the exact path(s) specified in your task file (typically appended to `pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean`).
5. Doc-comments at the top of each new declaration: state infrastructure-only scope (not P ≠ NP progress), not NP-membership.

### 4.3 Shared-file conventions for Lean tasks

If your Lean task introduces new public theorems/definitions, you must add corresponding entries to:

- `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` — one `#check` per public definition; optional `def check_<name>` wrapper per theorem.
- `pnp4/Pnp4/Tests/AxiomsAudit.lean` — one `#print axioms` per theorem; optional `#check` per definition.

Your PR applies these patches directly. Within wave 1 only one Lean task is active at a time, so no parallel-merge collision is expected.

### 4.4 Trust-root unchanged (all tasks)

After your work:

- `git diff origin/main pnp3/Complexity/Interfaces.lean` must be empty.
- `git diff origin/main pnp3/Barrier/` must be empty.
- `git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean` must be empty.
- `git diff origin/main pnp3/Magnification/AuditRoutes/` must be empty.
- `git diff origin/main pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage*.lean` must be empty.
- For markdown-only tasks: `git diff origin/main -- "*.lean"` must be empty.

If any of these diffs is non-empty for your task, the PR will be rejected.

---

## 5. Self-attack discipline

Before opening your PR, run a 10-minute self-attack:

1. **Read your own deliverable as an adversary.** Did you accidentally turn a parser into `noncomputable def`? Did you add a `Classical.choose` to a core definition? Did you add an `axiom`?
2. **Check you did not formalize a circular interface.** A round-trip "theorem" that's trivially true by definition is not a theorem; a length-convention "theorem" that doesn't unfold the parser body is suspicious.
3. **Verify `#print axioms`.** New theorems should depend only on standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) plus whatever your task file explicitly authorises.
4. **Check the test surface compiles.** `lake build` on the test files specifically.
5. **Verify doc-comment honesty.** No "this module proves a step toward P ≠ NP" language.

If self-attack reveals problems, fix them or write a `failures/<TASK_ID>_<handle>.md` report (§10).

---

## 6. Cross-engineer coordination

You don't coordinate with other engineers directly. The operator does.

- If another engineer's PR lands first and conflicts with your file paths, **do not** retarget. Report via failure report.
- If you need a definition from another engineer's pending work, **do not** assume it will land.

---

## 7. Time budget

Each task has an estimated time in its task/design file. If you exceed 1.5× the estimate without a clean deliverable, **stop and write a structured failure report** (§10).

---

## 8. Required commands

### For markdown-only tasks

```bash
git diff origin/main -- "*.lean"                                # must be empty
git diff origin/main pnp3/Barrier/                              # must be empty
```

### For Lean tasks

```bash
lake build PnP3 Pnp4
./scripts/check.sh
rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4                # must be empty
git diff origin/main pnp3/Complexity/Interfaces.lean            # must be empty
git diff origin/main pnp3/Barrier/                              # must be empty
git diff origin/main pnp3/Magnification/UnconditionalResearchGap.lean  # must be empty
git diff origin/main pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean        # must be empty
git diff origin/main pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean      # must be empty
git diff origin/main pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean # must be empty
```

All commands must succeed (or for `rg` / `git diff`, return empty).

---

## 9. PR submission

1. Push your branch only if explicitly instructed by the operator: `git push -u origin khanukov/phase1-<TASK_ID>-<handle>`.
2. Open PR to `main`.
3. PR title: `Phase 1 <TASK_ID>: <task title>`.
4. PR description uses §12 template.

Do **not** request review unless your self-attack (§5) is clean.

---

## 10. Failure protocol

If you cannot complete your task within scope, write a failure report at:

`seed_packs/phase1_20engineer_parallel_dispatch/failures/<TASK_ID>_<handle>.md`

With **exactly four sections**:

1. **What was attempted.** Concrete approach; high-level recipe; time spent.
2. **Where it broke.** Lean error verbatim, or precise scope obstruction.
3. **Local vs global obstruction.**
   - `Local`: another engineer with a different approach might succeed.
   - `Global`: the task as specified is unimplementable in the current repo state; needs operator scope revision.
4. **What an integrator must know.** Specific recipe for redispatching or pivoting.

PR the failure report only (no Lean changes). Operator decides on redispatch.

---

## 11. Honest reporting

Every PR description **must** include a "Honest caveats" line. Examples of good caveats:

- "The length-convention proof handles all 7 success branches of the parser do-block, but I did not add a separate `parseTreeMCSPPrefixInput_short_input` lemma for the `m < 8` case (it is implicitly covered by the do-bind short-circuit)."
- "The round-trip proof uses an extensional equality argument over `Fin` indices; I did not need `Classical.choose` for `prefixLength_le` proof-irrelevance, but I did rely on the `CanonicalRawTreeMCSPPrefixFields` separation landed by P1P-02L₂."
- "The encoder's `gammaBit` definition uses an `if … else if … else` branching structure; the future round-trip proof will need a separate gamma-decoder correctness lemma `decodeGamma? (encodeGamma n) = some (n, gammaLen n)`."

Dishonest framing to avoid:

- ❌ "This module advances toward P ≠ NP."
- ❌ "Round-trip is trivial." (when there's real proof engineering involved)
- ❌ "No caveats." (when there are clearly limitations)

Honest framing is **rewarded**. Operator merges honest partial completions; rejects dishonest "complete" claims.

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
  [x] No trust-root edits (verified via git diff)
  [x] Markdown-only: no Lean edits (git diff origin/main -- "*.lean" empty)
      OR Lean-task: lake build PnP3 Pnp4 → green;
                    ./scripts/check.sh → green;
                    rg sorry|admit -g"*.lean" pnp3 pnp4 → empty;
                    smoke test in AlgorithmsToLowerBoundsSurfaceTests.lean;
                    #print axioms entries in AxiomsAudit.lean
  [x] Doc-comment honestly describes scope

Acceptance criteria (task-specific):
  [x] / [ ] <each item from your task file>

For Lean tasks — landed signatures:
  - <name> : <type>
  - ...

For markdown tasks — report sections:
  - <summary>

Honest caveats:
  - <list any place where deliverable falls short of literal task spec, or where
    you took a design liberty>

Commands run:
  - <list per §8>

Self-attack notes:
  - <what you checked during your 10-minute adversarial review>

Scope violations: none / <list>
```

---

## 13. Final reminders

- **This phase is infrastructure + operator situational awareness**, not P ≠ NP progress. Don't overclaim.
- **Trust-root files are read-only.** No exceptions.
- **Parsers and encoders must remain computable.** No `noncomputable def`, no `Classical.choose` in core data definitions. A11 anti-faking discipline.
- **Honest partial completion is good**; dishonest "complete" is rejected.
- **Time-box at 1.5× the estimate.** If exceeding, write a failure report.
- **Self-attack before submitting.** 10 minutes minimum.
- **One task per engineer.** Don't grab multiple.
- **Only authorised task IDs.** Operator-prompted only. No L/B/K/X dispatch.

Good luck. The contract-expansion track is the only active engineering track right now; everything else is markdown hygiene.
