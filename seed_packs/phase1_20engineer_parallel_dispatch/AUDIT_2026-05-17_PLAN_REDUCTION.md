# Audit 2026-05-17 — plan reduction from 19 tasks to reduced wave of 6

## Verdict

**RED** on the 19-task dispatch plan as written in commits `63fa68b` and `6397c1b`.

**GREEN** on a reduced first wave of **A02 + A07 + A08 + A09 + A10 + X01** (6 tasks).

**AMBER** on X02 — only after X01 lands AND X02 spec is rewritten to align with the runtime convention already in `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`.

**DEFERRED this phase** — L01, L02, B01, B02, B03, K01, K02. Task files retained as record but flagged with a DEFERRED header. Not dispatchable until specific issues below are addressed.

This memo supersedes the dispatch sizing in `README.md` and the engineer count / ID scheme in `COMMON_WORKER_INSTRUCTIONS.md`. Both files have been rewritten alongside this memo.

## Structural flaws identified

### Flaw 1 — Metadata inconsistency (disabling bug)

`COMMON_WORKER_INSTRUCTIONS.md` was authored before the 20→19 revision and uses the original `E<NN>` ID scheme throughout:

- "engineer E<NN> in a parallel dispatch of 20 independent tasks" (L3)
- `tasks/E<NN>_*.md` (L36) — these files do not exist; actual files are `A01..A10`, `B01..B03`, `K01..K02`, `L01..L02`, `X01..X02`.
- branch convention `khanukov/phase1-E<NN>-<handle>` (L16)
- failures path `failures/E<NN>_<handle>.md` (L270)
- PR title `Phase 1 E<NN>: <title>` (L24)
- diapason-based reading sections: `E14-E16` (barrier), `E17-E18` (kill-machine), `E19-E20` (contract expansion), `E01-E13` (Phase A) — these IDs do not match any task in the revised plan.

Net effect: any engineer reading the binding common doc would use the wrong naming scheme, fail to locate their task file, and follow wrong branch/PR/failure conventions. This is disabling, not cosmetic.

### Flaw 2 — Plan internally contradicts itself

`README.md` revision rationale (L7–11) says Phase 0 audit must come first so subsequent dispatches target real gaps. But L114 says "NO engineer is blocked on another. All 19 tasks dispatch-able NOW." If Phase 0 audit synthesis is the gating signal, Phases 2–5 cannot dispatch in parallel with Phase 0 — they must wait for Phase 0 output.

Additionally, README L25/L101/L157/L198 openly anticipate a second wave "Phase 1+" of 5–15 more tasks before the first wave is even reviewed. A closeout plan should not commit to expanding before evaluating.

### Flaw 3 — "Independent at merge time" is false

Every Lean task per COMMON §4.3 + §4.4 modifies:

- `lakefile.lean` (one `Glob.one` line per new module)
- `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` (one `check_<name>` wrapper per public signature)
- `pnp4/Pnp4/Tests/AxiomsAudit.lean` (one `#print axioms` line per theorem)

Multiple parallel Lean PRs will collide on those three files. Operator merge load is not "~6 hours for 19 PRs" if every Lean PR needs a rebase. Reduced wave mitigates this: only X01 is Lean among the 6 active tasks; the 5 audit tasks are markdown-only.

### Flaw 4 — Specific task design bugs

**X02 — runtime convention mismatch.** Task spec uses `M := fun n => n`:

```
m = (treeMCSPPrefixParserConcrete encoding 0 (fun n => n)).M input.n
```

But `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean:18-21` already fixes the ambient-length convention:

```
treeMCSPPrefixAmbientLength overhead witnessBits padBits n
  = Pnp3.Models.Partial.tableLen n + overhead n + witnessBits n + padBits n
```

`length_convention` theorem in X02 as specified cannot be proven against the live runtime unless X02 is rewritten to target `treeMCSPPrefixAmbientLength`, not `M(n) = n`. **X02 is buggy as written**; before any reactivation it must be rewritten to consume the existing ambient-length convention.

**L01 — bibliographic identifier suspect.** L01 cites Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS 2018, as `arXiv:1804.05985`. The arXiv ID for Hirahara's FOCS 2018 paper is `1808.06848`; `1804.05985` is a different paper. Before any reactivation L01 must verify the source theorem statement against the correct arXiv version and confirm what is actually being formalized.

**B02 / B03 — placeholder-heavy specs.** B02 explicitly allows placeholder relativized predicates and placeholder oracles; its honest caveat acknowledges that making them concrete would require multi-month oracle-TM machinery. B03 defines `algebrizes` as a placeholder, allows `algebraicExtension := True`, and asks only for `True`-valued theorems. These are wrapper surfaces, not kernel-checked barrier theorems. They run against the repo's own anti-circularity discipline (NoGo log NOGO-000008 / 000009 style) and would consume operator review hours without producing operator-decision-useful artifacts.

**K01 / K02 — typed rubrics, not theorem engines.** K01 reduces NoGo applicability to a hand-coded `List (String × NoGoApplicability)` over a `ProofSafetyCertificate` whose fields are bare `Prop`s. K02 stores barrier evidence as `String`. Useful as a documentation/program-management layer once routes are settled — not on the critical path now.

### Flaw 5 — Plan not framed as closeout

The repository's own strategic documents (FP3b retrospective, D0 polynomial-time-formalism scoping) recommend a narrow tranche centered on the actual bottleneck: the math-level `ResearchGapWitness` source, with optional X01-style formalism investment for resumability. The 19-task plan opens 5 new programmatic surfaces (literature, barriers, kill-machine, contract expansion ×2, audits) — none of which alone advances the real bottleneck.

## What the reduced wave is

| ID | Task | Type | Reason for keep |
|---|---|---|---|
| **A02** | Audit `pnp3/Magnification/FinalResult*.lean` (6 files, ~4,091 LOC) | markdown audit | Verifies how the active wrapper consumes `ResearchGapWitness`; optional but high-signal for operator visibility |
| **A07** | Audit `pnp4/Pnp4/AlgorithmsToLowerBounds/` (24 files) | markdown audit | Where AC⁰[p] + MCSP infrastructure lives; live strategy surface |
| **A08** | Audit `pnp4/Pnp4/Frontier/` incl. `ContractExpansion/` | markdown audit | Where R1-A/B/B1/B2/B2a packaged source-theorem layer lives |
| **A09** | Audit `outputs/nogolog.jsonl` formal_witness validation | markdown audit | Checks NoGo witnesses match kernel-checked theorems |
| **A10** | Cross-cutting `_Partial`/`_Legacy`/`TODO`/`Classical.choose` inventory | markdown audit | Repo-wide placeholder map |
| **X01** | `PolyTimeVerifierSpec` + bridge to `NP_TM`, with toy instance | Lean implementation | D0 memo recommends exactly this narrow bridge; only Lean task in the wave |

All audit tasks (A02, A07, A08, A09, A10) produce markdown reports only — zero shared-file collisions. X01 is the single Lean task, so no parallel merge conflict on `lakefile.lean` / `AxiomsAudit.lean` / `AlgorithmsToLowerBoundsSurfaceTests.lean` within this wave.

## What is deferred and why (per task)

| ID | Status | Specific issue |
|---|---|---|
| L01 | DEFERRED | Cited arXiv ID `1804.05985` does not match Hirahara FOCS 2018; correct ID is `1808.06848`. Before reactivation: verify source theorem statement against correct paper. Possibly should be markdown-only literature D0 first. |
| L02 | DEFERRED | Not on critical path; Pich-Santhanam unprovability is a long-horizon investment not aligned with current bottleneck. Re-evaluate after wave 1 synthesis. |
| B01 | DEFERRED | Razborov-Rudich barrier as pnp4 extension produces typed surface, not P-vs-NP closeout signal. Lower priority than X01. |
| B02 | DEFERRED | Spec explicitly authorizes placeholder oracles; honest caveat admits multi-month effort for concrete instances. Not currently useful. |
| B03 | DEFERRED | Spec defines `algebrizes` as `True`-typed placeholder; theorems are `trivial`. Wrapper surface, not kernel-checked barrier. |
| K01 | DEFERRED | Hand-coded NoGo applicability list over bare-Prop certificate; useful as documentation layer post-closeout, not now. |
| K02 | DEFERRED | Barrier evidence stored as `String`; classification rubric, not theorem-producing engine. |
| X02 | DEFERRED until X01 lands AND spec rewritten | Current spec uses `M := fun n => n` which is incompatible with the live `treeMCSPPrefixAmbientLength` convention. Rewrite required before dispatch. |

Original task files are retained under `tasks/` with a DEFERRED header citing this memo, so the design record is preserved.

## What is dropped (not deferred)

- "Phase 1+" preemptive sizing of 5–15 additional tasks: removed from `README.md`. Wave 2 (if any) is an operator decision after wave 1 synthesis, not a pre-committed expansion.
- Phase-2/3/4/5 framing: collapsed. The reduced wave is "5 audits + 1 narrow bridge"; no programmatic surface beyond that.

## Wave 2 (provisional)

After wave 1 lands and operator synthesizes:

- If audits confirm no hidden shorter route and X01 ships clean → **stop**. The bottleneck is math-level, not engineering. Wait for a new lower-bound idea (Hirahara/magnification/AC⁰ route) before opening new infrastructure.
- If X01 ships clean AND there is operator interest in continuing contract-expansion → dispatch **rewritten X02** explicitly gated on X01 and aligned with `treeMCSPPrefixAmbientLength`.
- L01 may be revived only as markdown-only literature D0 with corrected bibliography first.

## Integration policy for shared files

For wave 1 only X01 touches Lean. But to prevent future-wave collisions, the integration operator (not engineers) will own three files:

- `lakefile.lean`
- `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`
- `pnp4/Pnp4/Tests/AxiomsAudit.lean`

Engineers list **what** their PR needs added to these files in the PR description (one `Glob.one` line, one `check_<name>` wrapper, one `#print axioms` line). The integration operator applies the patches centrally during merge. This avoids the original plan's hidden merge-time conflict zone.

## What this memo does not do

- Does not retract earlier closed work (R1-A/B/B1/B2/B2a, falsifiability audit, FP3b retrospective, D0 scoping). All of that is good.
- Does not promote anything to `accepted`.
- Does not edit trust-root files.
- Does not claim the math-level bottleneck is now closer.

## Cross-references

- `seed_packs/phase1_20engineer_parallel_dispatch/README.md` (rewritten)
- `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` (rewritten)
- `seed_packs/phase1_20engineer_parallel_dispatch/tasks/{L01,L02,B01,B02,B03,K01,K02,X02}_*.md` (DEFERRED headers added)
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean` (live runtime convention X02 must align with)
- `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` (FP3b closeout context)
- `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` (D0 X01 rationale)
