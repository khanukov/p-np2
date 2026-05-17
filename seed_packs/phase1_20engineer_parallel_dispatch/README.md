# Phase 1 — A11-gated dispatch

## Status

**LIMITED DISPATCH ONLY.** A11 synthesized Phase 0 as `PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS`; broad implementation dispatch is not authorised.

Current authorised dispatch:

- P1P-01
- P1P-02
- follow-up tasks only by explicit operator authorisation.

No implementation task may start without an explicit operator prompt after A11/P1P documentation is in place. A11 synthesis is required before any Phase 1+ / L / B / K / X implementation wave.

## Critical revision (post-audit)

This dispatch plan was **revised** after discovering substantial existing infrastructure in `pnp3/Magnification/*_Partial.lean`, `pnp3/Magnification/FinalResult*.lean`, `pnp3/LowerBounds/*_Partial.lean`, and `pnp4/Pnp4/AlgorithmsToLowerBounds/*` (~24 files). The original 20-task plan would have duplicated existing work.

**The revised plan front-loads a Phase 0 audit** to map what's actually done, what's partial, what's missing — so subsequent dispatches target real gaps.

## Classification

**Infrastructure / kill-machine acceleration / repo state mapping.**

This phase is **not** P-vs-NP mainline progress. It accelerates the kill-machine by:

1. **Phase 0** — comprehensive audit of existing repo infrastructure (10 tasks).
2. **Phase 2** — formalize literature genuinely missing from repo (2 tasks).
3. **Phase 3** — extend minimal barrier interfaces to kernel-checked theorems (3 tasks).
4. **Phase 4** — industrial-scale kill-machine tooling (2 tasks).
5. **Phase 5** — complete contract_expansion implementation per D0 scoping (2 tasks).

After A11/P1P governance repair, Phase 1+ (completion of partial work) may be redispatched only by explicit operator authorisation. **A11 synthesis is required before any Phase 1+ / L / B / K / X implementation wave.**

## What the repo already has (per pre-dispatch audit)

| Area | Files | LOC | Status |
| --- | --- | --- | --- |
| `pnp3/Magnification/*_Partial.lean` | 6 | ~4,474 | Substantively complete for partial-MCSP variant |
| `pnp3/Magnification/FinalResult*.lean` | 6 | ~4,091 | Main pipeline; needs `ResearchGapWitness` instance |
| `pnp3/LowerBounds/*_Partial.lean` | 2 | ~2,290 | AntiChecker + formula LB chain |
| `pnp3/Barrier/*.lean` | 4 | ~200 | Minimal interfaces; need pnp4-side extensions |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/` | 24 | ? | AC⁰[p] + MCSP infrastructure |
| `pnp4/Pnp4/Frontier/ContractExpansion/` | 4 | ~700 | R1-A, R1-B, R1-B1, R1-B2a |

`UnconditionalResearchGap.lean` confirms: `P_ne_NP_final (gap : ResearchGapWitness) : P_ne_NP` is **already proven**. The only mathematically meaningful gap is producing a `ResearchGapWitness` instance — i.e., a real proof of `NP_not_subset_PpolyDAG`.

## Engineer dispatch

Take **ONE** authorised task by `<TASK_ID>`. Don't take more than one. Current authorised dispatch is P1P-01 and P1P-02 only; every follow-up task requires explicit operator authorisation.

### Common reading (everyone)

Before starting your task:

1. `RESEARCH_CONSTITUTION.md` — discipline rules; binding.
2. `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — universal rules for this phase.
3. **Your specific task file** in `tasks/<TASK_ID>_*.md`.
4. (If your task is Phase 0 audit) The files you're auditing — read carefully.

### Task list

#### Phase 0 — Repo audit (10 tasks, all markdown-only)

| ID | Audit area | LOC scope | Time |
| --- | --- | --- | --- |
| [A01](tasks/A01_audit_pnp3_magnification_partial.md) | `pnp3/Magnification/*_Partial.lean` (6 files) | ~4,474 | 1 wk |
| [A02](tasks/A02_audit_pnp3_finalresult.md) | `pnp3/Magnification/FinalResult*.lean` (6 files) | ~4,091 | 1 wk |
| [A03](tasks/A03_audit_pnp3_ac0_bridges.md) | `pnp3/Magnification/AC0*.lean` + `Asymptotic*Collapse.lean` (~6 files) | ~1,500 | 1 wk |
| [A04](tasks/A04_audit_pnp3_barrier.md) | `pnp3/Barrier/` (4 files) | ~200 | 3 days |
| [A05](tasks/A05_audit_pnp3_lowerbounds.md) | `pnp3/LowerBounds/` (incl `_Partial`) | ~2,290 | 1 wk |
| [A06](tasks/A06_audit_pnp3_models_complexity.md) | `pnp3/Models/` + non-trust-root `pnp3/Complexity/` | varies | 1 wk |
| [A07](tasks/A07_audit_pnp4_algorithmstolowebounds.md) | `pnp4/Pnp4/AlgorithmsToLowerBounds/` (24 files) | ? | 1 wk |
| [A08](tasks/A08_audit_pnp4_frontier.md) | `pnp4/Pnp4/Frontier/*` (incl. ContractExpansion) | ~1,000 | 1 wk |
| [A09](tasks/A09_audit_nogolog_formal_witnesses.md) | `outputs/nogolog.jsonl` formal_witness validation | — | 3 days |
| [A10](tasks/A10_audit_partial_legacy_markers.md) | Cross-cutting search for `_Partial`/`_Legacy`/`TODO`/placeholder | — | 3 days |

**Phase 0 output:** each audit lands one markdown report at `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/<ID>_<area>_<handle>.md` with required sections (see task file).

#### Phase 2 — Literature genuinely missing (2 tasks)

| ID | Title | Time | Difficulty |
| --- | --- | --- | --- |
| [L01](tasks/L01_hirahara_search_to_decision.md) | Hirahara search-to-decision MCSP surface | 2 wks | high |
| [L02](tasks/L02_pich_santhanam_unprovability.md) | Pich-Santhanam bounded arithmetic unprovability surface | 3 wks | high |

#### Phase 3 — Barriers as kernel-checked theorems (3 tasks)

| ID | Title | Time | Difficulty |
| --- | --- | --- | --- |
| [B01](tasks/B01_razborov_rudich_barrier.md) | Razborov-Rudich natural proofs barrier — pnp4 extension | 3 wks | high |
| [B02](tasks/B02_relativization_barrier.md) | Relativization (BGS) barrier — concrete oracle witnesses | 3 wks | high |
| [B03](tasks/B03_algebrization_barrier.md) | Algebrization (Aaronson-Wigderson) barrier | 3 wks | high |

#### Phase 4 — Industrial kill-machine (2 tasks)

| ID | Title | Time | Difficulty |
| --- | --- | --- | --- |
| [K01](tasks/K01_cross_route_nogo_checker.md) | Cross-route NoGo applicability checker library | 2 wks | medium |
| [K02](tasks/K02_pre_dispatch_barrier_classifier.md) | Pre-dispatch barrier classification tool | 2 wks | medium |

#### Phase 5 — Contract expansion completion (2 tasks)

| ID | Title | Time | Difficulty |
| --- | --- | --- | --- |
| [X01](tasks/X01_polytimeverifierspec_bridge.md) | PolyTimeVerifierSpec + bridge to NP_TM (Option B.1) | 3 wks | medium |
| [X02](tasks/X02_concrete_tree_mcsp_parser.md) | Concrete tree-MCSP parser implementation + runtime proofs | 4 wks | medium-high |

#### (Future) Phase 1+ — Completion of partial work

**Not currently dispatched.** Phase 1+ completion work requires A11 synthesis plus explicit operator authorisation before any implementation wave. Future scope may target specific gaps in `pnp3/Magnification/*_Partial.lean`, `FinalResult*.lean`, and `pnp4/Pnp4/AlgorithmsToLowerBounds/` only after that gate.

### A11 dispatch gate and task status summary

A11 is now the governing synthesis for this dispatch pack. The old dependency graph has been superseded: L/B/K/X implementation tasks are **not** globally independent and are **not** dispatchable as a concurrent wave.

Current authorised dispatch:

- P1P-01
- P1P-02
- follow-up tasks only by explicit operator authorisation.

A11 synthesis is required before any Phase 1+ / L / B / K / X implementation wave. No implementation task may start without an explicit operator prompt after A11/P1P documentation is in place.

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

## Acceptance criteria — universal

For every task:

1. ✅ Files at exact paths specified in the task.
2. ✅ For Lean tasks: `lake build PnP3 Pnp4` passes; `./scripts/check.sh` passes.
3. ✅ `rg sorry|admit -g"*.lean" pnp3 pnp4` empty.
4. ✅ For audit tasks: markdown report at expected path with all required sections.
5. ✅ For Lean tasks: smoke tests + `#print axioms` entries where applicable.
6. ✅ PR description uses structured template from COMMON.
7. ✅ No edits to forbidden files (see COMMON).

Operator review target: **< 15 minutes per landed task** for Phase 2-5; **< 30 minutes** for Phase 0 audits (longer because audit reports contain more synthesis).

## Forbidden scope — universal

See `COMMON_WORKER_INSTRUCTIONS.md`. Summary:

- No edits to `pnp3/Complexity/Interfaces.lean`, `pnp3/Magnification/UnconditionalResearchGap.lean`, `pnp3/Barrier/*` (trust roots).
- No edits to existing `pnp3/Magnification/*_Partial.lean`, `FinalResult*.lean`, `AC0*Bridge.lean` files. **Even though Phase 0 audits them, Phase 0 tasks produce markdown reports — NOT Lean edits.** Phase 1+ (separate dispatch) may edit them after operator approval.
- No `sorry` / `admit` / `axiom` / `opaque` / `Fact` / typeclass-payload in committed Lean.
- No `Classical.choose` in core definitions (acceptable in derived proofs if standard exponent extraction; document).
- No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claim.
- No `ProvenanceFilter_v1` promotion.
- No new NoGoLog entries (operator-side action only).

## Output template — every PR

See `COMMON_WORKER_INSTRUCTIONS.md` §12.

## Operator review process

Each completed task lands as one PR to `main`. Operator:

1. Reads the PR description and verifies the acceptance checklist.
2. For Phase 0 audits: spot-checks 2-3 file-state claims against repo reality.
3. For Phase 2-5: spot-checks Lean signatures.
4. Either merges or requests specific changes.
5. Phase 0 audits inform the **Phase 1+ dispatch decision**.

Target: 2-3 audits + 1-2 implementation PRs merged per operator-day during active dispatch.

## What this phase does NOT do

* No P-vs-NP proof.
* No `ResearchGapWitness` construction.
* No new endpoint or final theorem.
* No claim that magnification reaches a strong enough lower bound on its own.

Phase 1 is **strictly infrastructure + repo state mapping**. Its value:
- Phase 0 audits prevent duplicate work in subsequent dispatches.
- Phase 2-5 add genuinely missing infrastructure.
- Phase 1+ (post-audit) completes existing partial work where viable.

## Re-dispatch / failure protocol

If you cannot complete your task within scope, write a structured failure report at:

`seed_packs/phase1_20engineer_parallel_dispatch/failures/<ID>_<your-handle>.md`

Four sections: What was attempted / Where it broke / Local vs global obstruction / What an integrator must know.

## Cross-references

* `RESEARCH_CONSTITUTION.md` — overarching discipline.
* `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` — context for why this phase exists.
* `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` — context for X01/X02.
* `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — required reading.

## Status header

```
Phase: 1 (initial dispatch)
Engineers: 19 (parallel)
  - Phase 0 audit: 10
  - Phase 2 literature: 2
  - Phase 3 barriers: 3
  - Phase 4 kill-machine: 2
  - Phase 5 contract expansion: 2
Phase 1+ (conditional, post-audit): 5-15 additional tasks
Estimated wall-clock to complete Phase 1 initial dispatch: 4 weeks (with full parallelism)
Operator review load Phase 1 initial: ~19 PRs × ~20 min = ~6 operator-hours
Outcome: complete repo state map + targeted infrastructure additions, ready for Phase 1+ completion dispatches
```
