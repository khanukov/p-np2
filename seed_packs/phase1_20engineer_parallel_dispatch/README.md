# Phase 1 — Wave 1 audits complete; A11 synthesis pending

## Status

**Wave 1 audits: 10 of 10 landed.** A11 synthesis is the **next active task**. No L/B/K/X dispatch until A11 lands and operator decides.

## What landed (wave 1)

| ID | Report | Lines | Verdict | Key finding |
|---|---|---|---|---|
| A01 | `audit_reports/A01_pnp3_magnification_partial_codex.md` | 466 | PARTIAL_BUT_USEFUL | `FormulaSupportRestrictionBoundsPartial` legacy/refuted-risk; `_fromPipeline` predicates safer staged replacement; 42 `Classical.choose` in `LocalityProvider_Partial.lean`. |
| A02 | `audit_reports/A02_pnp3_finalresult_auditor.md` | 493 | PARTIAL_BUT_USEFUL | Pipeline complete only modulo `ResearchGapWitness`; canonical conditional endpoints kernel-wired; refuted/vacuous quarantine routes named visibly; no pnp4 adapter to `ResearchGapWitness`. |
| A03 | `audit_reports/A03_pnp3_ac0_bridges_gpt55.md` | 470 | PARTIAL_BUT_USEFUL | `FormulaSemanticMultiSwitchingProvider` audit-marked refuted-channel; internal singleton provider satisfies empty-witness route; `AsymptoticDAGCollapse` is only conditional DAG endpoint. |
| A04 | `audit_reports/A04_pnp3_barrier_gpt55.md` | 598 | PARTIAL_BUT_USEFUL | 4 trust-root barrier files ~200 LOC; `BarrierBypassPackage` is Prop wrapper not certificate; no active bypass-witness constructions. |
| A05 | `audit_reports/A05_pnp3_lowerbounds_codex.md` | 372 | PARTIAL_BUT_USEFUL | Kernel-checked anti-checker + locality contradictions for partial-MCSP; DAG/stable-restriction chain with conditional `NP_not_subset_PpolyDAG` endpoints; `FailedRoute_*` legacy quarantine. |
| A06 | `audit_reports/A06_pnp3_models_complexity_codex.md` | 568 | PARTIAL_BUT_USEFUL | Kernel-checked partial truth-table + decision/promise surfaces + `P_subset_PpolyDAG` upper-bound route; fixed-slice DAG→Formula hardwiring theorem not-to-be-overgeneralized. |
| A07 | `audit_reports/A07_pnp4_algorithmstolowebounds_codex.md` | 581 | PARTIAL_BUT_USEFUL | 24 files ~6,687 LOC; kernel-checked finite-slice MCSP + coin + masking + local-PRG transfer; published lower bounds packaged as contract structures; no `VerifiedNPDAGLowerBoundSource` construction. |
| A08 | `audit_reports/A08_pnp4_frontier_codex.md` | 568 | (operator-dispatched outside main wave) | pnp4/Pnp4/Frontier/* incl. ContractExpansion audited. |
| A09 | `audit_reports/A09_nogolog_formal_witnesses_codex.md` | 312 | PARTIAL_BUT_USEFUL | All 8 non-null `formal_witness` entries point to existing kernel-checked declarations; NOGO-000002/000004/000005 use stale line anchors; NOGO-000003 is `needs_review` with no witness. |
| A10 | `audit_reports/A10_partial_legacy_markers_codex.md` | 1,266 | PARTIAL_BUT_USEFUL | Repo-wide scan: 34 `_Partial`/`_Legacy`, 37 `placeholder`, 274 `Classical.choose`, 505 `noncomputable def`. Hotspots: `LocalityProvider_Partial`, `Facts_Switching`, `Simulation`, `FinalResultMainline`, `FinalResultAuditRoutes`, `UnconditionalResearchGap`. |

Total audit volume: ~5,694 lines of markdown across 10 reports.

Closed duplicates: PR #1299, #1305 (alternate A01 codex variants; #1306 selected).

## What is next — A11 synthesis (only active task)

| ID | Task | Time | Type |
|---|---|---|---|
| [A11](tasks/A11_wave1_synthesis.md) | Synthesis of A01–A10 + wave-2 decision memo | 1 wk | markdown-only |

**A11 is gating.** It is the synthesis pass that turns 10 audit reports into a single operator-decision memo: cross-audit consensus map, refuted/vacuous quarantine inventory, math-level bottleneck status per candidate path, wave-2 decision matrix per deferred task (L01, L02, B01, B02, B03, K01, K02, X01, X02), prioritized cross-cutting cleanup items, and a single recommended wave-2 size (0–N).

Until A11 lands and the operator decides based on it, **no L/B/K/X dispatch happens**.

## Deferred — pending A11 outcome

The following 9 task files exist under `tasks/` with DEFERRED headers. **Do not dispatch any of these.** A11 will recommend per-task whether to dispatch, defer further, or cancel.

- L01, L02 (literature: Hirahara search-to-decision MCSP, Pich-Santhanam unprovability)
- B01, B02, B03 (barriers: Razborov-Rudich, Relativization, Algebrization — pnp4 extensions)
- K01, K02 (kill-machine: cross-route NoGo checker, pre-dispatch barrier classifier)
- X01 (PolyTimeVerifierSpec + NP_TM bridge — D0-endorsed)
- X02 (concrete tree-MCSP parser — spec needs rewrite to consume `treeMCSPPrefixAmbientLength`)

X01 is the only Lean task; it remains gated on A11 even though no audit directly contradicts dispatching it — wave-1 evidence may change the priority or scope.

## Cross-cutting consensus from wave 1 (pre-synthesis snapshot)

This is a quick snapshot only; A11 will produce the authoritative synthesis.

- **No hidden shorter route.** No audit found a path that bypasses the math-level `ResearchGapWitness` bottleneck.
- **Engineering is compartmentalized and axiom-clean.** pnp3: 0 sorry, 0 admit, 0 axiom-decl, 6 opaque, 9 Fact (staged routes); pnp4: fully clean.
- **Refuted/vacuous routes are well-quarantined but still callable.** A02, A03, A05 all flag the same support-bounds and singleton-provider risks.
- **No pnp4↔pnp3 final-boundary adapter** from `VerifiedNPDAGLowerBoundSource` to `ResearchGapWitness` (A02, A07, A08).
- **NoGoLog integrity is mostly intact** with 3 stale anchors and 1 `needs_review` entry to clean up (A09).
- **Cross-cutting hotspots:** `LocalityProvider_Partial.lean`, `Facts_Switching.lean`, AC0 multiswitching provider surfaces (A01, A03, A10).

A11 will turn these into a wave-2 decision and a prioritized cleanup list.

## Repository reality (recap)

`UnconditionalResearchGap.lean` proves `P_ne_NP_final (gap : ResearchGapWitness) : P_ne_NP`. The mathematical bottleneck is a non-vacuous `ResearchGapWitness` source — equivalent to a real proof of `NP_not_subset_PpolyDAG`. Wave 1 audits confirm this remains the only mathematical gap.

## Status header

```
Wave: 1 (audits complete)
Audits landed: 10 of 10 (A01–A10)
Next active task: A11 synthesis (markdown-only, 1 week, gating)
Wave 2 (L/B/K/X): blocked on A11 + operator decision
```

## Cross-references

- `seed_packs/phase1_20engineer_parallel_dispatch/AUDIT_2026-05-17_PLAN_REDUCTION.md` — pre-audit reduction memo (now superseded by wave-1 evidence; A11 produces the post-audit decision).
- `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` — FP3b context.
- `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` — X01 rationale (still relevant post-A11 if X01 is dispatched).
- `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — required reading for the A11 worker.
