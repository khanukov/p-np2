# Phase 1 — Wave 1 status (post-audit landing)

## Status

**Wave 1 audits: LANDED.** 9 of 10 audit reports merged to main (commits `833f93c`..`9545867`). A08 missing (no worker dispatched). X01 not yet dispatched.

The reduced-wave plan written in `AUDIT_2026-05-17_PLAN_REDUCTION.md` (kept A02, A07, A09, A10 + X01, with A02 optional) was pre-empted by an operator dispatch of all 10 audits before that plan reduction landed on main. The 5 originally-deferred audits (A01, A03, A04, A05, A06) also completed and were merged because they are markdown-only with zero shared-file collision cost; merging them expands operator situational awareness without slowing anything.

This file is now a status board, not a dispatch spec.

## What landed (wave 1)

| ID | Report | Lines | Verdict | Key finding |
|---|---|---|---|---|
| A01 | `audit_reports/A01_pnp3_magnification_partial_codex.md` | 466 | PARTIAL_BUT_USEFUL | `FormulaSupportRestrictionBoundsPartial` legacy/refuted-risk; `_fromPipeline` predicates safer staged replacement; 42 `Classical.choose` in `LocalityProvider_Partial.lean`. |
| A02 | `audit_reports/A02_pnp3_finalresult_auditor.md` | 493 | PARTIAL_BUT_USEFUL | Pipeline complete only modulo `ResearchGapWitness`; canonical conditional endpoints kernel-wired; refuted/vacuous quarantine routes (`RefutedRoute_*`/`Vacuous_*`) named visibly; no pnp4 adapter to `ResearchGapWitness`. |
| A03 | `audit_reports/A03_pnp3_ac0_bridges_gpt55.md` | 470 | PARTIAL_BUT_USEFUL | `FormulaSemanticMultiSwitchingProvider` audit-marked refuted-channel; internal singleton provider satisfies empty-witness route; `AsymptoticDAGCollapse` is only conditional DAG endpoint. |
| A04 | `audit_reports/A04_pnp3_barrier_gpt55.md` | 598 | PARTIAL_BUT_USEFUL | 4 trust-root barrier files ~200 LOC; `BarrierBypassPackage` is Prop wrapper not certificate; no active bypass-witness constructions. |
| A05 | `audit_reports/A05_pnp3_lowerbounds_codex.md` | 372 | PARTIAL_BUT_USEFUL | Kernel-checked anti-checker + locality contradictions for partial-MCSP; DAG/stable-restriction chain with conditional `NP_not_subset_PpolyDAG` endpoints; `FailedRoute_*` legacy quarantine. |
| A06 | `audit_reports/A06_pnp3_models_complexity_codex.md` | 568 | PARTIAL_BUT_USEFUL | Kernel-checked partial truth-table + decision/promise surfaces + `P_subset_PpolyDAG` upper-bound route; fixed-slice DAG→Formula hardwiring theorem not-to-be-overgeneralized. |
| A07 | `audit_reports/A07_pnp4_algorithmstolowebounds_codex.md` | 581 | PARTIAL_BUT_USEFUL | 24 files ~6,687 LOC; kernel-checked finite-slice MCSP + coin + masking + local-PRG transfer; published lower bounds packaged as contract structures (Prop fields); no `VerifiedNPDAGLowerBoundSource` construction. |
| **A08** | **MISSING** | — | — | **No worker dispatched** for `pnp4/Pnp4/Frontier/` incl. ContractExpansion. Needs separate dispatch. |
| A09 | `audit_reports/A09_nogolog_formal_witnesses_codex.md` | 312 | PARTIAL_BUT_USEFUL | All 8 non-null `formal_witness` entries point to existing kernel-checked declarations; NOGO-000002/000004/000005 use stale line anchors; NOGO-000003 is `needs_review` with no witness. |
| A10 | `audit_reports/A10_partial_legacy_markers_codex.md` | 1,266 | PARTIAL_BUT_USEFUL | Repo-wide scan: 34 `_Partial`/`_Legacy`, 37 `placeholder`, 24 TODO|FIXME|XXX|HACK, 274 `Classical.choose`, 505 `noncomputable def`, 13 axiom doc-refs. Hotspots: `LocalityProvider_Partial`, `Facts_Switching`, `Simulation`, `FinalResultMainline`, `FinalResultAuditRoutes`, `UnconditionalResearchGap` (noncomputable `researchGapWitness` placeholder). |

Cross-cutting consensus across all 9 reports: **no audit found a hidden shorter route to `P != NP` or to `NP_not_subset_PpolyDAG`**. The mathematical gap remains the bottleneck.

Closed duplicates: PR #1299, PR #1305 (alternate A01 codex variants). PR #1306 selected.

## What is still pending

### Pending — needs dispatch

| ID | Task | Status |
|---|---|---|
| A08 | Audit `pnp4/Pnp4/Frontier/*` incl. `ContractExpansion/` (~1,200 LOC) | **No worker dispatched in wave 1.** Operator should dispatch separately. Task file at `tasks/A08_audit_pnp4_frontier.md` is still valid. |
| X01 | `PolyTimeVerifierSpec` + bridge to `NP_TM` (Option B.1 from D0) | **Not yet dispatched.** Task file at `tasks/X01_polytimeverifierspec_bridge.md` is still valid. Only Lean task in the wave. |

### Deferred (no marginal value this phase)

L01, L02, B01, B02, B03, K01, K02, X02 — see per-task `DEFERRED` headers in `tasks/` and per-task rationale in `AUDIT_2026-05-17_PLAN_REDUCTION.md`. X02 specifically requires rewriting the spec to consume `treeMCSPPrefixAmbientLength` before reactivation.

## Wave 2 (provisional, operator decision)

After A08 + X01 land, wave 2 is an operator decision:
- **Stop** if audits confirm no hidden shorter route and X01 + A08 ship clean. Engineering closeout complete; bottleneck is math-level (`ResearchGapWitness` source).
- **Dispatch rewritten X02** if operator wants to continue contract-expansion; X02 spec must be rewritten to consume `treeMCSPPrefixAmbientLength` (the live runtime convention in `PrefixExtensionLanguageRuntime.lean`), and gated on X01 merged.

No pre-commitment to wave 2.

## Cross-cutting operator-decision items from the 9 audits

These were surfaced as Phase 1+ recommendations across multiple audit reports; the operator can choose to act, defer, or ignore:

1. **NoGoLog anchor repair (from A09).** Update line anchors for NOGO-000002, NOGO-000004, NOGO-000005; decide whether NOGO-000003 needs a formal witness or remains `needs_review`.
2. **Provider/Default quarantine (from A01, A03, A10).** Many `hasDefault*` / `default*` provider names in `LocalityProvider_Partial.lean` and AC0 bridges create hidden-payload risk if used as ambient facts. Consider rename/quarantine pass.
3. **Old vs `_fromPipeline` support-bounds visibility (from A01, A03).** `FormulaSupportRestrictionBoundsPartial` is documented as inconsistent/refuted but compatibility theorems still callable. Markdown quarantine note proposed.
4. **pnp3↔pnp4 MCSP crosswalk (from A06, A07).** No adapter currently exists between pnp3 `gapPartialMCSP_Language` and pnp4 `SearchMCSPCompressionProblem`. A markdown crosswalk would prevent duplicate engineering.
5. **`RefutedRoute_*` naming review (from A02).** Some pipeline-aware wrappers in `FinalResultAuditRoutes.lean` have `RefutedRoute_` names but comments call them non-ex-falso. Naming/documentation cleanup proposed.

Each is markdown-only or low-risk Lean test; none change the math-level bottleneck.

## Repository reality (recap)

`UnconditionalResearchGap.lean` proves `P_ne_NP_final (gap : ResearchGapWitness) : P_ne_NP`. The mathematical bottleneck is a non-vacuous `ResearchGapWitness` source — equivalent to a real proof of `NP_not_subset_PpolyDAG`. Wave 1 audits confirm this remains the only mathematical gap; engineering is otherwise compartmentalized and axiom-clean (`pnp3`: 0 sorry, 0 admit, 0 axiom-decl; `pnp4`: fully clean).

## Cross-references

- `RESEARCH_CONSTITUTION.md` — overarching discipline.
- `seed_packs/phase1_20engineer_parallel_dispatch/AUDIT_2026-05-17_PLAN_REDUCTION.md` — original reduction memo (now superseded by this status board for wave 1 outcomes).
- `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` — FP3b context.
- `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` — X01 rationale.
- `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — required reading for A08/X01 workers.

## Status header

```
Wave: 1 (audits landed; A08 + X01 still pending)
Audits landed: 9 of 10 (A01, A02, A03, A04, A05, A06, A07, A09, A10)
Audits missing: 1 (A08 — needs separate dispatch)
Lean tasks pending: 1 (X01)
Wave 2: operator decision after A08 + X01 synthesis (no pre-commitment)
```
