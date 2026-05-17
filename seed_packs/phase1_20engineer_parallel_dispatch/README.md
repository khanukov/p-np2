# Phase 1 — Contract-expansion infrastructure track (P1P-02 line)

## Status

**Wave 1 audits complete (A01–A10 + A11 synthesis).** Contract-expansion parser infrastructure track active and progressing: P1P-01 governance + P1P-02 design + P1P-02L real parser + P1P-02L₂ encoder/length-convention/RuntimeAwarePrefixParser wiring all landed. Next: P1P-02L₃ canonical round-trip.

No broad L/B/K/X dispatch authorised. Every follow-up task requires explicit operator authorisation.

## What landed (wave 1 + P1P track)

### Wave 1 audits (A01–A10) and synthesis

| ID | Report | Verdict | Key finding |
|---|---|---|---|
| A01 | `audit_reports/A01_pnp3_magnification_partial_codex.md` | PARTIAL_BUT_USEFUL | `FormulaSupportRestrictionBoundsPartial` legacy/refuted-risk; safer `_fromPipeline` predicates available |
| A02 | `audit_reports/A02_pnp3_finalresult_auditor.md` | PARTIAL_BUT_USEFUL | Pipeline complete only modulo `ResearchGapWitness`; refuted/vacuous quarantine routes named visibly; no pnp4 adapter to `ResearchGapWitness` |
| A03 | `audit_reports/A03_pnp3_ac0_bridges_gpt55.md` | PARTIAL_BUT_USEFUL | `FormulaSemanticMultiSwitchingProvider` audit-marked refuted-channel; `AsymptoticDAGCollapse` is the only conditional DAG endpoint |
| A04 | `audit_reports/A04_pnp3_barrier_gpt55.md` | PARTIAL_BUT_USEFUL | 4 trust-root barrier files ~200 LOC; `BarrierBypassPackage` is Prop wrapper not certificate |
| A05 | `audit_reports/A05_pnp3_lowerbounds_codex.md` | PARTIAL_BUT_USEFUL | Kernel-checked anti-checker + locality contradictions; `FailedRoute_*` legacy quarantine |
| A06 | `audit_reports/A06_pnp3_models_complexity_codex.md` | PARTIAL_BUT_USEFUL | Kernel-checked partial truth-table + `P_subset_PpolyDAG` upper-bound route |
| A07 | `audit_reports/A07_pnp4_algorithmstolowebounds_codex.md` | PARTIAL_BUT_USEFUL | 24 files ~6,687 LOC; AC0[p]/coin/local-PRG contracts; no `VerifiedNPDAGLowerBoundSource` construction |
| A08 | `audit_reports/A08_pnp4_frontier_codex.md` | PARTIAL_BUT_USEFUL | pnp4 Frontier + ContractExpansion audited |
| A09 | `audit_reports/A09_nogolog_formal_witnesses_codex.md` | PARTIAL_BUT_USEFUL | NOGO-000002/000004/000005 stale anchors; NOGO-000003 `needs_review` |
| A10 | `audit_reports/A10_partial_legacy_markers_codex.md` | PARTIAL_BUT_USEFUL | Repo-wide marker scan; key hotspots inventoried |
| A11 | `audit_reports/A11_phase0_synthesis_codex.md` | PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS | Consensus across all syntheses: no hidden shorter route; only limited Phase 1+ dispatch authorised |

### P1P infrastructure track

| ID | Deliverable | Status |
|---|---|---|
| P1P-01 | `docs/P1P_01_route_map_dispatch_errata_codex.md` (191 lines) | Landed: 5-bucket route map, dispatch status table, 13-item governance errata. |
| P1P-01 governance application | README + COMMON updated with A11-gated dispatch policy | Landed (commit `b796282`). |
| P1P-02 | `docs/P1P_02_prefix_parser_convention_gpt55.md` (364 lines) | Landed: parser convention design — tag, Elias-gamma `n`, fixed-width `i`, `M(n)` ambient length, malformed semantics, round-trip targets, R1-B2a mapping. |
| P1P-02L | `pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean` (202 lines) | Landed: real computable parser, `readBit?`, `readNatBE`, `sliceBits?`, `decodeGamma?` helpers, main `parseTreeMCSPPrefixInput`, `tableLen_le_treeMCSPPrefixM`, `parseTreeMCSPPrefixInput_bad_tag`, `parseTreeMCSPPrefixInput_malformed_rejected`. |
| P1P-02L operator review | `docs/P1P_02L_operator_review_claudeopus.md` (215 lines) | Landed: verdict `approve_P1P02L`. |
| P1P-02L₂ | Same Lean file + 188 lines | Landed: `CanonicalRawTreeMCSPPrefixFields` struct + `Fin`-indexed `natBitBE`/`gammaBit` bit encoders + `encodeTreeMCSPPrefixFields`/`encodeTreeMCSPPrefixInput` computable encoders + `parseTreeMCSPPrefixInput_length_convention` + `treeMCSPRuntimeAwarePrefixParser` R1-B2a wiring with `parser_polynomial_time_in_M` as honest staged `Prop`. |

### What is next

**P1P-02L₃ — canonical parse-encode round-trip:**
- Prove `parseTreeMCSPPrefixInput threshold codec (encodeTreeMCSPPrefixInput input) = some input` for canonical inputs.
- Auxiliary lemmas needed: gamma round-trip (`decodeGamma? (gammaBit n) = some (n, gammaLen n)`), `natBitBE` round-trip, slice/identity round-trips.
- Estimated 150-300 LOC; main proof-engineering risk is `prefixLength_le` proof-irrelevance — mitigated by `CanonicalRawTreeMCSPPrefixFields` separation already in place from P1P-02L₂.
- **No** NP membership claim, **no** R1-C, **no** `RuntimeAwareTreeCircuitCodec` full instantiation, **no** `TreeMCSPPrefixRuntimeBudget` instantiation, **no** source theorem.

After P1P-02L₃ lands, the parser convention surface will be fully ready for any future X01-style PolyTimeVerifierSpec work toward `PrefixExtensionLanguage ∈ NP`. Until then, the polynomial-time formalism gap remains visibly staged via `parser_polynomial_time_in_M : Prop`.

## A11 dispatch gate and task status summary

A11 is the governing synthesis. The original 19-task plan has been replaced by the A11-gated decision: only narrowly-scoped, operator-authorised tasks dispatch.

Current authorised dispatch:

- The P1P-02 → P1P-02L → P1P-02L₂ chain (parser infrastructure track) — landed.
- Next planned: P1P-02L₃ — only by explicit operator authorisation.

| Task(s) | A11 status | Dispatch implication |
| --- | --- | --- |
| B02 | Cancelled as written | Do not dispatch without a replacement scope. |
| B03 | Cancelled as written | Do not dispatch without a replacement scope. |
| B01 | Rewrite required | Redispatch only after concrete barrier-certificate criteria are approved. |
| K01 | Rewrite required | Redispatch only after the NoGo/manual-classification scope is corrected. |
| K02 | Hold until governance repair | Hold until further README/COMMON repair lands (most governance now in place). |
| X01 | Hold pending no-faking / NP-interface review | Do not implement until the bridge cannot accept staged placeholders and the interface review is complete. |
| X02 | Rewrite after parser convention design | P1P-02L/L₂ now provide the parser; X02 should be redesigned around them if reactivated. |
| L01/L02 | Downgrade to markdown | Treat as literature/interface alignment documents, not Lean implementation tasks. |

## Repository reality (recap)

`UnconditionalResearchGap.lean` proves `P_ne_NP_final (gap : ResearchGapWitness) : P_ne_NP`. The mathematical bottleneck is a non-vacuous `ResearchGapWitness` source — equivalent to a real proof of `NP_not_subset_PpolyDAG`. Wave 1 audits confirm this is the only mathematical gap; engineering is otherwise compartmentalized and axiom-clean. The P1P track does not move this bottleneck; it cleanly stages contract-expansion infrastructure so future work can attempt it honestly.

## Cross-cutting items still open (from A11 synthesis)

These are markdown-only or low-risk cleanup items still on the table. Operator may dispatch any of them individually:

- P1P-03: NoGoLog stale-anchor repair plan (markdown-only, A09 evidence)
- P1P-04: Restricted-lower-bound side-track guardrails (markdown-only)
- P1P-05: Existing surface-test gap inventory for pnp4 public theorems
- Provider/default quarantine pass for `LocalityProvider_Partial.lean`
- pnp3↔pnp4 MCSP crosswalk markdown
- `FailedRoute_*` cleanup recommendations from A05

None are gating on the contract-expansion track and none move the math-level bottleneck. They reduce confusion and operator review load.

## Status header

```
Phase 1 status: contract-expansion infrastructure track active
Wave 1: complete (A01-A10 + A11)
P1P track: P1P-01 design + governance + P1P-02 design + P1P-02L parser + P1P-02L₂ encoder/length-conv/RuntimeAware all landed
Next planned: P1P-02L₃ canonical round-trip (operator-authorised only)
L/B/K/X dispatch: not authorised; per-task status in A11 table above
```

## Cross-references

- `RESEARCH_CONSTITUTION.md` — overarching discipline.
- `seed_packs/phase1_20engineer_parallel_dispatch/AUDIT_2026-05-17_PLAN_REDUCTION.md` — pre-audit reduction memo (historical record).
- `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_codex.md` — A11 synthesis verdict.
- `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_01_route_map_dispatch_errata_codex.md` — A11-aligned route map and governance errata.
- `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_02_prefix_parser_convention_gpt55.md` — parser convention design.
- `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_02L_operator_review_claudeopus.md` — operator review of P1P-02L.
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean` — landed parser + encoder + length convention.
- `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` — FP3b context.
- `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` — X01 rationale (still relevant if X01 reactivated post-review).
- `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — universal worker rules.
