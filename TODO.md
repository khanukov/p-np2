# TODO / Roadmap (current)

Updated: 2026-03-15

Canonical blocker checklist lives in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release checklist/w wording guardrail: `RELEASE_RC.md`.

## Snapshot

- Active `axiom` in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- Baseline checks: `./scripts/check.sh` and current audit tests pass
- Final API remains conditional (`pnp3/Magnification/FinalResult.lean`)

## What is already closed

1. AC0/formula separation wiring is present and compiles.
2. Internal linear step-spec provider is closed:
   `stepCompiledLinearCandidateStepSpecProvider_internal`.
3. Linear route has closed internal size and correctness witnesses:
   `compiledRuntimeCircuitSizeBoundLinear_internal`,
   `compiledRuntimeAcceptCorrectnessLinear_internal`.
4. Axiom/sorry hygiene is clean in active `pnp3/`.

## What still blocks unconditional `P ≠ NP`

1. Internalize `hNPDag`: `NP_not_subset_PpolyDAG`.

Inclusion-side status:

1. Closed no-arg evaluator/output-wire agreement:
   `compiledAcceptOutputWireAgreementLinear_internal`.
2. Closed no-arg inclusion endpoint:
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
3. Default `P_ne_NP_final*` wiring already consumes this no-arg
   inclusion endpoint.

## A3 + A4 milestone (closed in active route)

Status: closed on 2026-03-14 in active `Magnification.FinalResult` API.

What was changed:

1. Removed hidden pointwise-at-`N0` use from active final endpoints:
   `NP_not_subset_PpolyFormula_final*` and `NP_not_subset_PpolyReal_final*`
   now take explicit `(n, hn : N0 ≤ n)`.
2. Replaced fixed-parameter NP-family wrapper with asymptotic NP bridge package:
   `AsymptoticNPPullback` carries
   `NP_strict (gapPartialMCSP_AsymptoticLanguage spec)` and per-`n` strict NP
   witnesses for `gapPartialMCSP_Language (pAt n hn)`.
3. Removed now-obsolete intermediate wrappers:
   old `StrictGapNPFamily` / `GapPartialMCSPTMWitnessFamily` path is deleted.
4. Constructive TM route no longer requires an external NP pullback function:
   `toFixed` is internalized from explicit TM-witness streams.
5. Barrier wrapper no longer hardcodes `N0`; it now takes explicit `(n, hn)`.

Verification:

1. `lake build` passes.
2. `lake build 2>&1 | rg "warning:"` is empty.
3. Regression/audit tests compile with the new signatures
   (`Tests/BridgeLocalityRegression`, `Tests/AxiomsAudit`, barrier audits).

## A9 milestone (closed end-to-end in active route)

Status: closed on 2026-03-14 in `Magnification.AC0LocalityBridge`.

What was changed:

1. `FormulaSupportBoundsFromMultiSwitchingContract` now requires an explicit
   semantic link: some `f ∈ F` extensionally equals the extracted formula
   semantics `FormulaCircuit.eval c` (after length cast).
2. Removed the vacuous reverse constructor
   `multiswitching_contract_of_formula_support_bounds` that previously built
   the contract via an unrelated empty AC0 family.
3. Added audit helper theorem `AC0LocalityBridge.package_semantic_link` and
   wired it into `Tests/AxiomsAudit`.
4. Added `formula_support_bounds_and_semantic_link_from_multiswitching` so the
   active locality bridge exports both numeric bounds and semantic linkage in
   one theorem (link no longer disappears at the projection boundary).
5. Added a split-constructor path:
   `multiswitching_contract_of_semantic_provider_and_support_bounds` builds the
   full strengthened A9 contract from two independent inputs:
   semantic AC0/multi-switching provenance + numeric support bounds.
6. Added an internal constructive semantic provider:
   `formulaSemanticMultiSwitchingProvider_internal`.
7. Added a fully internalized constructor:
   `multiswitching_contract_internalized_of_support_bounds` derives the
   strengthened A9 contract directly from support-bounds assumptions.

Interpretation:

1. The contract can no longer be satisfied by a completely irrelevant AC0
   family payload.
2. Semantic linkage is now constructive in-repo (internal provider exists),
   while numeric obligations remain exactly the explicit support-bounds inputs.

## A8 milestone (closed in canonical CCDT bridge)

Status: closed on 2026-03-14 in `ThirdPartyFacts.Facts_Switching`.

What was changed:

1. Added constructive `LeafPartitionWithin` framework for canonical trees.
2. Proved canonical CNF DT leaf completeness/uniqueness on compatible inputs:
   `canonicalDT_CNF_aux_leaf_of_compatible`,
   `canonicalDT_CNF_aux_leaf_unique_of_compatible`.
3. Proved leaf refinement-to-root for both canonical DT and canonical CCDT:
   `canonicalDT_CNF_aux_leaves_refine_root`,
   `canonicalCCDT_CNF_aux_leaves_refine_root`.
4. Proved canonical CCDT leaf partition at free root:
   `canonicalCCDT_CNF_aux_leafPartition_free`.
5. Removed external `hpart : LeafPartition ...` argument from
   `shrinkage_negDnfFamily_to_dnf_canonicalCCDT`; partition is now derived
   internally from canonical CCDT structure.

Verification:

1. `lake build pnp3/ThirdPartyFacts/Facts_Switching.lean` passes.
2. `lake build` passes.
3. `./scripts/check.sh` passes.

## Active next step: asymptotic formula-collapse (current focus)

Status: in progress on 2026-03-15 for active `codex-refactoring` route.

Scope:

1. Primary target is formula-track only:
   unconditional `NP_not_subset_PpolyFormula` via asymptotic language collapse.
2. This does not close unconditional `P ≠ NP`; DAG blocker
   `NP_not_subset_PpolyDAG` remains independent.
3. Fixed-slice (`gapPartialMCSP_Language p`) theorems stay as helper lemmas, not
   the final claim surface for this milestone.

Main theorem target:

1. Add a direct asymptotic collapse theorem (no external provider/transfer
   assumptions in theorem statement):
   `asymptotic_formula_collapse (spec) :
      PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False`.

Implementation plan:

1. Add `pnp3/Magnification/AsymptoticFormulaCollapse.lean` and keep the collapse
   proof there as the single source of truth for formula-target finalization.
2. Internalize support-bounds extraction as a constructive theorem:
   `formula_support_bounds_internal : FormulaSupportRestrictionBoundsPartial`.
3. Build `StructuredLocalityProviderPartial` internally from support bounds
   (through existing certificate/engine constructors), without default
   `Nonempty` wrappers in the core proof path.
4. Rewire `FinalResult.lean` so active formula finals are grounded in the new
   asymptotic collapse theorem; keep fixed-slice route only as supporting lemmas.
5. Resolve `strictAsymptotic`/`strictFixed` mismatch:
   ensure the active proof path consumes the asymptotic witness directly and
   keeps slice witnesses auxiliary.
6. Add audit/regression checks so formula-final regressions cannot silently
   reintroduce external provider-style assumptions in the core theorem.

Progress (2026-03-15):

1. Added `pnp3/Magnification/AsymptoticFormulaCollapse.lean` as the dedicated
   collapse module for this milestone.
2. Added explicit constructive bridge helpers in that module:
   `ppolyFormula_fixed_of_asymptotic_slice`,
   `asymptotic_formula_collapse_of_slice_agreement`,
   and strict-NP wrapper
   `NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse`.
3. Rewired `FinalResult.lean` so
   `NP_not_subset_PpolyFormula_final_with_provider` now consumes
   `hNPbridge.strictAsymptotic` on the active path (instead of relying on
   `strictFixed` as the endpoint input).
4. Added explicit `sliceEq` to `AsymptoticFormulaTrackHypothesis`; active
   `asymptotic_formula_collapse` now obtains slice agreement from this package
   directly (no extra theorem argument at call sites).
5. Removed obsolete intermediate formula-final wrapper that duplicated the old
   fixed-slice endpoint route.
6. Moved active `MagnificationAssumptions.switching` payload from a raw
   `StructuredLocalityProviderPartial` field to
   `FormulaSupportRestrictionBoundsPartial`; provider is now derived internally
   at formula/real final wrappers.
7. Added provider-free formula/real final wrappers:
   `NP_not_subset_PpolyFormula_final_with_supportBounds`,
   `NP_not_subset_PpolyReal_final_with_supportBounds`.
8. Raised final switching boundary to the strengthened A9 contract:
   `MagnificationAssumptions.switching` now carries
   `FormulaSupportBoundsFromMultiSwitchingContract`, and active
   `NP_not_subset_PpolyFormula_final` / `NP_not_subset_PpolyReal_final`
   derive support-bounds internally via
   `formula_support_bounds_from_multiswitching`.

Remaining for this milestone:

1. Internalize
   `formula_support_bounds_internal : FormulaSupportRestrictionBoundsPartial`.
2. Build provider construction from that internal theorem in the core route,
   so the asymptotic collapse no longer depends on externally passed
   `StructuredLocalityProviderPartial`.
3. Promote a direct theorem surface
   `PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False`
   without external provider parameters.

Acceptance criteria for this milestone:

1. A direct theorem of the shape
   `PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False` compiles in
   active code.
2. Active formula-separation final endpoint is derived from this theorem.
3. `./scripts/check.sh` and existing audits remain green.
4. Documentation explicitly distinguishes:
   formula-track unconditional target vs DAG-side `P ≠ NP` blocker.

## Execution order

1. Keep docs honest: no unconditional claim while DAG blockers remain.
2. Complete asymptotic formula-collapse milestone above.
3. Then continue DAG-side work (`NP_not_subset_PpolyDAG`) for unconditional
   `P ≠ NP`.
4. Only after (3), switch global wording to unconditional.

## Done criteria

1. Final route no longer needs external DAG separation input.
2. `./scripts/check.sh` and current audit tests pass unchanged.
3. Top-level docs report unconditional status consistently.
