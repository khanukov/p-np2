# Proof Overview (Auditor Guide)

Updated: 2026-05-28

This file is the short auditor-oriented map of the active proof route in the
current repository state.

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current interim release posture:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Russian-language frontier FAQ (more detailed, authoritative narrative source):
`pnp3/Docs/Unconditionality_FAQ_ru.md`.

## 1. Pipeline shape

Active code path remains:

`SAL -> Covering/Lower Bounds -> anti-checker -> magnification -> DAG final wrappers`.

The single-file frontier where the remaining unconditional gap lives is:

`pnp3/Magnification/UnconditionalResearchGap.lean`.

The compatibility import path for the historical aggregator is
`pnp3/Magnification/FinalResult.lean`; the implementation aggregator is
`pnp3/Magnification/FinalResultCore.lean`.

## 2. Final theorem ladder in code

The active ladder has one honest public closure boundary plus several layers
of explicit compatibility/audit wrappers.

### Public default closure boundary

Both are defined in
`pnp3/Magnification/UnconditionalResearchGap.lean`:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

The single mathematical input is `ResearchGapWitness.dagSeparation`, of type
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

### Audit / legacy wrappers (not the public closure boundary)

In `pnp3/Magnification/FinalResultAuditRoutes.lean`:

1. `P_ne_NP_final_of_magnification (hMag : MagnificationAssumptions)`
2. `P_ne_NP_final_of_asymptoticPullback (hMS, hAsym, hNPbridge)`
3. `P_ne_NP_final_of_multiswitchingData (hMS, D)`
4. fixed-slice / promise-YES / iso-strong route wrappers
5. various `NP_not_subset_PpolyDAG_final_of_*` companions

These all consume assumptions (`MagnificationAssumptions`,
`FormulaSupportBoundsFromMultiSwitchingContract`,
`FormulaSupportBoundsPartial_fromPipeline`, ...) that the falsifiability audit
has formally refuted.  They compile, but they route through inconsistent
assumptions; they are kept only for import stability and audit attribution.

### Additional fixed-slice / asymptotic DAG surfaces

In `FinalResultMainline` and related modules:

1. `NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse`
2. `NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction`
3. `NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure`
4. `NP_not_subset_PpolyDAG_final_of_asymptotic_blocker`
5. companion `P_ne_NP_final_of_*` wrappers for the same fixed-slice routes

These are conditional theorem surfaces, useful for tracking precise data
shapes, but they are not the public closure boundary.

### Concrete fixed-slice `_TM` DAG surfaces

In `FinalResultLegacyTM` and related modules:

1. `NP_not_subset_PpolyDAG_final_of_blocker_TM`
2. `P_ne_NP_final_of_blocker_TM`
3. related `_TM` wrappers from stable restriction / source closure /
   support-bounds bridges

These are likewise conditional compatibility surfaces, not the public closure
boundary.

## 3. Current explicit boundary assumption

The public default theorem is:

```text
P_ne_NP_final
  (gap : ResearchGapWitness)
```

Interpretation:

1. Inclusion side is internalized as
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
2. DAG separation is routed through `NP_not_subset_PpolyDAG_final gap`, where
   `gap.dagSeparation : NP_not_subset_PpolyDAG` is the entire remaining
   mathematical input.
3. There is no `hMag`, `hMS`, `hAsym`, `hNPbridge`, or provider parameter on
   the default theorem.

## 4. What is closed

Closed in the active tree:

1. buildable active route and public default wrappers;
2. axiom/sorry hygiene for active `pnp3/`;
3. inclusion-side internalization via `proved_P_subset_PpolyDAG_internal`;
4. DAG endpoint plumbing (fixed-slice / asymptotic / `_TM` / source-closure /
   blocker / Route-B wrappers);
5. falsifiability audit for legacy support-bounds and multi-switching surfaces
   (all formally refuted to `False`);
6. canonical witness-density and support-half fallback closure;
7. current audit / regression test suite;
8. iso-strong route class formally retired at the canonical asymptotic
   instantiation (see `STATUS.md` for the post-PR13 chain).

## 5. What is open

Still open:

1. a non-vacuous proof of `ResearchGapWitness`, equivalently
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`, that does not route through
   the refuted support-bounds / multi-switching surfaces;
2. a zero-argument public theorem `P_ne_NP_unconditional`, currently kept as
   a commented template inside
   `pnp3/Magnification/UnconditionalResearchGap.lean`.

The remaining gap is a research-level lower-bound problem, not a missing
wrapper.  The `ResearchGapWitness` port is method-agnostic: an algebraic,
spectral, finite-field, SOS, or Fourier-analytic proof of
`NP_not_subset_PpolyDAG` is admissible, and is not required to produce
support sets, AC0 provenance, random restrictions, or
`AcceptedFamilyCertificateAt`.

## 6. Current recommended audit reading

If the goal is to understand the real blocker rather than the packaging:

1. `pnp3/Magnification/UnconditionalResearchGap.lean` — the single-file
   research-gap frontier.
2. `pnp3/Magnification/FinalResultMainline.lean` — anti-checker / DAG mainline.
3. `pnp3/Magnification/FinalResultAuditRoutes.lean` — the refuted legacy
   wrappers, kept for attribution.
4. `pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean`.
5. `pnp3/Magnification/AC0LocalityBridge.lean`.
6. `pnp3/Magnification/AsymptoticFormulaCollapse.lean`.

## 7. Minimal verification script

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean \
         pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean; do
  lake env lean "$f"
done
rg -n "^theorem P_ne_NP_final\b|^theorem NP_not_subset_PpolyDAG_final\b" \
  pnp3/Magnification/UnconditionalResearchGap.lean
```

## 8. Documentation policy

Use these files as the active source of truth:

1. `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
2. `STATUS.md`
3. `TODO.md`
4. `AXIOMS_FINAL_LIST.md`
5. `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`
6. `pnp3/Docs/Unconditionality_FAQ_ru.md`

Historical notes in `archive/` remain non-authoritative.
