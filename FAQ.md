# Frequently Asked Questions

Updated: 2026-05-28

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current milestone release checklist:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Russian-language frontier FAQ (longer, treated as authoritative narrative
source for this English FAQ):
`pnp3/Docs/Unconditionality_FAQ_ru.md`.

## What is currently proved in code?

Active final surface is implemented across:

- `pnp3/Magnification/UnconditionalResearchGap.lean`
  (the honest research-gap frontier and public default endpoints);
- `pnp3/Magnification/FinalResultCore.lean`
  (compatibility aggregation, re-exported by the historical import path
  `pnp3/Magnification/FinalResult.lean`);
- `pnp3/Magnification/FinalResultMainline.lean`
  (anti-checker / DAG mainline);
- `pnp3/Magnification/FinalResultAuditRoutes.lean`
  (legacy / audit-only wrappers around refuted support-bounds and
  multi-switching assumptions);
- `pnp3/Magnification/FinalResultWeakRoutes.lean`
  and `pnp3/Magnification/FinalResultLegacyTM.lean`
  (additional bridge / `_TM` compatibility surfaces).

Public default endpoints are exactly:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

`hMag`, `hMS`, support-bounds, multi-switching, and provider-backed routes
remain as compatibility / audit wrappers under explicit `_of_*` names; they
are not the current public closure boundary.

These all compile on the current tree.

## Is unconditional `P ≠ NP` proved here?

No. The repository still does not contain an unconditional in-repo theorem
`P ≠ NP`.

## Conditional on what exactly?

The current public default theorem is:

```text
P_ne_NP_final
  (gap : ResearchGapWitness)
```

Interpretation:

1. The default route to `P ≠ NP` goes through `NP_not_subset_PpolyDAG_final`
   on the DAG side, with inclusion side already internalized as
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
2. The only remaining mathematical input is the `dagSeparation` field of
   `ResearchGapWitness`, which is exactly:
   ```text
   ResearchGapWitness.dagSeparation :
     ComplexityInterfaces.NP_not_subset_PpolyDAG
   ```
3. So the public default boundary is `NP_not_subset_PpolyDAG` itself, not
   `MagnificationAssumptions`, not `FormulaSupportBoundsFromMultiSwitchingContract`,
   and not any provider payload.

The historical `hMag : MagnificationAssumptions` argument is preserved only
on the explicit audit wrapper:

```text
P_ne_NP_final_of_magnification
  (hMag : MagnificationAssumptions)
```

This is not the current public default.  `MagnificationAssumptions` is also
formally refuted by the falsifiability audit
(`MagnificationAssumptions -> False`), so the audit wrapper is vacuous and
must not be presented as the canonical path.

## Are we currently using GapMCSP or Partial MCSP in active code?

Active code (`pnp3/`) uses **Partial MCSP** (`GapPartialMCSP*` objects).
Legacy GapMCSP material is preserved under `archive/` for provenance only.

## Is the active tree axiom-free in the strictest sense?

No in the absolute metatheoretic sense. Active `pnp3/` has no project-local
`axiom` and no `sorry/admit`, but the audited theorem surface still uses the
standard Lean assumptions:
`propext`, `Classical.choice`, `Quot.sound`.

## Is `hNPDag` still a blocker?

That step is already done on the default final surface.

`P_ne_NP_final` no longer takes external DAG separation as a separate input;
it takes a single `ResearchGapWitness`, whose `dagSeparation` field is the
DAG separation itself.

## What is the current fastest path to a zero-argument theorem?

The single-file frontier is `pnp3/Magnification/UnconditionalResearchGap.lean`.

Concretely:

1. Prove `ComplexityInterfaces.NP_not_subset_PpolyDAG` inside that file,
   without using the refuted support-bounds surfaces
   (`FormulaSupportRestrictionBoundsPartial`,
   `FormulaSupportBoundsFromMultiSwitchingContract`,
   `FormulaSupportBoundsPartial_fromPipeline`, or the overbroad
   `fixedParams + uniformProvenance` pair).
2. Build a `ResearchGapWitness` from that proof.
3. Expose the commented template:
   ```text
   theorem P_ne_NP_unconditional : ComplexityInterfaces.P_ne_NP :=
     P_ne_NP_final researchGapWitness
   ```

No other API change is required.  Wrappers below the `ResearchGapWitness`
boundary already exist; the missing piece is the lower-bound mathematics.

The `ResearchGapWitness` port is method-agnostic.  An algebraic, spectral,
finite-field, SOS, or Fourier-analytic proof of `NP_not_subset_PpolyDAG`
plugs in at the same point without producing support sets, AC0 provenance,
random restrictions, or `AcceptedFamilyCertificateAt`.

## Is axiom/sorry hygiene clean?

Yes for active `pnp3/`:

- active global `axiom`: 0
- active `sorry/admit`: 0

Use:

```bash
./scripts/check.sh
```

## How to quickly verify current audit surface?

```bash
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean \
         pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean; do
  lake env lean "$f"
done
```

## Is there any unconditional formalization result in this repo?

Yes, but at a restricted model, not at full `P ≠ NP`.

`pnp3/LowerBounds/AC0_GapMCSP.lean` exposes the paper-facing fixed-slice AC0
endpoint `gapPartialMCSP_not_in_AC0`.  This is a standalone restricted-model
formalization deliverable.  It does not close the `ResearchGapWitness` gap and
must not be presented as progress toward unconditional `P ≠ NP`.

## Where is the longer route map?

See `PROOF_OVERVIEW.md`.
