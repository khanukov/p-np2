# PNP3: Publication-facing status snapshot

Updated: 2026-05-28

Canonical checklist for unconditional claim readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release wording/checklist for the current milestone:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Russian-language frontier FAQ (authoritative narrative source for the
publishable framing):
`pnp3/Docs/Unconditionality_FAQ_ru.md`.

## Current claim level

1. Active `pnp3/` formalization has no project-local axioms and no
   `sorry/admit`.
2. The public final route compiles in
   `pnp3/Magnification/UnconditionalResearchGap.lean`
   (re-exported via the historical aggregator
   `pnp3/Magnification/FinalResultCore.lean`, accessible by the legacy import
   path `pnp3/Magnification/FinalResult.lean`).
3. `./scripts/check.sh` and current audit tests pass on the current tree.
4. The audited theorem surface still uses standard Lean assumptions
   `propext`, `Classical.choice`, `Quot.sound`.
5. Honest DAG wrappers exist for asymptotic fixed-slice collapse, concrete
   `_TM` source/blocker routes, and Route-B / source-closure / blocker /
   support-half fallback surfaces.  These are preserved as conditional
   compatibility wrappers, not as the public closure boundary.
6. Final `P ≠ NP` remains conditional on a single explicit input:
   `ResearchGapWitness`, whose `dagSeparation` field is exactly
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`.

## Current public closure boundary

The public default endpoints are:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

Legacy `hMag` / `hMS` / support-bounds / multi-switching / provider routes
remain only as explicit audit / compatibility wrappers under `_of_*` names
(`P_ne_NP_final_of_magnification`,
`P_ne_NP_final_of_asymptoticPullback`,
`P_ne_NP_final_of_multiswitchingData`, etc.) in
`pnp3/Magnification/FinalResultAuditRoutes.lean`.  They consume assumptions
that the falsifiability audit has formally refuted, so they are vacuous as
paths to unconditional closure and must not be presented as the canonical
route.

## Publishable standalone deliverables

Independent formalization milestones that are honest standalone deliverables
and do not depend on closing `ResearchGapWitness`:

1. `pnp3/LowerBounds/AC0_GapMCSP.lean` — paper-facing fixed-slice AC0
   endpoint `gapPartialMCSP_not_in_AC0`.  Restricted-model formalization
   result over the active `SmallAC0Solver_Partial` interface.
2. The falsifiability audit itself.  The audit module
   `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` proves
   `FormulaSupportRestrictionBoundsPartial -> False`,
   `FormulaSupportBoundsFromMultiSwitchingContract -> False`,
   `MagnificationAssumptions -> False`,
   `FormulaSupportBoundsPartial_fromPipeline -> False`,
   `MagnificationAssumptions_fromPipeline -> False`, and
   `FormulaCertificateProviderPartial -> False`.  This is itself a
   publishable result on the formalization side.
3. Iso-strong / promise-YES route closure at the canonical asymptotic
   instantiation (see `STATUS.md`, post-PR13 chain).  Four named theorems in
   `pnp3/Tests/GeneralIsoStrongRouteClosure.lean` formally retire the
   iso-strong route class as a path to unconditional `NP ⊄ P/poly`.

These deliverables are independently publishable.  They are recorded
separately from any final `P ≠ NP` claim and must not be packaged together
with one.

## Public statement rule

Until the checklist in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` is fully closed,
do not claim unconditional `P ≠ NP`.

In particular, do not present the legacy `hMag` / `hMS` / provider audit
wrappers as the canonical closure route; they are vacuous in the current
tree.

## Recommended publication wording for this release

1. The repository provides a Lean 4 framework and falsifiability audit for a
   magnification route around Partial MCSP.
2. Inclusion side for the public default is internalized as the coarse
   polynomial-size DAG inclusion theorem
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
3. The public closure boundary on the DAG side is sharpened to a single
   research-gap object `ResearchGapWitness` (whose `dagSeparation` field is
   exactly `NP_not_subset_PpolyDAG`); all legacy support-bounds /
   multi-switching / provider entry points have been formally refuted by the
   audit and survive only as compatibility / audit wrappers.
4. Additional standalone publishable artifacts include
   `gapPartialMCSP_not_in_AC0` (restricted-model lower bound), the
   falsifiability audit theorems, and the formal retirement of the
   iso-strong route class at the canonical asymptotic instantiation.
5. Final `P ≠ NP` remains conditional on `ResearchGapWitness`, so this is a
   milestone / RC release rather than an unconditional final claim.
