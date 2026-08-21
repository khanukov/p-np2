# Checklist: Unconditional Constructive `P != NP`

Updated: 2026-08-21

This is the canonical checklist for what still blocks an unconditional
in-repo theorem `P != NP`.

Scope note: the repository has two active tracks.  `pnp3/` carries the magnification
route; `pnp4/` carries the P-vs-NP mainline per `AGENTS.md`.  Both terminate at
`ComplexityInterfaces.NP_not_subset_PpolyDAG`; neither closes it.  See "pnp4 Route"
below.

For current release posture, see `RELEASE_RC.md`.
For hard route policy lock, see `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
For the simulation complexity-leakage boundary, see
`pnp3/Docs/Simulation_FineGrained_Status.md`.
For the research-method boundary, see
`pnp3/Docs/Research_Method_Boundary.md`.

## Current Final API (actual code)

Files:

- compatibility import path: `pnp3/Magnification/FinalResult.lean`
- active research-gap surface:
  `pnp3/Magnification/UnconditionalResearchGap.lean`
- legacy/audit route surface:
  `pnp3/Magnification/FinalResultAuditRoutes.lean`
- pnp4 conditional source surface:
  `pnp4/Pnp4/Frontier/ContractExpansion/ConsolidatedTreeSeparation.lean`
  (see "pnp4 Route" below)

Current public endpoints:

```text
NP_not_subset_PpolyDAG_final
  (gap : ResearchGapWitness)

P_ne_NP_final
  (gap : ResearchGapWitness)
```

Provider/support-bounds endpoints are retained only as explicit audit routes,
for example:

```text
P_ne_NP
  [FinalPayloadProvider]

P_ne_NP_final_of_asymptoticPullback
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
```

Those audit routes are not unconditional theorems.  The `hMS` component is
part of the formally refuted support-bounds route.

## Already Closed

1. Active `pnp3/` tree is axiom-clean (`axiom = 0`, `sorry/admit = 0`).
2. `./scripts/check.sh` passes on current tree.
3. Inclusion is internalized via
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
4. That inclusion is coarse polynomial-size DAG inclusion only, not a
   fine-grained simulation adequacy theorem for hardness magnification.
5. DAG endpoint wiring and fixed-slice `PpolyDAG -> PpolyFormula` conversion
   are implemented.
6. Historical fixed-slice support-half branch is archived as a no-go route:
   - `FailedRoute_FixedSliceSupportHalfCore.lean`
   - `FailedRoute_FixedSliceSupportHalfImpossible.lean`.

## Refuted Assumption Surfaces

The support-bounds audit (`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`)
proves that these six surfaces are vacuous:

1. `FormulaSupportRestrictionBoundsPartial -> False`
2. `FormulaSupportBoundsFromMultiSwitchingContract -> False`
3. `MagnificationAssumptions -> False`
4. `FormulaSupportBoundsPartial_fromPipeline -> False`
5. `MagnificationAssumptions_fromPipeline -> False`
6. `FormulaCertificateProviderPartial -> False` (Probe 13, PR 13 audit)

Therefore, proving final statements from these assumptions is not mathematical
progress toward unconditional `P != NP`.

## Closed Route Families

Two route families are closed beyond the six refuted surfaces above.  Neither closure
proves `P != NP` or `NP ⊄ PpolyDAG`; both remove a route.

### Iso-strong / promise-YES route class

Closed at the **conclusion** level over arbitrary `GapSliceFamilyEventually`:

```text
isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
  ¬ IsoStrongFamilyEventually F hInDag
```

in `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, with the strategic consequence packaged
as four named theorems in `pnp3/Tests/GeneralIsoStrongRouteClosure.lean` and the two
canonical promise companions in `pnp3/Tests/PromiseRouteConclusionProbe.lean`.  The
canonical asymptotic track via `canonicalAsymptoticHAsym` is therefore not a closure
route.  Full 16-stage audit chain: `STATUS.md`.

### Deprecated pnp3 fixed-slice AC0 endpoint

`pnp3/LowerBounds/AC0_GapMCSP.lean` is a deprecated compatibility quarantine.  The
canonical certificate is

```text
false_of_smallAC0Params_and_easyFamilyData
  (params : SmallAC0ParamsPartial p)
  (easy   : AC0EasyFamilyDataPartial params.ac0) : False
```

which projects only `params` and `easyData` and never uses solver correctness.  The
historical `in_AC0` / `not_in_AC0` names must not be cited as a standard AC0 lower
bound, a publishable result, or a closure route.  See
`pnp3/Docs/AC0_Publishable_Result.md`.

## Fixed-Params Candidate

The active nontrivial candidate shape is:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

Current audit status:

1. fixed external `ac0` blocks the known Probe 7 singleton-provider attack;
2. fixedParams alone is not currently refuted in-project;
3. fixedParams plus uniform provenance for every formula witness under the
   same `ac0` implies the old false predicate;
4. the pair `fixedParams + uniformProvenance` is formally inconsistent.

## Remaining Unconditional Blocker

Full unconditionality requires a non-vacuous proof of `ResearchGapWitness`,
equivalently `ComplexityInterfaces.NP_not_subset_PpolyDAG`.  Any lower-level
support/locality theorem used to obtain it must:

1. avoid universal quantification over arbitrary `PpolyFormula` witnesses;
2. reject truth-table hardwiring and singleton provenance;
3. use fixed, externally meaningful AC0 parameters;
4. not imply `FormulaSupportRestrictionBoundsPartial`;
5. connect to the existing DAG endpoint plumbing without routing through the
   old `FormulaSupportBoundsFromMultiSwitchingContract`.

This is a research-level lower-bound gap, not a missing wrapper.

The final `ResearchGapWitness` boundary is method-agnostic.  A future proof may
be algebraic, spectral, finite-field, SOS, Fourier-analytic, or otherwise
non-combinatorial.  Such a proof does not need to produce
`AcceptedFamilyCertificateAt`, support sets, random restrictions, or AC0
provenance if it proves `NP_not_subset_PpolyDAG` directly.

The gap is isolated in
`pnp3/Magnification/UnconditionalResearchGap.lean`.  The file defines
`ResearchGapWitness` and already proves
`P_ne_NP_of_researchGap : ResearchGapWitness -> P_ne_NP`.

## pnp4 Route

`pnp4/` reaches the same target through a separate, machine-checked conditional chain.
At a concrete polynomial threshold it collapses to exactly two explicit hypotheses
(`pnp4/Pnp4/Frontier/ContractExpansion/ConsolidatedTreeSeparation.lean`):

```text
NP_not_subset_PpolyDAG_treePoly
  (k : Nat)
  (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
  (hNPWit  : PrefixExtensionNPWitness
               (treeMCSPConcretePrefixParser (thresholdPoly k) …))
  : ComplexityInterfaces.NP_not_subset_PpolyDAG
```

Status of each input:

1. `hNoPoly` — open, research-level.  The decision→search extraction is formalized in
   **one direction only** (`boundedSearchSolver_of_PpolyDAG_prefixExtension` plus its
   contrapositive); the converse is not formalized, so this is a one-way reduction and
   not an equivalence.  Since the instance length is `tableLen n = 2^n`, `hNoPoly` is at
   least as strong as the full `P/poly` lower bound and is **not** a weak bound amplified
   by magnification — no magnification theorem is formalized.
2. `hNPWit` — open, engineering-heavy.  It is an NP-membership obligation in the
   repository's deterministic single-tape, exact-step `TM` model (`runTime` is a structure
   field; `TM.accepts` is evaluated at exactly step `runTime n`).  No cross-model
   runtime-robustness theorem is formalized.
3. `PolyBoundedInTable threshold` — **discharged** at the canonical polynomial thresholds
   (`polyBoundedInTable_thresholdPoly`, `ThresholdGrowth.lean`); an open input only at an
   arbitrary threshold.

Neither open input is proved, so this route currently adds no unconditional progress.
Proved-vs-open breakdown: `pnp4/Pnp4/Frontier/ContractExpansion/README.md`.

## Proof-Quality Safety Checks

Before declaring any blocker closed, confirm:

1. `./scripts/check.sh` passes.
2. Current audit/regression tests pass:
   `pnp3/Tests/AxiomsAudit.lean`,
   `pnp3/Tests/BarrierAudit.lean`,
   `pnp3/Tests/BarrierBypassAudit.lean`,
   `pnp3/Tests/BridgeLocalityRegression.lean`,
   `pnp3/Tests/WeakRouteSurfaceTests.lean`,
   `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
3. New source assumptions have a falsifiability audit before they are used by
   final theorem surfaces.
4. Any source route that uses exact MCSP thresholds, Shannon slack, or
   hardness-magnification constants has a separate fine-grained simulation
   adequacy theorem before it is wired to `ResearchGapWitness`.
5. New non-combinatorial source routes are not forced through AC0/locality or
   `AcceptedFamilyCertificateAt` if they prove `ResearchGapWitness` directly.
6. Green CI, route guards, and axiom audits are treated as hygiene checks, not
   as mathematical evidence that the remaining lower-bound gap is closing.
7. No document claims unconditional `P != NP` prematurely.

## Definition Of Done

All of the following must hold at once:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` is derived without false or
   externally supplied research assumptions, by **either**:
   - a non-vacuous source theorem on the pnp3 side (replacing the refuted
     support-bounds / multi-switching route, or proving the `ResearchGapWitness`
     boundary directly by any method); **or**
   - discharging both open inputs of the pnp4 route above
     (`NoPolynomialBoundedSearchSolver` and `PrefixExtensionNPWitness`), whose
     endpoint is already exactly that target.
2. That derivation is wired to a `ResearchGapWitness` in
   `pnp3/Magnification/UnconditionalResearchGap.lean`, or to an equivalent
   zero-hypothesis endpoint, so the public final theorem has a single named source.
3. Public final theorem no longer depends on external provider payload.
4. Zero-argument theorem `P_ne_NP` is derivable in the active tree.
5. Canonical docs are updated consistently to unconditional wording.
6. No route claim rests on a strength overstatement — in particular the pnp4
   extraction is still described as one-way, not as an equivalence, unless a converse
   is actually formalized.
