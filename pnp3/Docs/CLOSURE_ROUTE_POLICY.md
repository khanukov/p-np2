# Closure Route Policy (canonical)

Updated: 2026-08-21.

This file is a hard policy reference for unconditional-closure planning.
It exists to prevent stale route language from re-entering status docs.

## Scope

This policy governs the **pnp3 magnification route** (SAL / locality / Route-A/B over
`GapPartialMCSP*`).  It is not the whole active surface.

Per `AGENTS.md`, the **pnp4** algorithms-to-lower-bounds frontier is a second permitted
active framing for P-vs-NP mainline work, whose source obligations are
`SearchMCSPWeakLowerBound` and `VerifiedNPDAGLowerBoundSource`.  Both framings terminate
at the same target, `ComplexityInterfaces.NP_not_subset_PpolyDAG`.  See the "pnp4
Frontier" section below, the pnp4 section of `STATUS.md`, and `pnp4/README.md`.

Nothing in this file authorizes describing a restricted `AC0[p]` / formula / local-PRG /
coin-problem result as mainline progress; that boundary is set by `AGENTS.md`.

## One Active pnp3 Framing

Only one active framing is allowed for the pnp3 route in canonical planning docs:

1. preserve the useful DAG endpoint infrastructure;
2. treat the legacy support-bounds and multi-switching route as formally
   refuted, not merely unfinished;
3. use `FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb` only as a
   candidate contract shape;
4. treat `Complexity/Simulation` as a coarse `P_subset_PpolyDAG` inclusion
   proof, not as a fine-grained magnification compiler;
5. treat `ResearchGapWitness` as the method-agnostic final port, so
   AC0/locality/restriction and `AcceptedFamilyCertificateAt` routes remain
   optional sufficient routes rather than mandatory proof formats;
6. treat green CI and `./scripts/check.sh` as proof hygiene, not as
   mathematical progress on general DAG lower bounds;
7. treat the missing non-vacuous fixed-params support/locality theorem as the
   research-level gap.

The theorem
`NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance`
is a gap-exposing theorem.  It must not be described as closing the gap.

The single-file frontier for closing the gap is
`pnp3/Magnification/UnconditionalResearchGap.lean`.  Future unconditional
closure should prove `ResearchGapWitness` there, without changing route
plumbing elsewhere.

Future algebraic, spectral, finite-field, SOS, Fourier-analytic, or otherwise
non-combinatorial proofs should plug in by proving `ResearchGapWitness`
directly.  They must not be rejected merely because they do not produce
support/locality data or an `AcceptedFamilyCertificateAt` producer.

## pnp4 Frontier

The pnp4 frontier reaches the same target without going through this file's pnp3
plumbing.  Its most concrete current form is

```text
NP_not_subset_PpolyDAG_treePoly
  (k : Nat)
  (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
  (hNPWit  : PrefixExtensionNPWitness
               (treeMCSPConcretePrefixParser (thresholdPoly k) …))
  : ComplexityInterfaces.NP_not_subset_PpolyDAG
```

in `pnp4/Pnp4/Frontier/ContractExpansion/ConsolidatedTreeSeparation.lean`.  Policy for
canonical docs describing it:

1. it is strictly **conditional** on those two hypotheses; neither is proved;
2. the decision→search extraction is formalized in **one direction only**
   (`PpolyDAG → solver` plus its contrapositive), so it must not be described as an
   equivalence, and `hNoPoly` must not be described as a *weak* bound amplified by
   magnification — no magnification theorem is formalized;
3. `hNPWit` is an NP-membership obligation in the repository's single-tape, exact-step
   `TM` model; see the runtime-model caveat in `STATUS.md` and
   `pnp4/Pnp4/Frontier/ContractExpansion/README.md`;
4. `PolyBoundedInTable threshold` is a third input at an arbitrary threshold and is
   proved at the canonical polynomial thresholds, so it disappears at `thresholdPoly k`.

A future closure via this route need not be re-expressed as `ResearchGapWitness`, though
it may be: the pnp4 endpoint already produces
`ComplexityInterfaces.NP_not_subset_PpolyDAG`, which is exactly
`ResearchGapWitness.dagSeparation`.

## Simulation Boundary

The active simulation theorem
`proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG` is a coarse
polynomial-size inclusion theorem.  Its size contract exposes an existential
polynomial bound of the form `n^k + k`.

Canonical docs must not describe this as a fine-grained Cook-Levin theorem or
as a hardness-magnification adequacy proof.  Any future route that depends on
exact MCSP thresholds, Shannon slack, or small compiler overheads must first
add a separate fine-grained simulation adequacy theorem.

## Closed/No-Go Routes

Literal fixed-slice blocker hunt is a closed historical no-go route for
unconditional closure planning.

Relevant no-go modules:

- `pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

The old support-bounds route is also closed as a false route:

- `FormulaSupportRestrictionBoundsPartial -> False`
- `FormulaSupportBoundsFromMultiSwitchingContract -> False`
- `FormulaSupportBoundsPartial_fromPipeline -> False`

## Documentation Guardrails

Canonical docs (`STATUS.md`, `TODO.md`,
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`,
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`,
`pnp3/Docs/Simulation_FineGrained_Status.md`,
`pnp3/Docs/Research_Method_Boundary.md`, and this file — the `route_docs` set in
`scripts/check.sh`) must satisfy all of the following:

1. explicitly mention fixed-slice no-go status;
2. explicitly mention the refuted support-bounds/multi-switching route;
3. explicitly mention fixedParams as a candidate, not a proved source theorem;
4. explicitly mention that `fixedParams + uniformProvenance` is inconsistent
   as currently stated;
5. explicitly mention the coarse simulation boundary and the absence of a
   fine-grained compiler adequacy theorem;
6. explicitly mention that `ResearchGapWitness` is method-agnostic and that
   `AcceptedFamilyCertificateAt`/AC0/locality routes are optional;
7. explicitly mention that green CI/check-script success is proof hygiene, not
   mathematical progress by itself;
8. avoid deprecated phrasing that presents residual work as API cleanup or
   ordinary endpoint plumbing.

This policy is enforced in `scripts/check.sh`.
