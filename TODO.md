# TODO / Roadmap (current)

Updated: 2026-09-03

Canonical checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release wording guardrail:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Simulation fine-grained boundary:
`pnp3/Docs/Simulation_FineGrained_Status.md`.
Research method boundary:
`pnp3/Docs/Research_Method_Boundary.md`.

## Snapshot

- Active `axiom` in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes.
- Inclusion is internalized as coarse `P_subset_PpolyDAG`.
- The simulation layer is not a fine-grained Cook-Levin or
  hardness-magnification compiler adequacy theorem.
- The final `ResearchGapWitness` port is method-agnostic; AC0/locality and
  `AcceptedFamilyCertificateAt` routes are optional sufficient routes, not a
  mandatory interface for every future proof.
- DAG endpoint plumbing is substantial.  The legacy formula-side
  support-bounds / multi-switching separation route is formally
  refuted; the current public closure boundary is `ResearchGapWitness`,
  whose `dagSeparation` field (= `NP_not_subset_PpolyDAG`) is the only
  remaining mathematical input.
- The former pnp3 fixed-slice AC0 surface is now an audit quarantine.
  Its enriched `SmallAC0Solver_Partial` package is inconsistent before solver
  correctness is used, so it is not an AC0 lower bound or P-vs-NP progress.
- Mainline scope: per `AGENTS.md`, P-vs-NP mainline progress means reducing
  `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource` in `pnp4/`.  The
  pnp3 targets below are honest infrastructure and no-go hardening for the
  magnification route; they are not the mainline.  See Target 4.

## Hard Policy Update

The project must not treat the legacy support-bounds route as an unfinished
technical lemma.

The following assumptions are formally ex-falso in the current tree:

- `FormulaSupportRestrictionBoundsPartial`
- `FormulaSupportBoundsFromMultiSwitchingContract`
- `MagnificationAssumptions`
- `FormulaSupportBoundsPartial_fromPipeline`
- `MagnificationAssumptions_fromPipeline`

The fixed-slice support-half blocker branch is also a closed historical no-go
route, as recorded by:

- `LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

## Remaining Closure Targets

### Target 1. Preserve honest endpoint infrastructure

Status: keep green.

The DAG side has useful plumbing:

1. fixed-slice `PpolyDAG -> PpolyFormula` conversion,
2. asymptotic and `_TM` wrappers,
3. Route-B/source-closure/blocker surfaces,
4. final wrappers exposing the exact assumptions consumed.

This infrastructure is valuable when paired with either a non-vacuous
formula / locality source theorem, or a direct method-agnostic source
theorem that proves `ResearchGapWitness` /
`NP_not_subset_PpolyDAG`.

### Target 2. Replace the false support-bounds source

Status: open pnp3 research question.  This is **not** the P-vs-NP mainline — see the
Snapshot above and Target 4.

Do not try to "finish" the old `hMS` route.  It is inconsistent.

The current candidate shape is:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

This fixed-params predicate blocks the known singleton-provider attack, but it
is not yet a proved source theorem.  Also, when paired with overbroad uniform
provenance for every formula witness under the same `ac0`, it reconstructs the
old false predicate and gives `False`.

Acceptance condition for real progress:

1. formulate a provenance-restricted support/locality theorem that cannot be
   instantiated by truth-table hardwiring;
2. prove it or clearly mark it as an external research assumption;
3. add falsifiability probes showing it does not imply the old false
   `FormulaSupportRestrictionBoundsPartial`.

### Target 3. Keep status docs honest

Status: active discipline.

Canonical docs must say:

1. no unconditional `P != NP` theorem exists in the repo;
2. the old support-bounds route is vacuous;
3. fixedParams is only a candidate contract shape;
4. `fixedParams + uniformProvenance` is itself inconsistent as currently
   stated;
5. the simulation route is coarse polynomial inclusion only, not a
   fine-grained compiler for slack-sensitive magnification;
6. green CI/check scripts are proof hygiene, not mathematical progress by
   themselves;
7. the remaining gap is mathematical, not just endpoint wiring;
8. the pnp4 decision→search extraction is formalized in one direction only
   (`PpolyDAG → solver` plus its contrapositive), never as an equivalence, and its
   no-solver input is not a weak bound amplified by magnification;
9. the preferred pnp4 `ContentPrefixExtensionNPWitness` obligation (and the retained
   `PrefixExtensionNPWitness` compatibility target) is stated in the repository's single-tape,
   exact-step `TM` model, with no cross-model runtime-robustness theorem and no formal prevention of
   input-length advice. P1c now proves countability and a direct no-length-advice diagonal for the
   separate versioned `Pnp3.Complexity.Uniform.V1.UniformP`; canonical `P` remains legacy and
   unchanged, with no rebind or equivalence inferred.

### Target 4. pnp4 mainline: the two consolidated source obligations

Status: the P-vs-NP mainline (per `AGENTS.md`).

The preferred content-truthful capstone in
`pnp4/Pnp4/Frontier/ContractExpansion/ContentConsolidatedSource.lean` reduces the verified-source
chain, at a concrete polynomial threshold, to exactly two explicit hypotheses:

```text
NP_not_subset_PpolyDAG_treePolyCT
  (k : Nat)
  (hNoPoly : NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k)))
  (hNPWit  : ContentPrefixExtensionNPWitness
               (treeCircuitWitnessCodec (thresholdPoly k)))
  : ComplexityInterfaces.NP_not_subset_PpolyDAG
```

1. `hNoPoly` is a genuine `P/poly` circuit lower bound for the concrete tree-MCSP search
   problem.  Research-level mathematics, not a Lean engineering task.  Because the
   extraction is one-way and the instance length is `tableLen n = 2^n`, it is at least as
   strong as "this concrete NP language is not in `P/poly`".
2. `hNPWit` is a concrete verifier TM plus polynomial runtime bound plus certificate correctness,
   in the model described in Target 3 item 9. D1b proves that a supplied
   `ContentVerifierBridge` repackages into this witness, but no bridge instance is constructed.
3. `PolyBoundedInTable threshold` is proved for the canonical polynomial thresholds
   (`ThresholdGrowth.lean`), so it is not an open input at `thresholdPoly k`.

Neither of the two open hypotheses is proved, so the endpoint stays strictly
conditional.  What *is* proved: the one-way decision→search extraction and its
contrapositive, the growth reduction, the concrete `treeCircuitWitnessCodec`
(`ConcreteTreeCodec.lean`), the threshold-growth discharge
(`polyBoundedInTable_thresholdPoly`), concrete `ContentAccepts` non-vacuity, gamma narrowing, and
vacuity of the convention-length equality gate. Exactly three tag/index/padding read-value tests
remain in the parser characterization.

For input (2), the remaining work is an actual concrete verifier bridge: machine construction,
runtime proof, and exact-step acceptance correctness. Wrapper-level `L'` padding invariance and
formal runtime/advice enforcement also remain open; complete-word `ContentAccepts` padding
invariance does not close either item. The original length-gated
`NP_not_subset_PpolyDAG_treePoly` / `PrefixExtensionNPWitness` capstone remains compiled and audited
as a compatibility route. See `pnp4/Pnp4/Frontier/ContractExpansion/README.md` for the full
proved-vs-open breakdown.

## Non-Goals Right Now

- Do not claim full unconditionality.
- Do not add wrappers that hide the false support-bounds source.
- Do not present the public zero-argument/provider API as assumption-free.
- Do not reopen the literal fixed-slice support-half branch as the main route.
- Do not treat Lean formalization alone as capable of closing the missing
  MCSP/Ppoly lower-bound mathematics.

## Practical Work Items

1. Keep `FormulaSupportBoundsFalsifiabilityProbe.lean` as the authoritative
   audit module for support-bounds falsifiability.
2. Keep `pnp3/Magnification/UnconditionalResearchGap.lean` as the single-file
   frontier **for the pnp3 route**: a pnp3-side unconditional closure should prove
   `ResearchGapWitness` there and then expose `P_ne_NP_unconditional` from that same
   file.  A pnp4-side closure (Target 4) need not be re-expressed as
   `ResearchGapWitness` — its endpoint already produces
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`, which is exactly
   `ResearchGapWitness.dagSeparation` — though routing it through that witness remains
   an option.  See `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
3. If a new support/provenance contract is proposed, first add a falsifiability
   audit before wiring it into final theorems.
4. If a new route depends on exact MCSP thresholds, Shannon slack, or small
   simulation overheads, first prove a separate fine-grained simulation
   adequacy theorem.
5. If a new algebraic/spectral/SOS/finite-field route cannot produce
   combinatorial support or accepted-family certificates, integrate it directly
   at `ResearchGapWitness` rather than forcing it through AC0/locality plumbing.
6. Optionally finish independent verifier/formalization milestones such as the
   polynomial-time MCSP verifier, but do not present them as closing `P != NP`.
7. Keep `LowerBounds.AC0_GapMCSP` as a deprecated compatibility quarantine.
   The canonical audit theorem is
   `false_of_smallAC0Params_and_easyFamilyData`; it records that the enriched
   parameter/easy-family assumptions imply `False` without solver correctness.
   Do not present the historical `in_AC0` / `not_in_AC0` names as a standard
   circuit-class result, a publishable AC0 lower bound, or a closure route.
