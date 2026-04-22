# TODO / Roadmap (current)

Updated: 2026-04-22

Canonical checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release wording guardrail:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Snapshot

- Active `axiom` in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes.
- Inclusion is internalized.
- DAG endpoint plumbing is substantial, but the current separation route still
  depends on formula-side support-bounds assumptions that the audit refutes.

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

This infrastructure is valuable only when paired with a non-vacuous
formula-side source theorem.

### Target 2. Replace the false support-bounds source

Status: main research blocker.

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
5. the remaining gap is mathematical, not just endpoint wiring.

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
   frontier: future unconditional closure should prove `ResearchGapWitness`
   there and then expose `P_ne_NP_unconditional` from that same file.
3. If a new support/provenance contract is proposed, first add a falsifiability
   audit before wiring it into final theorems.
4. Optionally finish independent verifier/formalization milestones such as the
   polynomial-time MCSP verifier, but do not present them as closing `P != NP`.
