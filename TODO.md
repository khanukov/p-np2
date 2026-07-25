# TODO / Roadmap (current)

Updated: 2026-05-28

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
- A separate restricted-model AC0 surface exists at
  `pnp3/LowerBounds/AC0_GapMCSP.lean`.  It is a side artifact /
  formalization milestone, not the current P-vs-NP mainline (see
  Practical Work Item 7 below and the same posture in `STATUS.md`,
  `AGENTS.md`, `pnp4/README.md`).

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
5. the simulation route is coarse polynomial inclusion only, not a
   fine-grained compiler for slack-sensitive magnification;
6. green CI/check scripts are proof hygiene, not mathematical progress by
   themselves;
7. the remaining gap is mathematical, not just endpoint wiring.

### Target 4. Uniform sequential route (Mainline B, 2026-07-25)

Status: **accepted as a second mainline**; the mathematics is open.

`pnp4/Pnp4/Frontier/SequentialMagnification/` adds a second closure port whose
target is `P != NP` itself rather than the strictly stronger
`NP_not_subset_PpolyDAG`.  It is built on the McKay-Murray-Williams streaming
magnification theorem, which the current pnp4 mainline interface cannot express.

Decisions taken (2026-07-25):

1. `PvsNPClosureRoute` is recognised as the widened endpoint in `AGENTS.md`;
2. `spec/target.toml` gained an additive `[secondary_target]` block
   (spec_version 0.1.2 -> 0.1.3); the frozen `[target]` block is untouched.

Open work items, in priority order:

1. **DONE (2026-07-25): update-time budget added.**  `UniformStreaming.lean`
   supplies `CircuitBoundedStreaming space updateBudget`, the faithful MMW
   contract, and the repaired port.  The obligation in the restricted class is
   weaker (`UniformMCSPStreamingHard_of_MCSPStreamingHard`).
2. **Next blocking item: audit a concrete generator's window set.**
   `windowAttack_forces_easy_indicator` shows the window attack survives the
   restriction exactly when the generator's last-`w` window set has a circuit of
   size `<= updateBudget`.  Before spending effort on a construction, check this
   for a Nisan-/Forbes-Kelley-style candidate.  If the window set is easy for
   structured generators, the local-HSG route is closed in the restricted class
   too, and that should be recorded as a second no-go.
3. **Then: the mathematics.**  In the restricted class, construct or refute a
   local hitting-set generator with seed length `N ^ o(1)`.  Note the standing
   counting price `2 ^ seedLen <= circuitCountBound n s`, which pins the
   published construction at `N ^ (1/2)`.
4. **Discharge the Shannon slack.**  `hSlack` is currently a hypothesis of
   `MCSPStreamingHard_of_localHSG`.  `pnp3/Counting` has the machinery
   (`card_easyFunctions_le`, `circuitCountBound`) to prove it for size
   parameters below the counting threshold; wiring it in would remove a
   hypothesis.
5. **Formalize MMW19 Theorem 1.3**, turning `MMWStreamingMagnification` from a
   published contract into a theorem.  Large independent project.
6. **Note.**  The space-only model of `MCSPStreamingTarget.lean` is retained
   because the anti-hardwiring results are cleanest there; the repaired class of
   `UniformStreaming.lean` is the one the port should be read against.

Non-goals for this target: claiming that the sequential route is close to
`P != NP`.  It is not.  Its remaining obligation is a weak lower bound that
nobody knows how to prove; the contribution is that the obligation is now the
*right size* and is quantified.

Reference: `outputs/sequential-magnification-route-2026-07.md`.

### Target 5. Direct route (indirect diagonalization), 2026-07-25

Status: family-level no-go proved; the open sub-questions are named.

`pnp4/Pnp4/Frontier/DirectRoute/SimulationCalculus.lean` proves that the
published simulation toolkit cannot refute `P = NP`, because the assumed
exponent `c` enters multiplicatively while every known gain is either
sub-polynomial or lands in the `SPACE` sink.

Open sub-questions, both checkable:

1. Is there a polynomial-gain speedup into *bounded alternation*, i.e.
   `TIME[t] subseteq Sigma_k TIME[t^(1-delta)]` for constants `k, delta > 0`?
   By `fixed_gain_insufficient` this alone still does not suffice, but it is the
   missing arrow that every other tool in the area is built from.
2. Is there an additive-cost analogue of the Cook-Mertz / catalytic machinery?
   Catalytic computation is about *reusing* a resource instead of paying for it
   repeatedly, which is the only additive-flavoured idea in a multiplicative
   field.

Non-goal: extending the calculus with more arrows in the hope of a contradiction.
Theorem 3 of the module says fixed-gain arrows cannot help; adding them is
provably wasted effort.

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
4. If a new route depends on exact MCSP thresholds, Shannon slack, or small
   simulation overheads, first prove a separate fine-grained simulation
   adequacy theorem.
5. If a new algebraic/spectral/SOS/finite-field route cannot produce
   combinatorial support or accepted-family certificates, integrate it directly
   at `ResearchGapWitness` rather than forcing it through AC0/locality plumbing.
6. Optionally finish independent verifier/formalization milestones such as the
   polynomial-time MCSP verifier, but do not present them as closing `P != NP`.
7. The restricted-model AC0 surface around `LowerBounds.AC0_GapMCSP`
   is kept available with paper-facing `in_AC0` / `not_in_AC0`
   theorem names over the `SmallAC0Solver_Partial` interface, but it
   is treated as a side artifact / formalization milestone only —
   not as the current P-vs-NP mainline and not as a planned closure
   route unless paired with an explicit bridge to
   `NP_not_subset_PpolyDAG`.  Do not present it as a standalone
   publishable AC0 lower bound, do not mix it into the
   `ResearchGapWitness` closure story, and keep release docs
   consistent with `AGENTS.md` / `pnp4/README.md` on this point.
