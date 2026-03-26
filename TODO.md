# TODO / Roadmap (current)

Updated: 2026-03-26

Canonical blocker checklist lives in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release wording guardrail: `RELEASE_RC.md`.
Current DAG plan notes:
- `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`
- `pnp3/Docs/GapTarget_StableRestriction_Route.md`
- `pnp3/Docs/AsymptoticDAGBarrier_Status.md`

## Snapshot

- Active `axiom` in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- `./scripts/check.sh` passes
- Final API remains conditional in `pnp3/Magnification/FinalResult.lean`
- Inclusion side is already internalized:
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`
- Main remaining blocker is still DAG-side separation:
  internalize `NP_not_subset_PpolyDAG`

---

## Current honest target

The right near-term goal is **not** “claim unconditional `P ≠ NP` soon”.
The right goal is:

> reduce the repository to one minimal honest open theorem-level blocker,
> with all other glue, counting, API shape, and asymptotic routing already
> internalized.

In particular, the repository should aim to be:

1. axiom/sorry clean in CI;
2. free of temporary bridge assumptions in the build-critical lower-bound path;
3. asymptotic at the final separation surface;
4. centered on one **weakest sufficient** DAG-side endpoint, not on a stronger
  -than-necessary global invariant;
5. equipped with one secondary/backup endpoint for an alternative
   magnification route.

---

## What is already closed

1. AC0/formula separation wiring compiles and has active asymptotic wrappers.
2. Internal inclusion theorem is closed:
   `proved_P_subset_PpolyDAG_internal`.
3. DAG stable-restriction consumer stack exists:
   `stableRestrictionGoal_of_abstractGapTargetedPayload` and downstream
   contradiction lemmas are already formalized.
4. Build/audit hygiene is clean for project-local assumptions:
   no active `axiom`, `sorry`, or `admit` in `pnp3/`.
5. Counting slack core is now direct:
   `Counting.exists_hard_function_with_constraints_of_countingSlack` is proved,
   and build-critical lower-bound wrappers no longer require `hSlackToHalf`.

---

## What still blocks unconditional `P ≠ NP`

1. Internalize `NP_not_subset_PpolyDAG`.
2. Remove the final external DAG-separation hypothesis
   `hNPDag : NP_not_subset_PpolyDAG` from `P_ne_NP_final*`.
3. Replace the current too-strong DAG-side “final blocker” with a weaker,
   theorem-minimal endpoint that matches what the counting contradiction really
   consumes.
4. Keep the final theorem surface asymptotic; fixed-slice theorems remain only
   as internal building blocks.

---

## Main design correction for the DAG route

The repository should **not** treat the current strongest route
`dagStableRestrictionInvariantProvider` as the canonical final blocker.
That route remains a valid **strong sufficient condition**, but it is too
strong to be the default “one theorem away” target.

The preferred primary blocker is now:

> a one-sided, promise-aware, value-coordinate certificate stating that a small
> solver accepts an exponentially large completion set around one YES instance,
> with enough counting slack to force a NO completion.

Working name for the new primary endpoint:

- `YesSubcubeCertificate`, or
- `PromiseValueLocalityCertificate`.

The current stable-restriction route should remain in the codebase as an
optional stronger route, not the main open target.

### Literature-driven caution

Recent hardness-magnification literature should affect how this endpoint is
judged:

1. **Locality barrier / localizability is an active constraint, not background
   commentary.** New endpoint candidates must be screened for whether they are
   likely to localize to circuits with small-fanin oracle gates.
2. **Distinguisher-based magnification is now a serious parallel route**, not
   just a speculative backup. The 2025 distinguisher-based general
   magnification work suggests a path that may sidestep the localization
   barrier.
3. **Restricted-model progress matters**: lower bounds obtained from shrinkage
   for models such as comparator circuits are relevant not only as side
   results, but as probes for the right invariant/endpoints.
4. **Variant hygiene matters**: recent results distinguish sharply between
   MCSP, Partial-MCSP, Gap-MCSP, oracle-MCSP, uniform vs nonuniform
   consequences, and formula vs general-circuit thresholds. No theorem or
   roadmap step should silently transfer a result across these variant
   boundaries without an explicit bridge theorem.
5. **Learning/witnessing interpretations are relevant side signals**:
   distinguisher/witness-finding frameworks connected to learning-from-lower-
   bounds may provide endpoint ideas or proof diagnostics even when they do not
   immediately yield the main DAG theorem.

---

## Concrete execution plan

The tasks below are the active implementation order.

### Task 0. Freeze the public statement of the remaining blocker

**Goal:** all docs and code comments use the same story.

**Status:** closed on 2026-03-26.

Do:
1. Treat the active remaining blocker as a theorem-level endpoint, not as vague
   “DAG-side work”.
2. Distinguish explicitly between:
   - primary nonuniform endpoint: one-sided promise/value locality;
   - stronger optional endpoint: global stable restriction;
   - parallel endpoint: distinguisher/uniform route.
3. Add an explicit variant ledger for each endpoint:
   - MCSP vs Partial-/Gap-MCSP,
   - valid-encoding vs arbitrary encoded input,
   - fixed-slice vs asymptotic,
   - formula vs DAG/general-circuit consequence,
   - uniform vs nonuniform conclusion.
4. Keep all top-level wording conditional until Task 8 is done.

Done when:
- `TODO.md`, `STATUS.md`, and `FinalResult.lean` are mutually consistent about
  what is open and what is only a stronger optional route;
- each planned endpoint has an explicit variant/signature boundary.

### Task 1. Remove the temporary counting bridge `hSlackToHalf`

**Priority:** critical.

**Status:** closed on 2026-03-26.

Result:
1. `pnp3/Counting/ShannonCounting.lean` now contains the direct-slack theorem

   ```text
   exists_hard_function_with_constraints_of_countingSlack
   ```

   consuming

   ```text
   circuitCountBound ... < 2^(tableLen - constrained.card)
   ```

   without converting first to `constrained.card ≤ tableLen / 2`.
2. `pnp3/LowerBounds/MCSPGapLocality.lean` wrappers
   - `exists_hard_function_with_constraints_of_countingSlack`
   - `exists_yes_no_agreeing_on_alive_of_countingSlack`

   no longer require `hSlackToHalf`.
3. Build-critical lower-bound theorems now consume counting slack directly.

Done when:
- `hSlackToHalf` disappears from build-critical lower-bound theorems.
- Layer A consumes only counting slack.

### Task 2. Introduce value-only / promise-only locality interfaces

**Priority:** critical.

Current issue:
- much of the current barrier API speaks about agreement on encoded-input
  coordinates (`mask ++ values`), while the counting contradiction really lives
  on truth-table value coordinates.

Progress update (2026-03-26):
- `pnp3/LowerBounds/MCSPGapLocality.lean` now defines
  `ValueCoordinateSet`, `AgreeOnValues`, `ValidEncoding`, and the new
  promise/value consumer
  `no_value_local_function_solves_mcsp_of_countingSlack`.
- `pnp3/LowerBounds/AsymptoticDAGBarrier.lean` now exposes the corresponding
  small-solver interface
  `SmallDAGImpliesPromiseValueLocalityAt`
  together with `no_dag_solver_of_promise_value_locality_at`.
- `pnp3/LowerBounds/DAGStableRestrictionProducer.lean` now also contains a
  native source-side package for this route:
  `PromiseValueLocalityPackageAt` and
  `smallDAGPromiseValueLocalityStatement_of_packageProvider`.
- The codebase now also contains the first one-sided weak-route surface:
  `exists_no_completion_agreeing_on_values_of_countingSlack`,
  `no_one_sided_value_local_function_solves_mcsp_of_countingSlack`,
  `YesSubcubeCertificateAt`,
  `no_small_dag_solver_of_yesSubcubeCertificateAt`.
- The remaining gap is now narrower: not a missing consumer or missing source
  API, but the missing theorem that actual DAG semantics produce a one-sided
  YES-centered certificate on slices.

Do:
1. Add value-level agreement notions, e.g.:
   - `AgreeOnValues`
   - `ValueCoordinateSet`
   - `valueSlack`
2. Separate semantic value bits from encoding artifacts (mask bits and general
   encoded-input garbage).
3. Add validity/promise-aware interfaces so locality is only required on:
   - valid table encodings;
   - and ideally only on the promise domain.
4. Rephrase the anti-locality consumer so it can consume value-only locality.

Done when:
- the final contradiction does not require locality on arbitrary encoded
  bitstrings;
- the final open endpoint is stated over semantic truth-table/value data.

### Task 3. Prove a new weaker sufficient endpoint

**Priority:** critical.

Current issue:
- global stable restriction is stronger than what the contradiction actually
  needs.

Progress update (2026-03-26):
- the one-sided weak-route endpoint is now formalized in code as
  `YesSubcubeCertificateAt`;
- the direct contradiction theorem already exists:
  `no_small_dag_solver_of_yesSubcubeCertificateAt`;
- the slice-family provider surface also exists:
  `yesSubcubeCertificateAtProviderOnSlices`;
- the stronger encoded-coordinate fallback is now reduced all the way to an
  explicit semantic/numeric stack via
  `generalSolverOfSmallDAGWitnessOnSlice`,
  `SmallDAGWitnessSemanticConeCertificateAt`,
  `SmallDAGWitnessRestrictionExtractionAt`,
  `SmallDAGWitnessRestrictionNumericDataAt`,
  `SmallDAGWitnessRestrictionCertificateDataAt`,
  `smallDAGWitnessShrinkageCertificateAt_of_restrictionData`,
  `dagStableRestrictionSlackPackageAt_of_shrinkageCertificate`,
  `smallDAGLocalityStatement_of_semanticConeAndNumericProvider`, and
  `smallDAGLocalityStatement_of_restrictionDataProvider`;
- therefore the remaining work in Task 3 is no longer "invent the endpoint
  shape" or "finish the downstream contradiction": it is to prove that small
  DAG semantics on slices actually produce a one-sided YES-centered certificate
  such as `YesSubcubeCertificateAt`.

Do:
1. Keep `YesSubcubeCertificateAt` as the canonical theorem-minimal weak-route
   target.
2. Prove a source theorem of the form:

   ```text
   SmallDAGWitnessOnSlice -> YesSubcubeCertificateAt
   ```

   or an equivalent one-sided YES-centered promise/value package that still
   feeds `no_small_dag_solver_of_yesSubcubeCertificateAt`.
3. Make explicit which semantic invariant is expected to yield this theorem:
   YES-centered stability around one valid promise instance, not pairwise
   locality as the primary target.
4. Add a **minimality benchmark subtask**: compare this endpoint against what is
   already enough in known magnification results (especially sparse-problem /
   formula thresholds) so we do not accidentally choose an endpoint stronger
   than the literature suggests is necessary.
5. Add a **barrier-screen subtask** before promoting this endpoint:
   test whether the endpoint/proof idea appears localizable in the sense
   highlighted by the hardness-magnification locality literature.
6. Only after the source theorem, minimality benchmark, and barrier-screen pass
   are in place, promote the new endpoint to the main blocker.

Done when:
- there is a proved theorem in Lean showing that actual DAG semantics on slices
  yield the one-sided certificate used by the weak route;
- the theorem is genuinely weaker than the current global stable-restriction
  route;
- the endpoint has been explicitly reviewed against locality-barrier concerns;
- we have written down why this endpoint is plausibly close to theorem-minimal
  relative to current literature.

### Task 4. Keep the current stable-restriction route as a stronger optional path

**Priority:** medium.

Progress update (2026-03-26):
- `pnp3/LowerBounds/DAGStableRestrictionProducer.lean` now contains an explicit
  witness-indexed `semantic-cone / restriction-extraction / numeric /
  restrictionData` stack for slice DAG solvers:
  `SmallDAGWitnessSemanticConeCertificateAt`,
  `SmallDAGWitnessRestrictionExtractionAt`,
  `SmallDAGWitnessRestrictionNumericDataAt`,
  `SmallDAGWitnessRestrictionCertificateDataAt`,
  `smallDAGWitnessShrinkageCertificateAt_of_restrictionData`,
  `smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider`,
  `smallDAGWitnessRestrictionExtractionAt_of_semanticConeCertificate`,
  `smallDAGWitnessRestrictionExtractionProviderOnSlices_of_semanticConeProvider`,
  `smallDAGLocalityStatement_of_semanticConeAndNumericProvider`,
  `smallDAGLocalityStatement_of_restrictionExtractionAndNumericProvider`.
- Concretely, the chain

  ```text
  SmallDAGWitnessOnSlice
    -> generalSolverOfSmallDAGWitnessOnSlice
    -> SmallDAGWitnessSemanticConeCertificateAt
    -> SmallDAGWitnessRestrictionExtractionAt
    -> SmallDAGWitnessRestrictionNumericDataAt
    -> SmallDAGWitnessRestrictionCertificateDataAt
    -> SmallDAGWitnessShrinkageCertificateAt
    -> DAGStableRestrictionSlackPackageAt
    -> SmallDAGImpliesCoordinateLocalityStatement
  ```

  is now compiled.
- So the stronger fallback blocker is no longer "build some DAG stable
  restriction package", and no longer "produce a shrinkage certificate" as a
  black-box object. The more precise source theorem is now split into two
  levels:
  first produce a semantic surviving-cone / forcing style certificate for the
  DAG-derived general solver on slices, then reduce it to semantic restriction
  extraction, then separately prove the numeric side conditions upgrading that
  extraction to `SmallDAGWitnessRestrictionCertificateDataAt`.
- Repo scan result: the current tree already contains formula-side analogues
  (`stableWitness_of_formula_supportBound`,
  `stableWitness_of_formula_sizeBound`) and certificate-driven downstream
  bridges (`PartialLocalityLift`, `ShrinkageCertificate.ofRestriction`), but no
  existing DAG-side theorem extracting a stabilizing restriction from a
  `SmallDAGWitnessOnSlice`.

Do:
1. Retain:
   - `DAGStableRestrictionCertificate`
   - `DAGStableRestrictionInvariantPackage`
   - `dagStableRestrictionInvariantProvider`
2. Reclassify them as stronger sufficient conditions, not as the canonical last
   blocker.
3. If helpful, add bridge lemmas:

   ```text
   strong stable restriction -> YesSubcubeCertificate
   ```

   or the analogous new weak endpoint.

Done when:
- the codebase has one primary endpoint and one stronger fallback endpoint,
  instead of presenting the stronger endpoint as mandatory.

### Task 5. Lift the DAG route to the asymptotic final surface

**Priority:** critical.

Current issue:
- many DAG closure lemmas are still naturally phrased at one fixed slice `p`.

Do:
1. Keep fixed-slice theorems as local building blocks only.
2. Add an asymptotic DAG endpoint matching the formula-side asymptotic shape.
3. Ensure the final theorem surface needed for `NP_not_subset_PpolyDAG` is over
   one asymptotic language/specification, not over one fixed finite slice.
4. Rewire `FinalResult.lean` so the default final DAG path is asymptotic in the
   same sense that the formula route already is.

Done when:
- the final default route to `NP_not_subset_PpolyDAG` / `P_ne_NP` no longer
  semantically depends on a single fixed `p`.

### Task 6. Replace the current DAG blocker in `FinalResult.lean`

**Priority:** medium after Tasks 1–5.

Do:
1. Add thin final wrappers from the new weak endpoint to:
   - `NP_not_subset_PpolyDAG`
   - `P_ne_NP`
2. Keep the older wrappers from stable-restriction and support-bounds routes for
   compatibility/audit.
3. Make the new weak endpoint the canonical remaining blocker in comments and
   theorem naming.

Done when:
- `FinalResult.lean` exposes the new primary endpoint and treats the old one as
  stronger/optional.

### Task 7. Add the parallel endpoint for a distinguisher/uniform route

**Priority:** strategic parallel track, but no longer optional background work.

Motivation from literature:
- recent distinguisher-based general magnification work suggests a route that
  may sidestep the localization barrier;
- therefore this track should be treated as a real parallel mainline, not just
  a speculative backup.

Do:
1. Add a separate endpoint interface for the alternative magnification route.
2. Keep it logically independent from the nonuniform DAG-route endpoint.
3. Record the exact theorem surface needed for a distinguisher/uniform closure
   of MCSP-style magnification.
4. Record explicitly which conclusion this route targets first:
   uniform MCSP consequence, nonuniform formula consequence, or full DAG/
   `P ≠ NP` consequence. Do not conflate these levels.
5. Add a note on adjacent learning/witness-finding formulations that may help
   specify the interface or provide constructive subgoals.
6. Do not let this route distort the correctness story of the current DAG
   route; it is a parallel path, not a post hoc gloss.

Done when:
- the repository contains a named secondary endpoint that could be used by a
  distinguisher-based proof line without reworking the main DAG consumer stack;
- docs treat this route as a real parallel program rather than an afterthought;
- the targeted consequence level of this route is stated explicitly.

### Task 8. Close the final external hypothesis and update wording

**Only after Tasks 1–7 are complete and one endpoint is actually proved.**

Do:
1. Internalize `NP_not_subset_PpolyDAG`.
2. Remove external `hNPDag` from `P_ne_NP_final*` wrappers.
3. Re-run:
   - `./scripts/check.sh`
   - `pnp3/Tests/AxiomsAudit.lean`
   - `pnp3/Tests/BarrierAudit.lean`
   - `pnp3/Tests/BarrierBypassAudit.lean`
   - `pnp3/Tests/BridgeLocalityRegression.lean`
4. Then update README/status docs to state unconditional status consistently.

Done when:
- `P_ne_NP_final*` no longer require external DAG-separation input.

---

## Concrete theorem-level subgoals to implement next

These are the most immediate Lean-facing tasks.

### Near-term theorem tasks

1. **Counting slack core**
   - closed on 2026-03-26:
     Shannon-counting now accepts slack directly and wrapper signatures no
     longer mention `hSlackToHalf`.

2. **Variant/validity layer**
   - define canonical validity objects for the endpoint layer;
   - separate truth-table objects, valid encodings, and arbitrary encoded
     inputs;
   - record explicit bridge lemmas between these worlds.
   - partial progress:
     `ValidEncoding` is now present and consumed by the new promise/value
     consumer and barrier route.

3. **Value/promise abstractions**
   - define `AgreeOnValues`;
   - define validity/promise-aware agreement predicates;
   - define value-level slack on truth-table coordinates.
   - partial progress:
     these are now present in code and exposed through the new
     promise/value source and consumer path.

4. **Weak endpoint certificate**
   - define `YesSubcubeCertificate` / `PromiseValueLocalityCertificate`.

5. **Weak endpoint consumer**
   - prove `no_small_dag_solver_of_yesSubcubeCertificate`.

6. **Bridge from existing strong route**
   - if easy, prove strong stable restriction implies the weak endpoint.

7. **Asymptotic DAG wrapper**
   - add an asymptotic `NP_not_subset_PpolyDAG` wrapper consuming the new
     weak endpoint.

8. **Distinguisher endpoint spec**
   - define the exact target consequence and signature for the parallel
     distinguisher/uniform route.

9. **Final result rewiring**
   - expose default thin wrappers in `pnp3/Magnification/FinalResult.lean`.

---

## Research-order recommendation

### Engineering track (should go first)

1. Task 2: value-only / promise-only interfaces.
2. Task 3: prove the weak endpoint is sufficient.
3. Task 5: asymptotic DAG final surface.
4. Task 6: `FinalResult` rewiring.

### Theory track A (main nonuniform mathematical risk)

After the weak endpoint is formally sufficient, attack the remaining theorem:

> small DAG solvers for asymptotic Gap-MCSP admit one-sided accepting
> value-subcube stability around some YES instance, with enough slack to force a
> NO completion.

This track should be continuously filtered through a locality-barrier test:
if a candidate proof idea appears to localize to small-fanin oracle-gate
extensions, it should be downgraded or abandoned early.

### Theory track B (parallel distinguisher mainline)

In parallel, build the alternative distinguisher/uniform endpoint so the whole
project is not bottlenecked on one localization-sensitive nonuniform route.
Treat this as a real parallel research program, not merely a backup note.

Use this track with explicit scope control:
- do not silently upgrade a uniform MCSP consequence into a nonuniform DAG or
  `P ≠ NP` consequence;
- but do use recent distinguisher-based results to calibrate how weak the
  endpoint interface can plausibly be.

### Restricted-model ladder

Use bounded/structured circuit classes (for example comparator circuits and
other shrinkage-friendly models) as a discovery tool for the right invariant.
This track is not just for intermediate publications; it is a probe for which
endpoint statements are mathematically realistic beyond the current singleton
collapse.

---

## Non-goals / avoid

1. Do **not** present the current strong
   `dagStableRestrictionInvariantProvider` as the only honest remaining
   theorem-level blocker.
2. Do **not** keep the final contradiction dependent on `hSlackToHalf`.
3. Do **not** formulate the final open endpoint over arbitrary encoded-input
   locality if value-only/promise-only locality suffices.
4. Do **not** rely on a fixed-slice theorem as the final separation surface.
5. Do **not** route the mainline through DAG→Formula conversion unless that
   bridge becomes genuinely easier than the new weak endpoint.
6. Do **not** adopt a new endpoint or proof paradigm without checking whether it
   is plausibly localizable in the sense highlighted by the hardness-
   magnification locality literature.
7. Do **not** treat the distinguisher-based route as mere documentation garnish;
   if kept, it should remain a concrete parallel theorem-development track.
8. Do **not** transfer claims across MCSP variants (MCSP / Partial-MCSP /
   Gap-MCSP / oracle-MCSP) or across consequence levels (uniform / nonuniform /
   formula / DAG / `P ≠ NP`) without an explicit bridge theorem in the repo.

---

## Done criteria

All of the following must hold simultaneously before the repository can claim
unconditional `P ≠ NP`.

1. `NP_not_subset_PpolyDAG` is proved in-repo with no external DAG hypothesis.
2. Default final wrappers no longer take `hNPDag`.
3. Build-critical counting/locality path uses real slack and no temporary
   bridge assumptions.
4. Final theorem surface is asymptotic.
5. Docs report unconditional status consistently.
