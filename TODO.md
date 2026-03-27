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

> a one-sided, promise-aware, value-only, promise-only **accepted-family**
> certificate stating that a small solver accepts a sufficiently large family
> of valid truth tables, large enough to exceed the counting capacity of all
> circuits of size `≤ sNO - 1`.

Canonical final consumer name (working):

- `AcceptedFamilyCertificateAt`.

Structured producer specializations may remain stronger routes into this final
consumer, for example:

- `YesSubcubeCertificateAt` (YES-centered value-subcube route),
- `PRGImageAcceptanceAt` (accepted structured-image / generator route),
- or another injective accepted-family package.

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
  needs;
- even `YesSubcubeCertificateAt` is now best treated as a strong structured
  producer target, not as the most general final consumer.

Progress update (2026-03-26):
- the generic final weak-route consumer is now formalized in code via
  `pnp3/LowerBounds/AcceptedFamilyBarrier.lean`:
  `AcceptedFamilyCertificate`,
  `no_function_solves_mcsp_of_acceptedFamilyCertificate`;
- the slice-level DAG-facing endpoint is now also present:
  `AcceptedFamilyCertificateAt`,
  `no_small_dag_solver_of_acceptedFamilyCertificateAt`,
  `acceptedFamilyCertificateAtProviderOnSlices`,
  `noSmallDAG_of_acceptedFamilyCertificateAtProviderOnSlices`;
- the asymptotic barrier layer now also exposes the same weak endpoint
  natively:
  `SmallDAGImpliesAcceptedFamilyAt`,
  `SmallDAGImpliesAcceptedFamilyStatement`,
  `no_dag_solver_of_acceptedFamily_at`,
  `no_dag_solver_of_acceptedFamily`,
  `magnificationStyleNoSmallDAG_of_eventually_acceptedFamily`;
- the one-sided weak-route endpoint is already formalized in code as
  `YesSubcubeCertificateAt`;
- the direct contradiction theorem already exists:
  `no_small_dag_solver_of_yesSubcubeCertificateAt`;
- the slice-family provider surface also exists:
  `yesSubcubeCertificateAtProviderOnSlices`;
- `YesSubcubeCertificateAt` is now wired as a structured producer into the
  generic accepted-family consumer via
  `acceptedFamilyCertificateAt_of_yesSubcubeCertificateAt` and
  `acceptedFamilyCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider`;
- the more realistic immediate source-side target for that route is now also
  formalized:
  `PromiseYesSubcubeCertificateAt`,
  `no_small_dag_solver_of_promiseYesSubcubeCertificateAt`,
  `promiseYesSubcubeCertificateAtProviderOnSlices`,
  `noSmallDAG_of_promiseYesSubcubeCertificateAtProviderOnSlices`,
  together with the reductions
  `promiseYesSubcubeCertificateAt_of_yesSubcubeCertificateAt` and
  `promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt`,
  plus direct package-route closure
  `noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices`;
- the semantic heart of that mainline target is now also split out explicitly
  as `PromiseYesAcceptanceInvariantAt`, together with the numeric upgrade
  `promiseYesSubcubeCertificateAt_of_acceptanceInvariant`;
- the currently chosen candidate proof mechanism for that semantic heart is now
  explicit in code as `PromiseYesDecisionCertificateAt`: a one-sided
  YES-certificate-complexity style object saying that, on valid promise inputs,
  agreement with one YES center on `S` already forces the solver decision;
- crucial sanity check: the bare decision-certificate mechanism is now also
  shown to be too weak as a standalone blocker, via
  `promiseYesDecisionCertificateAt_fullValueCoordinates`;
  every correct small DAG witness already has such a certificate with
  `S = univ` by choosing an easy all-false YES center;
- this mechanism now reduces mechanically to the current semantic target via
  `promiseYesAcceptanceInvariantAt_of_decisionCertificate`;
- the quantitative operational form of the real blocker is now also explicit in
  code via `promiseYesSubcubeCertificateAt_of_decisionCertificate`, i.e.
  a YES-centered decision certificate plus slack on the same `S` is already
  enough to recover `PromiseYesSubcubeCertificateAt`;
- the current pairwise fallback route already feeds this semantic invariant via
  `promiseYesDecisionCertificateAt_of_promiseValueLocalityPackageAt` and then
  `promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt`, so the
  remaining research gap is now more precise:
  prove a *quantitatively small* YES-centered certificate directly from DAG
  semantics, not just a bare decision certificate; the real difficulty is now
  explicit smallness/slack on `S`, because the existence-only form is vacuous;
- the strong encoded-coordinate fallback now also partially feeds the weak
  mainline under one precise additional hypothesis:
  `promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported`
  and
  `promiseYesSubcubeCertificateAt_of_dagStableRestrictionSlackPackageAt_valueSupported`
  show that a slack restriction package already yields the one-sided weak route
  once its surviving `alive` set is supported only on semantic value
  coordinates;
- the asymptotic/barrier layer now also exposes that nearer-term mainline
  theorem target directly via
  `SmallDAGImpliesPromiseYesSubcubeAt`,
  `SmallDAGImpliesPromiseYesSubcubeStatement`,
  `no_dag_solver_of_promise_yes_subcube_at`,
  `no_dag_solver_of_promise_yes_subcube`,
  `magnificationStyleNoSmallDAG_of_eventually_promiseYesSubcube`,
  with compiled witness-indexed bridges
  `smallDAGPromiseYesSubcubeStatement_of_certificateProvider`,
  `smallDAGPromiseYesSubcubeStatement_of_packageProvider`, and
  `smallDAGPromiseYesSubcubeStatement_of_yesSubcubeCertificateProvider`;
- a second non-subcube structured producer route is now also formalized:
  `PRGImageAcceptanceAt`,
  `acceptedFamilyCertificateAt_of_prgImageAcceptanceAt`,
  `acceptedFamilyCertificateAtProviderOnSlices_of_prgImageAcceptanceProvider`,
  `noSmallDAG_of_prgImageAcceptanceAtProviderOnSlices`;
- the witness-indexed producer layer now compiles directly into the canonical
  asymptotic accepted-family endpoint via
  `smallDAGAcceptedFamilyStatement_of_certificateProvider`,
  `smallDAGAcceptedFamilyStatement_of_yesSubcubeCertificateProvider`, and
  `smallDAGAcceptedFamilyStatement_of_prgImageAcceptanceProvider`;
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
  `smallDAGLocalityStatement_of_restrictionDataProvider`.

Design correction:
- the canonical final weak-route consumer should now be a generic accepted-family
  endpoint rather than exact subcube geometry.
- `YesSubcubeCertificateAt` should remain as one important structured producer
  into that final consumer.

Do:
1. Prove a source theorem of the form:

   ```text
   SmallDAGWitnessOnSlice -> AcceptedFamilyCertificateAt
   ```

   or, if the proof naturally goes through a stronger structured producer,
   prove one of:

   ```text
   SmallDAGWitnessOnSlice -> YesSubcubeCertificateAt
   SmallDAGWitnessOnSlice -> PRGImageAcceptanceAt
   ```

   and then reduce to the generic accepted-family consumer.
2. Make explicit which semantic invariants are acceptable producer targets:
   one-sided YES-centered stability, accepted PRG image, or another injective
   accepted family — not pairwise locality as the canonical final target.
   The current nearest mainline theorem target is now explicitly the
   asymptotic/barrier-level one-sided promise statement
   `SmallDAGImpliesPromiseYesSubcubeStatement`, not the pairwise locality
   schema.
   Immediate subgoal inside that route: prove a quantitatively nontrivial
   YES-centered certificate, i.e. `PromiseYesSubcubeCertificateAt` itself or an
   equivalent one-sided certificate carrying an explicit smallness/slack bound
   on `S`, operationally packaged as
   `PromiseYesDecisionCertificateAt + hSlack`.
   Bare `PromiseYesDecisionCertificateAt` is already too weak.
   The strong fallback now splits cleanly into two distinct readings:
   - to recover the chosen one-sided YES-centered route itself, it is enough to
     extract a value-supported stabilizing restriction
     (`promiseYesSubcubeCertificateAt_of_dagStableRestrictionSlackPackageAt_valueSupported`);
   - but to feed the terminal weak consumer `AcceptedFamilyCertificateAt`,
     value-support is no longer needed:
     `acceptedFamilyCertificateAt_of_dagStableRestrictionSlackPackageAt`
     already turns any encoded-coordinate slack package into a large accepted
     family by restricting to total truth-table encodings.
   This is now compiled not only as a local contradiction but also at provider
   level via
   `acceptedFamilyCertificateAtProviderOnSlices_of_dagStableRestrictionSlackPackageAtProvider`,
   `smallDAGAcceptedFamilyStatement_of_dagStableRestrictionSlackPackageAtProvider`,
   and the downstream shrinkage / restriction-data specializations.
   Moreover, the strong sprint target is now slightly narrower than "full
   shrinkage package": `dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound`
   and
   `dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndNumeric`
   show that semantic restriction extraction plus the quarter/half alive bound
   already suffice for the encoded-coordinate slack package.
   There is now also a first closed restricted-model theorem on this route:
   `smallDAGWitnessRestrictionExtractionAt_of_support` extracts a stabilizing
   restriction directly from `DagCircuit.support`, and
   `dagStableRestrictionSlackPackageAt_of_supportHalfBound` plus
   `no_small_dag_solver_of_supportHalfBound_via_acceptedFamily`
   show that any slice-DAG whose output support is at most half the truth-table
   length already contradicts correctness through the strong accepted-family
   route.
   On the chosen weak mainline there is now a first quantitative restricted-model
   foothold as well:
   `promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported`,
   `promiseYesSubcubeCertificateAt_of_supportHalfBound_valueSupported`,
   and
   `no_small_dag_solver_of_supportHalfBound_valueSupported`
   show that if the output support is both small and already confined to value
   coordinates, then the quantitative YES-centered route closes directly.
3. Add a **minimality benchmark subtask**: compare this endpoint against what is
   already enough in known magnification results (especially sparse-problem /
   formula thresholds) so we do not accidentally choose an endpoint stronger
   than the literature suggests is necessary.
4. Add a **barrier-screen subtask** before promoting this endpoint:
   test whether the endpoint/proof idea appears localizable in the sense
   highlighted by the hardness-magnification locality literature.
5. Only after the source theorem, minimality benchmark, and barrier-screen pass
   are in place, promote the new endpoint to the main blocker.

Done when:
- there is a proved theorem in Lean showing that actual DAG semantics on slices
  yield the generic accepted-family certificate used by the weak route, or a
  structured producer that automatically reduces to it;
- the terminal consumer no longer hardcodes subcube geometry;
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
3. If helpful, add bridge lemmas from stronger routes into the new weak-route
   consumer stack, for example:

   ```text
   strong stable restriction -> YesSubcubeCertificateAt
   YesSubcubeCertificateAt -> AcceptedFamilyCertificateAt
   PRGImageAcceptanceAt -> AcceptedFamilyCertificateAt
   ```

   or analogous producer-to-consumer reductions.

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

Progress update (2026-03-26):
- the generic accepted-family weak endpoint is now already compiled not only at
  slice/provider level, but also as a native asymptotic barrier schema via
  `SmallDAGImpliesAcceptedFamilyAt`,
  `SmallDAGImpliesAcceptedFamilyStatement`, and
  `magnificationStyleNoSmallDAG_of_eventually_acceptedFamily`;
- `FinalResult.lean` now documents that this weak endpoint exists at the
  asymptotic barrier level, but still does not expose thin final DAG wrappers
  consuming it directly.
- a repo scan confirms that the missing piece for those thin wrappers is no
  longer consumer-side endpoint shape, but a genuine bridge from global
  `ComplexityInterfaces.PpolyDAG` witnesses to the asymptotic
  `SmallDAGSolver` / `SizeBound` schema used by
  `MagnificationStyleNoSmallDAG`.

Do:
1. Add thin final wrappers from the generic accepted-family weak endpoint to:
   - `NP_not_subset_PpolyDAG`
   - `P_ne_NP`
2. Keep structured producer wrappers such as `YesSubcubeCertificateAt` / future
   `PRGImageAcceptanceAt` as intermediate compatibility surfaces if they remain
   useful.
3. Keep the older wrappers from stable-restriction and support-bounds routes for
   compatibility/audit.
4. Make the accepted-family weak endpoint the canonical remaining blocker in
   comments and theorem naming.

Done when:
- `FinalResult.lean` exposes the generic accepted-family endpoint as the main
  weak-route surface and treats older routes as stronger/optional.

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

4. **Generic accepted-family endpoint**
   - define `AcceptedFamilyCertificateAt` as the canonical final consumer.

5. **Generic accepted-family consumer**
   - prove `no_small_dag_solver_of_acceptedFamily`.

6. **Structured producer adapters**
   - prove `YesSubcubeCertificateAt -> AcceptedFamilyCertificateAt`;
   - define `PRGImageAcceptanceAt`;
   - prove `PRGImageAcceptanceAt -> AcceptedFamilyCertificateAt`.

7. **Bridge from existing strong route**
   - if easy, prove stronger route outputs feed one of the structured producers
     or the generic accepted-family endpoint directly.

8. **Asymptotic DAG wrapper**
   - add an asymptotic `NP_not_subset_PpolyDAG` wrapper consuming the generic
     weak endpoint.

9. **Distinguisher endpoint spec**
   - define the exact target consequence and signature for the parallel
     distinguisher/uniform route.

10. **Final result rewiring**
   - expose default thin wrappers in `pnp3/Magnification/FinalResult.lean`.

---

## Research-order recommendation

### Engineering track (should go first)

1. Task 2: value-only / promise-only interfaces.
2. Task 3a: generic accepted-family terminal consumer.
3. Task 3b: structured producer adapters (`YesSubcube`, `PRGImage`, etc.).
4. Task 5: asymptotic DAG final surface.
5. Task 6: `FinalResult` rewiring.

Status update (2026-03-26):
- Items 1-4 are now effectively complete at the infrastructure/barrier level:
  the repository already has the value-only / promise-only weak consumer,
  generic accepted-family terminal consumer, structured producers
  (`YesSubcubeCertificateAt`, `PRGImageAcceptanceAt`), and the asymptotic
  barrier-level accepted-family schema.
- Item 5 remains open only in the honest sense that thin final DAG wrappers
  still need a bridge from global `PpolyDAG` witnesses to the asymptotic
  `SmallDAGSolver` / `SizeBound` schema.
- From this point, further progress should not come from adding new endpoint
  infrastructure unless a concrete source theorem forces it.

### Theory track A (main nonuniform mathematical risk)

After the generic weak endpoint is formally sufficient, attack the remaining
source theorem:

> small DAG solvers for asymptotic promised Gap-MCSP accept a sufficiently
> large family of valid truth tables exceeding the counting capacity of all
> circuits of size `≤ sNO - 1`.

Preferred structured proof routes into this statement are:
- one-sided YES-centered acceptance (`YesSubcubeCertificateAt`),
- accepted structured images / generators (`PRGImageAcceptanceAt`),
- or another injective accepted-family package.

Active theorem-target policy (2026-03-26):
- keep `AcceptedFamilyCertificateAt` as the canonical terminal consumer;
- treat the promise-aware YES-centered route
  `PromiseYesSubcubeCertificateAt` as the current closest mainline theorem
  target, because it matches the existing one-sided counting consumer exactly
  and now already has a compiled reduction from the existing pairwise
  `PromiseValueLocalityPackageAt` surface;
- keep `YesSubcubeCertificateAt` as a stronger all-valid structured producer
  into `AcceptedFamilyCertificateAt`;
- keep `PRGImageAcceptanceAt` as the parallel structured-image backup target;
- do not re-promote exact subcube geometry as the only honest blocker unless
  the mathematics clearly forces it;
- do not spend more infrastructure effort on additional consumer generalization
  before one of these producer theorems has a concrete proof path.

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
- do use recent distinguisher-based results to calibrate how weak the accepted-
  family endpoint can plausibly be;
- explicitly test whether PRG-image / structured-image accepted families are a
  better fit than exact subcube geometry.

### Restricted-model ladder

Use bounded/structured circuit classes (for example comparator circuits and
other shrinkage-friendly models) as a discovery tool for the right invariant.
This track is not just for intermediate publications; it is a probe for which
endpoint statements are mathematically realistic beyond the current singleton

Current route split:
- weak-route mainline:
  `SmallDAGWitnessOnSlice -> PromiseYesSubcubeCertificateAt`
  and, if the stronger all-valid form becomes available,
  `PromiseYesSubcubeCertificateAt -> YesSubcubeCertificateAt`
  or direct contradiction via the one-sided counting consumer;
- weak-route stronger producer / terminal-consumer bridge:
  `SmallDAGWitnessOnSlice -> YesSubcubeCertificateAt`
  or
  `SmallDAGWitnessOnSlice -> PRGImageAcceptanceAt`
  then reduce to `AcceptedFamilyCertificateAt`;
- strong-route diagnostic only:
  `SmallDAGWitnessSemanticConeCertificateAt` and its downstream restriction /
  shrinkage stack;
- final wrapper work should remain downstream of whichever weak-route source
  theorem starts to look viable.
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
