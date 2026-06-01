# Project Status (current)

Updated: 2026-05-28

Authoritative checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Simulation fine-grained boundary:
`pnp3/Docs/Simulation_FineGrained_Status.md`.
Research method boundary:
`pnp3/Docs/Research_Method_Boundary.md`.

## Verified State

- Active `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes on the current tree (strict policy:
  no `sorry`/`admit` anywhere, no `sorryAx` in any term).
- Inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- That inclusion theorem is coarse polynomial-size DAG inclusion only; it is
  not a fine-grained Cook-Levin or hardness-magnification compiler adequacy
  theorem.
- The repository contains substantial DAG endpoint plumbing, including the
  fixed-slice DAG-to-formula bridge
  `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`.
- A separate restricted-model surface exists at
  `pnp3/LowerBounds/AC0_GapMCSP.lean`; it exposes the paper-facing
  fixed-slice AC0 endpoint `gapPartialMCSP_not_in_AC0`.  This is a
  side artifact / formalization milestone, not the current P-vs-NP
  mainline; it is not a planned closure route unless paired with an
  explicit bridge to `ComplexityInterfaces.NP_not_subset_PpolyDAG`
  (consistent with `AGENTS.md` and `pnp4/README.md`).

## Current Audit Result

There is still **no unconditional in-repo theorem** `P != NP`, and the
current blockers are sharper than the old "remove residual payload" wording.

The active public DAG endpoint is now the honest research-gap boundary:

```text
NP_not_subset_PpolyDAG_final
  (gap : ResearchGapWitness)

P_ne_NP_final
  (gap : ResearchGapWitness)
```

The legacy `hMS`/provider/support-bounds endpoints still compile, but they are
explicitly audit routes in `Magnification.FinalResultAuditRoutes`, not the
public closure boundary.  The falsifiability audit proves:

- `FormulaSupportRestrictionBoundsPartial -> False`
- `FormulaSupportBoundsFromMultiSwitchingContract -> False`
- `MagnificationAssumptions -> False`
- `FormulaSupportBoundsPartial_fromPipeline -> False`
- `MagnificationAssumptions_fromPipeline -> False`
- `FormulaCertificateProviderPartial -> False` (Probe 13, PR 13 audit)

So the legacy support-bounds, multi-switching, and certificate-provider
final routes are vacuous: they compile, but they route through inconsistent
assumptions.

**Note on PR #1366 canonical asymptotic infrastructure.**  PR #1366 landed
`canonicalAsymptoticHAsym` (unconditional fill of the
`AsymptoticFormulaTrackHypothesis` data structure) and a 7-session
TM-verifier construction plan for the canonical spec.  Probe 13 above shows
that the downstream wiring `i4_final_wiring_of_formulaCertificate` (the
consumer of a hypothetical `canonicalAsymptoticNPBridge_of_TM W`) is
ex-falso via `FormulaCertificateProviderPartial -> False`.  Therefore:

- The canonical infrastructure (slice-equality bridge, computable decider,
  TM-verifier scaffold) is sound Lean engineering and can be retargeted.
- The 7-session TM-verifier construction targeting `canonicalAsymptoticSpec`
  is **NOT** a path to unconditional `NP ⊄ P/poly` in the current
  formalization.  A future TM-witness consumer must route through a NEW
  provider that does not universally quantify over `PpolyFormula` (so it
  is not satisfied by truth-table hardwiring).

**Note on post-PR13 retarget chain (May 2026).**  The post-PR13 audit chain
landed three D0 / L0 deliverables under `seed_packs/`:

1. `seed_packs/post_pr13_provider_retarget_D0` (opus47):
   `RETARGET_EXISTING_ROUTE` — identified
   `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` and
   `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` as the
   two non-refuted DAG-side consumers of the canonical track.
2. `seed_packs/asymptotic_isostrong_route_audit_D0` (gpt55, PR #1378):
   `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS` — confirmed neither
   route imports `FormulaCertificateProviderPartial` or universally
   quantifies over `PpolyFormula`, and that NOGO-000004/6/8/9 do not
   transfer.
3. `seed_packs/hInDag_triviality_probe_D0` (gpt55, PR #1383):
   `YELLOW_INCONCLUSIVE` — no markdown-only argument settles the
   triviality question; blocking construction is either
   `canonicalAsymptotic_in_P` (multi-session TM-verifier plan) OR a
   direct DAG truth-table hardwiring at fixed slice.
4. `seed_packs/hInDag_triviality_probe_L0` (gpt55, PR #1388):
   `RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN` — the L0-A route closed.
   `pnp3/Tests/HInDagTrivialityProbe.lean` (121 LOC, kernel-checked,
   no `axiom`/`opaque`/`sorry`/`native_decide`, no refuted-predicate
   imports) defines:

   ```lean
   noncomputable def fixedSlice_gapPartialMCSP_in_PpolyDAG
       (p : GapPartialMCSPParams) : InPpolyDAG (gapPartialMCSP_Language p)

   noncomputable def hInDag_for_canonicalAsymptoticHAsym :
       ∀ n β, InPpolyDAG (gapPartialMCSP_Language
         ((eventualGapSliceFamily_of_asymptotic
             canonicalAsymptoticHAsym).paramsOf n β))
   ```

   via per-slice truth-table DAG hardwiring at the single encoded length
   `partialInputLen p` plus `constFalseDag` elsewhere.  The polynomial
   bound holds with a slice-dependent constant `K_p` because
   `InPpolyDAG.polyBound_poly` requires polynomiality in the input
   length `n`, and constant-in-`n` is polynomial.

**Structural consequence of the L0 landing.**  Both
`AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` and
`AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` have
the shape `∀ hInDag, <structural conclusion>`.  With
`hInDag_for_canonicalAsymptoticHAsym` now Lean-witnessed, the `∀`
collapses to instantiation at the hardwired witness.  But the derived
`ppolyDAGSizeBoundOnSlicesEventually F hInDag` under truth-table
`polyBound = K_p` is a per-slice constant of order `2^N` at canonical
input length `N = 2 · 2^m`, doubly-exponential in the slice index.
"Small DAG" under this bound admits essentially every DAG of size
`≤ 2^N`, so the iso-strong / promise-YES conclusions now ask for
YES-isolating combinatorial structure for **arbitrary-size DAGs**, not
just polynomial-size DAGs.

**Note on canonical asymptotic track conclusion-side refutation
(May 2026, completed).**  Following the L0 hInDag triviality
landing, the audit chain continued with three additional D0 and L0
deliverables that ultimately **refuted the canonical track at the
conclusion level**:

5. `seed_packs/global_hInDag_contract_repair_D0` (codex53, PR #1396):
   `REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS` — proposed
   `GlobalAsymptoticDAGWitness` structure with single shared
   `(coeff, exponent)` polynomial bound to structurally close the
   hardwiring loophole.
6. `seed_packs/global_hInDag_contract_L0` (gpt55, PR #1404):
   `RED_GLOBAL_CONTRACT_CORE_LANDED` — landed
   `pnp3/Tests/GlobalHInDagContractProbe.lean` (116 LOC) with
   `GlobalAsymptoticDAGWitness` + `globalPolyDAGSizeBound` +
   `AsymptoticPromiseYesWeakRouteEventually_global` +
   `globalWitness_to_hInDag` forward projection.  Hypothesis-side
   hardwiring loophole structurally closed.
7. `seed_packs/isoStrong_conclusion_audit_D0` (codex53, PR #1407):
   `INCONCLUSIVE_NEEDS_LEAN_PROBE` — 4/4 D0 workers identified the
   conclusion-side question needs Lean probe.
8. `seed_packs/isoStrong_conclusion_L0` (codex, PR #1413):
   `YELLOW_PARTIAL_LANDING` — landed
   `pnp3/Tests/IsoStrongConclusionProbe.lean` (80 LOC; now archived under
   `archive/pnp3/Tests/`, subsumed by stage 14) with `F_Mof =
   n+2` simp lemma + `canonical_isoStrong_implies_eventual_strict_slack`
   slack-inequality extraction.  Identified pigeonhole
   z-construction as L1 blocker.
9. `seed_packs/isoStrong_conclusion_L1` (4 codex sessions, PRs
   #1416, #1423, #1427, #1433):
   **`RED_CONCLUSION_REFUTED`** — the canonical iso-strong route is
   **formally inconsistent** at canonical `sYES=1, sNO=2`.  Total
   staging file size: 409 LOC, kernel-checked, no `axiom`/`opaque`/
   `sorry`/`admit`/`native_decide`, no refuted-predicate imports.

The L1 chain (4 sessions) proved the **fourth major refutation** in
the post-PR13 chain via a corrected pigeonhole argument over
size-1 candidate traces on truth-table rows:

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

**Proof structure:**
1. Pigeonhole core (session 1): `Size1Candidate n` finite type with
   `Fintype.card = n + 2`; `exists_trace_not_size1_of_card_lt` shows
   that under slack `n + 2 < 2 ^ Fintype.card α`, there exists a
   Boolean labeling outside all size-1 traces.
2. Encoding bridge (session 2): `traceSize1CandidateOnRows` evaluates
   size-1 candidates on truth-table rows via `Nat.testBit`;
   `diagonalPartialTable` constructs the candidate counterexample
   `z := encodePartial (diagonalPartialTable p yYes D label)`;
   `diagonal_z_valid` (ValidEncoding) and `diagonal_z_agrees_on_D`
   (AgreeOnValues) verify two of the three required properties.
3. Not-YES bridge + composition (session 3):
   `is_consistent_diagonal_table_implies_label_trace` (size-1
   consistency → label equals trace);
   `diagonal_z_not_yes_of_label_not_trace` (contradiction with
   label-not-in-trace hypothesis);
   `exists_valid_agreeing_not_yes_under_slack` (full composition).
4. Main theorem assembly (session 4):
   `correctOnPromiseSlice_of_InPpolyDAG_family` (lift InPpolyDAG to
   CorrectOnPromiseSlice); `slack_for_D_of_isoStrong_slack` (convert
   iso-strong slack κ-form to D.card-form); compose with `hForce`
   and `exists_valid_agreeing_not_yes_under_slack` to derive
   contradiction.

**Consequence.** The canonical asymptotic track via
`canonicalAsymptoticHAsym` is closed at conclusion level in the
following precise sense:

- The iso-strong route is formally refuted.  The in-build kernel-checked
  witness is the general theorem `isoStrong_conclusion_negative_general`
  (`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, stage 14 below), which
  subsumes the canonical instance `isoStrong_conclusion_negative_for_canonical`.
  The original canonical-specific staging probe
  (`IsoStrongConclusionProbe.lean`, stages 9–11) has been archived to
  `archive/pnp3/Tests/` now that the general theorem covers it.
- The promise-YES weak and promise-YES certificate routes are now also
  exposed as standalone Lean negation theorems in
  `pnp3/Tests/PromiseRouteConclusionProbe.lean`:
  - `promiseYesCertificate_conclusion_negative_for_canonical` and
  - `promiseYesWeak_conclusion_negative_for_canonical`,
  each with the same `∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym, ¬ ...`
  shape as the iso-strong companion.  They are corollaries of the
  iso-strong negation composed with the pointwise versions of the
  existing route-level implications
  `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
  (`pnp3/Magnification/FinalResultMainline.lean:348`) and
  `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
  (`pnp3/Magnification/FinalResultMainline.lean:400`).
- This makes the audit chain self-contained in Lean: instead of the
  closure of the certificate / weak routes living in the prose paragraph
  above, the closure is now three theorems with the same shape.
- Inhabitancy caveat: `GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`
  is referenced only as a universal hypothesis (`∀ W : ...`) in the
  inspected files; no explicit inhabitant is constructed in the current
  codebase.  This is recorded as context; the `∀ W, ¬P(W)` theorem is
  logically meaningful as-is.

This does **NOT** prove `P ≠ NP` or even `NP ⊄ P/poly`.  It rules
out the canonical asymptotic track at the canonical `sYES = 1,
sNO = 2` spec as a route to those endpoints.  Future P-vs-NP mainline
work must pivot to a different route family:

- pnp4 frontier `SearchMCSPWeakLowerBound` /
  `VerifiedNPDAGLowerBoundSource`;
- or genuinely new research-level mathematics proving
  `ResearchGapWitness` directly.

Restricted-model AC0 artifacts such as
`pnp3/LowerBounds/AC0_GapMCSP.lean::gapPartialMCSP_not_in_AC0` are
side artifacts / formalization milestones only.  They are not
treated as the current P-vs-NP mainline and are not a planned
closure route unless paired with an explicit bridge to
`ComplexityInterfaces.NP_not_subset_PpolyDAG` (consistent with the
restricted-track posture recorded in `AGENTS.md` and
`pnp4/README.md`).  A NEW canonical spec with non-trivial `sYES/sNO`
where the pigeonhole argument does not apply (i.e., `Mof` grows fast
enough relative to `tableLen` to invalidate the slack inequality
used in `slack_for_D_of_isoStrong_slack`) is also an internal
spec-engineering option, not a publishable route on its own.

**Audit chain summary (11 stages, all kernel-checked).**

| Stage | Verdict | Lean witness |
|---|---|---|
| 1. PR 13 / Probe 13 | `FormulaCertificateProviderPartial → False` | `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` |
| 2. post_pr13_provider_retarget_D0 (opus47) | RETARGET_EXISTING_ROUTE | markdown audit |
| 3. asymptotic_isostrong_route_audit_D0 (gpt55, #1378) | YELLOW | markdown audit |
| 4. hInDag_triviality_probe_D0 (gpt55, #1383) | YELLOW_INCONCLUSIVE | markdown audit |
| 5. hInDag_triviality_probe_L0 (gpt55, #1388) | RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN | `HInDagTrivialityProbe.lean` (121 LOC) |
| 6. global_hInDag_contract_repair_D0 (codex53, #1396) | REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS | markdown audit |
| 7. global_hInDag_contract_L0 (gpt55, #1404) | RED_GLOBAL_CONTRACT_CORE_LANDED | `GlobalHInDagContractProbe.lean` (116 LOC) |
| 8. isoStrong_conclusion_audit_D0 (codex53, #1407) | INCONCLUSIVE_NEEDS_LEAN_PROBE | markdown audit |
| 9. isoStrong_conclusion_L0 (codex, #1413) | YELLOW_PARTIAL_LANDING | `IsoStrongConclusionProbe.lean` (80 LOC; staging probe now archived under `archive/pnp3/Tests/`, subsumed by stage 14) |
| 10. isoStrong_conclusion_L1 sessions 1-3 (#1416, #1423, #1427) | YELLOW_PARTIAL chain | extends to 340 LOC |
| 11. isoStrong_conclusion_L1 session 4 (#1433) | **RED_CONCLUSION_REFUTED** | extends to 409 LOC; `isoStrong_conclusion_negative_for_canonical` formally proved (staging probe now archived; subsumed by stage 14's general theorem) |
| 12. general_isoStrong_no_go D0 (codex53, ffd47f6) | NEEDS_LEAN_PROBE | markdown audit |
| 13. circuit_count_trace_bound L0 (codex53, c436392) | GREEN_COUNTING_BRICKS_LANDED | `CircuitCountTraceBoundProbe.lean` (~120 LOC) |
| 14. general_isoStrong_no_go L1 sessions 1-4 (codex53+opus47, 75c5ae0 → 24d51510) | **RED_GENERAL_ISOSTRONG_REFUTED** | `GeneralIsoStrongNoGoProbe.lean` (~460 LOC); `isoStrong_conclusion_negative_general` formally proved over arbitrary `GapSliceFamilyEventually` |
| 15. general_isoStrong_route_closure (opus47) | **ROUTES_NAMED_AS_CLOSED** | `GeneralIsoStrongRouteClosure.lean` (~120 LOC); four named route-closure theorems |
| 16. promise_route_conclusion_companions | **CONCLUSION_COMPANIONS_NAMED** | `PromiseRouteConclusionProbe.lean`; `promiseYesCertificate_conclusion_negative_for_canonical` and `promiseYesWeak_conclusion_negative_for_canonical` standalone theorems with the same `∀ W, ¬ ...` shape as `isoStrong_conclusion_negative_for_canonical` |

The canonical asymptotic track is now closed at conclusion side via
standalone Lean theorems (iso-strong via the in-build general theorem
`isoStrong_conclusion_negative_general`, which subsumes the archived
canonical `isoStrong_conclusion_negative_for_canonical`; promise-YES
certificate and promise-YES weak via the two companions in
`PromiseRouteConclusionProbe.lean`).  The
four major refutations in the post-PR13 chain:

1. `FormulaCertificateProviderPartial → False` (PR 13, formula-side
   truth-table hardwiring).
2. `hInDag_for_canonicalAsymptoticHAsym` provable
   (L0 #1388, DAG-side per-slice truth-table hardwiring).
3. Global contract structurally closes hypothesis side
   (L0 #1404).
4. **`isoStrong_conclusion_negative_for_canonical` provable
   (L1 sessions 1-4, canonical track formally inconsistent at
   conclusion level).**

**Note on general iso-strong refutation and route-level closure
(May 2026, completed).**  Following the canonical L1 session 4
landing, the audit chain continued with a D0 audit, an L0 counting-
brick probe, and four L1 sessions that lifted the canonical
refutation to the general `GapSliceFamilyEventually` schema.  After
these steps the route-level refutation lives in
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean` as

```lean
theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
    ¬ IsoStrongFamilyEventually F hInDag
```

and the strategic consequence is packaged as four named theorems
in `pnp3/Tests/GeneralIsoStrongRouteClosure.lean`:

- `not_AsymptoticIsoStrongRoute_of_hInDag`
  (parameter-agnostic helper);
- `not_AsymptoticIsoStrongRoute_canonical`
  (instantiated via `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`);
- `not_AsymptoticPromiseYesCertificateRoute_canonical`
  (via `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`);
- `not_AsymptoticPromiseYesWeakRouteEventually_canonical`
  (via `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`).

All four are kernel-checked with standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`).  They make the iso-strong /
promise-YES certificate / promise-YES weak route class **formally
retired** at the canonical asymptotic instantiation: each named
theorem refutes the corresponding route prop directly, so a future
reader scanning the route catalogue can identify these three routes
as closed without re-deriving the meta-argument.

This does **NOT** prove `P ≠ NP` or `NP ⊄ P/poly`.  It closes the
iso-strong route class as a path to those endpoints; future
P-vs-NP mainline work must pivot to a different route family —
either the pnp4 frontier (`SearchMCSPWeakLowerBound` /
`VerifiedNPDAGLowerBoundSource`) or genuinely new research-level
mathematics proving `ResearchGapWitness`.  Restricted-model AC0
artifacts such as `gapPartialMCSP_not_in_AC0` are side artifacts /
formalization milestones only and are not a planned closure route
unless paired with an explicit bridge to
`ComplexityInterfaces.NP_not_subset_PpolyDAG` (see `AGENTS.md` /
`pnp4/README.md`).

## Fixed-Params Status

Session 67 introduced the stronger contract
`FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb`.

Session 68 established the current honest boundary:

- the Probe 7 singleton-provider attack does not directly port to fixed
  external `ac0` parameters;
- `fixedParams ac0 sb` alone is not currently refuted in the project;
- `fixedParams ac0 sb` plus uniform provenance for every formula witness under
  the same `ac0` reconstructs the old false support-bounds predicate;
- therefore the pair `fixedParams + uniformProvenance` is formally
  inconsistent in the current formalization.

The theorem
`NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance`
is useful as a gap-exposing theorem, not as progress toward an unconditional
claim.  Its assumptions describe the research-level hole.

The single-file boundary for future closure is
`pnp3/Magnification/UnconditionalResearchGap.lean`.  It contains
`ResearchGapWitness` and the compiled bridge
`P_ne_NP_of_researchGap : ResearchGapWitness -> P_ne_NP`; a future
unconditional proof should be localized there by proving
`ComplexityInterfaces.NP_not_subset_PpolyDAG` without using the refuted
support-bounds surfaces.

`ResearchGapWitness` is method-agnostic.  AC0/locality/restriction/shrinkage
routes, including `AcceptedFamilyCertificateAt`, are optional sufficient
routes and compatibility surfaces, not the required format for a future
algebraic, spectral, finite-field, SOS, or other non-combinatorial proof.

## What Is Closed

### Canonical asymptotic track (May 2026)

The asymptotic anti-checker pair `(hAsym, hNPbridge)` is no longer a
hypothesis parameter throughout the magnification mainline.  See
`pnp3/Magnification/CanonicalAsymptoticTrackData.lean`:

- `canonicalAsymptoticSpec : GapPartialMCSPAsymptoticSpec` — minimal legal
  asymptotic spec (`sYES = 1, sNO = 2`); all four structure fields built.
- `canonicalAsymptoticParams n hn : GapPartialMCSPParams` — per-slice
  parameters at slice `n ≥ 8` with Shannon-counting `circuit_bound_ok`
  proved unconditionally via `canonicalShannonBound`.
- `canonicalSliceEq : ∀ n hn x, asymp(...) = perSlice(...)` — Lean
  technical bridge for the `Classical.choose` dependent cast.  Closed via
  an `Eq.rec` motive parameterised over the type-level witness proof; the
  base case reduces the cast through `Subsingleton.elim` on the `Eq`
  proof.  The supporting helper
  `Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen` is in
  `Model_PartialMCSP.lean`.
- `canonicalAsymptoticHAsym : AsymptoticFormulaTrackHypothesis` —
  **unconditional**.
- `canonicalAsymptoticNPBridge_of_TM W`, `canonicalAsymptoticData_of_TM W`,
  `canonicalAntiCheckerAssumptions_of_TM W` — produce the strict NP
  package from a single concrete TM-verifier witness
  `W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

`pnp3/Tests/CanonicalIntegrationTests.lean` validates end-to-end
integration wiring surfaces, including
`i4_final_wiring_of_formulaCertificate` and
`NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`.
The canonical conclusion-side closure is witnessed in-build by the general
iso-strong theorem `isoStrong_conclusion_negative_general`
(`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`) together with the two canonical
promise companions `promiseYesCertificate_conclusion_negative_for_canonical` /
`promiseYesWeak_conclusion_negative_for_canonical`
(`pnp3/Tests/PromiseRouteConclusionProbe.lean`).  The canonical-specific
iso-strong staging probe (`isoStrong_conclusion_negative_for_canonical`,
`IsoStrongConclusionProbe.lean`) is archived under `archive/pnp3/Tests/` and is
subsumed by the general theorem.

The single remaining typed-deliverable for the independent canonical
infrastructure milestone (reusable NP-verifier scaffolding, not a
P-vs-NP closure route) is the TM verifier: see "What Is Still Open"
below.

### Inclusion side

- Default inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- Default final wrappers no longer need external inclusion-contract bundles.
- The simulation layer is closed only at the coarse `P_subset_PpolyDAG` level:
  its active size contract is existential polynomial (`n^k + k`), not a
  fine-grained overhead bound.  This is sufficient for
  `ResearchGapWitness -> P_ne_NP_final`, but not for any future route that
  depends on exact magnification slack.

### DAG plumbing

- The fixed-slice DAG-to-formula bridge exists.
- Route-B, source-closure, blocker, asymptotic, and `_TM` endpoint wrappers are
  implemented.
- This plumbing is useful for future magnification arguments.

### Fixed-slice no-go status

The historical fixed-slice support-half route is a closed no-go branch under
fixed-slice `PpolyDAG` membership:

- `no_fixedSlice_stableRestriction_of_inPpolyDAG`
- `no_fixedSlice_blocker_of_inPpolyDAG`
- `not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG`

## What Is Still Open

### Canonical-track TM-verifier deliverable (independent infrastructure milestone)

> **Scope note.**  After the canonical iso-strong / promise-YES
> conclusion-side refutations recorded above, the canonical asymptotic
> track is **no longer a P-vs-NP closure route**.  The TM-verifier
> deliverable below is therefore an independent formalization /
> infrastructure milestone for the reusable NP-verifier and decider
> scaffolding.  Finishing it does not reduce the `ResearchGapWitness`
> gap by itself, and it must not be presented as P-vs-NP progress.

Considered as an isolated infrastructure target, the canonical
asymptotic infrastructure reduces to a single typed object:

```
W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec
```

i.e., a concrete polynomial-time TM that verifies
`gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec` against a
size-1 circuit certificate.  Mathematically this is the published
OPS19/CJW20 fact `GapMCSP ∈ NP` (one-half-page argument in textbooks).

**Decomposition (May 2026)**:
`pnp3/Magnification/CanonicalAsymptoticDecider.lean` reduces the
obligation to a single TM-engineering target.  It contains:

- `decideAsymptotic : (n : Nat) → Bitstring n → Bool` — a computable
  decider equal pointwise to `gapPartialMCSP_AsymptoticLanguage
  canonicalAsymptoticSpec` (proved as `decideAsymptotic_iff`).
- `findCanonicalSlice` — fully axiom-free `Option Nat` detector for
  canonical input lengths `Partial.inputLen m = 2 · 2^m`.
- `decideYesAt1` — enumerates the `m + 2` size-1 circuit candidates
  and checks consistency via the now-proved `is_consistent_iff_bool`.
- `CanonicalAsymptoticVerifierComponents` — the minimum-sufficient
  structure: a TM `M` plus the property `accepts (x ++ w) = decideAsymptotic n x`
  for every certificate `w`, plus the polynomial-runtime bound.
- `witnessOfComponents : Components → GapPartialMCSP_Asymptotic_TMWitness
  canonicalAsymptoticSpec` — closed bridge.

After this decomposition, the only remaining sub-obligation **for the
infrastructure milestone** is to construct a TM whose acceptance
behaviour matches the (now-defined) `decideAsymptotic` function, with
polynomial runtime.  All decidability and language correctness are
closed; the engineering reduces to "build a TM that ignores `w` and
computes a known Bool function on `x`".  Again, this is reusable
NP-verifier infrastructure, not a P-vs-NP closure step.

**Multi-session plan**: see `pnp3/Docs/TMVerifier_Session_Plan.md` for
the 7-session decomposition (Variant B NP-style architecture):

1. Session 1: `seqList_run_full` (generic CS-composition correctness)
2. Session 2: `writeVecOfNatProgram` + `_run_full`
3. Session 3: `mcspCheckAllRows_correct`
4. Session 4: Witness decoder (`decodeCandidateSpec` + `_writeToTape_run_full`)
5. Session 5: `canonicalLengthCheckProgram_run_full`
6. Session 6: Top-level composition `verifierProgram_accepts_iff`
7. Session 7: Runtime bound + final `canonicalAsymptoticVerifierComponents` term

Each session = ~350 LOC, closes one leaf theorem with 0 sorry / standard
classical axioms.  Total estimated work: ~2500 LOC over 7 sessions.

### Research-gap source theorem (longer-horizon)

The remaining blocker is not endpoint plumbing.  It is the missing
non-vacuous source theorem for `ResearchGapWitness`, equivalently
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

A real lower-level route may still come from support/locality mathematics, but
only if it produces DAG separation through a provenance gate that:

1. does not quantify over arbitrary `PpolyFormula` witnesses;
2. cannot be satisfied by truth-table hardwiring or singleton provenance;
3. uses fixed, externally meaningful AC0 parameters;
4. does not combine with an overbroad uniform-provenance assumption to imply
   the old false support-bounds predicate.

That missing theorem is the research-level mathematical gap.  It should be
treated as open, not as a Lean engineering task.

Green CI and a passing `./scripts/check.sh` are formal hygiene checks, not
mathematical progress toward `NP_not_subset_PpolyDAG` by themselves.  They
prevent stale or vacuous route claims from re-entering the tree; they do not
replace the missing lower-bound idea.

### pnp4 conditional decision→search extraction chain (June 2026)

`pnp4/Pnp4/Frontier/ContractExpansion/` now formalizes a verified **conditional**
chain that replaces the abstract
`SearchMCSPMagnificationContract.magnifiesToVerifiedDAGSource` jump with explicit,
machine-checked interfaces: from a `PpolyDAG` membership of the prefix-extension
language it extracts a bounded search solver, and contrapositively
`NoPolynomialBoundedSearchSolver + growth ⇒ ¬ PpolyDAG`; combined with an
NP-membership witness it assembles a `VerifiedNPDAGLowerBoundSource`.

This is **not** unconditional progress: it proves neither `P ≠ NP` nor
`NP_not_subset_PpolyDAG`.  It only exposes the remaining mathematics as three
explicit, open inputs — (1) a genuine weak lower bound
`NoPolynomialBoundedSearchSolver`, (2) a concrete NP verifier witness
`PrefixExtensionNPWitness`, (3) a concrete witness codec (reduced, after the
`Circuit ↔ CircuitTree` bridge and encoding-length bound, to final assembly).
Input (1) is the same research-level lower-bound gap described above.  See
`pnp4/Pnp4/Frontier/ContractExpansion/README.md` for the full module map and the
proved-vs-open breakdown.

## Repository-Wide Honesty Policy

Any file claiming unconditional `P != NP` is inaccurate until the
project has either a non-vacuous replacement for the refuted
support-bounds / multi-switching source, or a direct method-agnostic
proof of `ResearchGapWitness` / `ComplexityInterfaces.NP_not_subset_PpolyDAG`
(algebraic, spectral, finite-field, SOS, Fourier-analytic, or other),
together with a zero-argument final theorem that does not depend on
external provider payload.
