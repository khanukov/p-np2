# Project Status (current)

Updated: 2026-04-23

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
- A separate restricted-model milestone surface now exists at
  `pnp3/LowerBounds/AC0_GapMCSP.lean`; it exposes the paper-facing fixed-slice
  AC0 endpoint `gapPartialMCSP_not_in_AC0`.

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

So the legacy support-bounds and multi-switching final routes are vacuous:
they compile, but they route through inconsistent assumptions.

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
integration with `i4_final_wiring_of_formulaCertificate`,
`NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`,
the promise-YES certificate route, and their `P ≠ NP` companions.

The single remaining typed-deliverable for the canonical track is the TM
verifier: see "What Is Still Open" below.

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

### Canonical-track TM-verifier deliverable

The canonical asymptotic infrastructure reduces the asymptotic-side
research-gap to a single typed object:

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

After this decomposition, the only remaining sub-obligation is to
construct a TM whose acceptance behaviour matches the (now-defined)
`decideAsymptotic` function, with polynomial runtime.  All decidability
and language correctness are closed; the engineering reduces to
"build a TM that ignores `w` and computes a known Bool function on `x`".

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

## Repository-Wide Honesty Policy

Any file claiming unconditional `P != NP` is inaccurate until the project has a
non-vacuous replacement for the false support-bounds/multi-switching source and
a zero-argument final theorem that does not depend on external provider
payload.
