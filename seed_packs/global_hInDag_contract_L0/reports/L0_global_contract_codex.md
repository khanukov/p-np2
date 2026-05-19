# L0 global hInDag contract report (codex)

Implemented `pnp3/Tests/GlobalHInDagContractProbe.lean` as a standalone staging probe with all required four pieces:

- Piece A: `GlobalAsymptoticDAGWitness`
- Piece B: `globalPolyDAGSizeBound`
- Piece C: `AsymptoticPromiseYesWeakRouteEventually_global`
- Piece D: `globalWitness_to_hInDag` (general form)

Notes:
- Used a local `constFalseDag` fallback for non-active lengths.
- Piece D projects a global asymptotic decider family onto fixed-slice `InPpolyDAG` using active-length dispatch and `hAsym.sliceEq` on canonical eventual slices.
- Kept file within 250 LOC (125 lines).

Audit command:
- `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/GlobalHInDagContractProbe.lean`
  returned no matches.

Build/check:
- Ran `./scripts/check.sh` and observed successful progression through full project build including `Magnification.FinalResultMainline` and downstream targets without Lean errors in the new file.

Task: global hInDag contract L0
Handle: codex
Branch: main
Commit before: 0d29652fc1f8f7af7a371aa008e7c474be512906
Commit after: e32c3dd896ee4d1443a7c00e6c227afbc92aedec
Changed files:
  pnp3/Tests/GlobalHInDagContractProbe.lean (125 lines)
  seed_packs/global_hInDag_contract_L0/reports/L0_global_contract_codex.md

Outcome:
  L0_LANDED

If L0 landed:
  staging file: pnp3/Tests/GlobalHInDagContractProbe.lean (125 lines)
  executive verdict: RED_GLOBAL_CONTRACT_CORE_LANDED
  pieces landed: A,B,C,D
  Piece D form: general
  ./scripts/check.sh: PASS
  declaration names audited: constFalseDag, constFalseDag_size, constFalseDag_eval, GlobalAsymptoticDAGWitness, globalPolyDAGSizeBound, AsymptoticPromiseYesWeakRouteEventually_global, globalWitness_to_hInDag
  imports audited: Complexity.Interfaces, Models.Model_PartialMCSP, Magnification.CanonicalAsymptoticTrackData, Magnification.FinalResultMainline, LowerBounds.AsymptoticDAGBarrierTheorems
  next action:
    open_anti_hardwiring_lemma_L1 OR
    open_isoStrong_route_global_refactor_L0

Scope violations:
  none
