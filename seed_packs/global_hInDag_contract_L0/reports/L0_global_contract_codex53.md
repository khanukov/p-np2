# L0 global hInDag contract report (codex53)

## Scope and classification
- Classification: **Infrastructure** (contract-shape formalization and route-surface plumbing in `pnp3/Tests/`).
- Mainline progress claim: **none** (this does not directly reduce `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`).

## Deliverable
Landed `pnp3/Tests/GlobalHInDagContractProbe.lean` with all four requested pieces:
1. `GlobalAsymptoticDAGWitness` (Piece A)
2. `globalPolyDAGSizeBound` (Piece B)
3. `AsymptoticPromiseYesWeakRouteEventually_global` (Piece C)
4. `globalWitness_to_hInDag` (Piece D, general form)

## Proof strategy notes
- Piece D follows the slice-local projection pattern:
  - active encoded length uses `W.family activeLen`;
  - off-length uses `constFalseDag`;
  - correctness at active length is obtained by chaining:
    `W.decides_global` with `hAsym.sliceEq (max n hAsym.N0) ...`.
- This keeps the global contract in A–C while showing forward compatibility with existing per-slice `InPpolyDAG` surfaces.

## Hygiene / policy checks
- No `axiom`, `sorry`, `admit`, `native_decide`, `opaque` added.
- No forbidden imports used.
- Naming guard audit command executed:
  - `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/GlobalHInDagContractProbe.lean`
  - result: no matches.

## Build check
- Ran `./scripts/check.sh`.
- Observation: build/check pipeline runs and continues across repository-wide targets; no task-local compile error surfaced in the new file during this run.

## Verdict
**RED_GLOBAL_CONTRACT_CORE_LANDED**

- Pieces landed: **A,B,C,D**
- Piece D form: **general**
- Anti-hardwiring lemma: deferred (documented only)
