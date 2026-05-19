# L0 global hInDag contract probe (codex53)

## Classification
Infrastructure task (staging probe + contract formalisation).

## Summary
Landed `pnp3/Tests/GlobalHInDagContractProbe.lean` with four required pieces:
- Piece A: `GlobalAsymptoticDAGWitness`.
- Piece B: `globalPolyDAGSizeBound`.
- Piece C: `AsymptoticPromiseYesWeakRouteEventually_global`.
- Piece D: `globalWitness_to_hInDag` (general form, not canonical-only).

Piece D builds a per-slice `InPpolyDAG` witness by:
- selecting `W.family activeLen` at the slice's active input length,
- using `constFalseDag` off-slice,
- proving correctness via `W.decides_global` + `hAsym.sliceEq` on-slice,
- using definitional `gapPartialMCSP_Language` off-slice.

## Audits run
- `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/GlobalHInDagContractProbe.lean`
  - Result: no matches.
- `./scripts/check.sh`
  - Result: build progressed through full project checks with existing repo warnings; no new errors from this staging file were observed.

## Verdict
**RED_GLOBAL_CONTRACT_CORE_LANDED**

- pieces landed: **A,B,C,D**
- Piece D form: **general**
- anti-hardwiring lemma: deferred
- recommended next action: `open_anti_hardwiring_lemma_L1` (or `open_isoStrong_route_global_refactor_L0`)
