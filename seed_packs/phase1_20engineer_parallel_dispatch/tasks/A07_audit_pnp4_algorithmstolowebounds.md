# A07: Audit `pnp4/Pnp4/AlgorithmsToLowerBounds/`

**Engineer:** A07 | **Phase:** 0 | **Estimated:** 1 week | **Difficulty:** medium | **Type:** markdown-only

## Goal

Audit all 24 files in `pnp4/Pnp4/AlgorithmsToLowerBounds/`. Map the AC⁰[p] → MCSP lower-bound pipeline. Identify the chain from coin problems, masking translation, local PRG, MCSP reductions, all the way to `BridgeToPpolyDAG.lean`.

## Files (24 known)

Read all from `pnp4/Pnp4/AlgorithmsToLowerBounds/`. Examples:
- `AC0pAsymptoticBridge.lean`
- `AC0pCoinAsymptotic.lean`
- `AC0pCoinLowerBound.lean`
- `AC0pSuperPolynomialBridge.lean`
- `AsymptoticSizeLowerBound.lean`
- `BasicCircuitClasses.lean`
- `BridgeToPpolyDAG.lean`
- `CoinMaskingTranslation.lean`
- `CoinProblem.lean`
- `FormulaCircuitAsymptotic.lean`
- `FormulaCircuitPublishedLowerBound.lean`
- `FormulaCircuitTargetModel.lean`
- `Growth.lean`
- `LocalPRG.lean`
- `LocalPRGHardnessSpec.lean`
- `MCSPCoinReduction.lean`
- `MCSPCoinReductionContract.lean`
- `MCSP_AC0p_Final.lean`
- `MCSP_AC0p_Quantitative.lean`
- `MCSP_Formula_Final.lean`
- `MCSP_Formula_Theorem2Quantitative.lean`
- `MCSP_LocalPRG_Transfer.lean`
- `SuperPolynomialBridge.lean`
- `TruthTableMCSP.lean`

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A07_pnp4_algorithmstolowebounds_<handle>.md`

### Required sections

1. **Executive summary**: is this an end-to-end AC⁰[p] → MCSP lower bound formalization? Is it complete? Conditional on what?
2. **Pipeline diagram**: data flow from `CoinProblem` → masking → local PRG → MCSP reduction → AC⁰[p] LB → ... → `BridgeToPpolyDAG`.
3. **File-by-file audit** (24 files; brief 2-3 sentence summary + key theorems per file).
4. **End-to-end theorem chain**: starting from `MCSP_AC0p_Final` / `MCSP_Formula_Final`, what's the final delivered theorem, and what bridges it to pnp3 `ResearchGapWitness`?
5. **Quantitative vs asymptotic**: how do `*_Final` and `*_Quantitative` relate?
6. **`BridgeToPpolyDAG.lean`** — what does it actually prove? Is this the bridge to `NP_not_subset_PpolyDAG`?
7. **Gaps**: any missing files, untyped `Prop` fields, `Classical.choose` usage hot spots.
8. **Phase 1+ recommendations**.
9. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] All 24 files referenced (at minimum: filename + 2-3 sentence role; longer for important ones).
- [ ] Pipeline diagram drawn.
- [ ] `BridgeToPpolyDAG.lean` audited in detail (it's the critical link).
- [ ] At least 5 Phase 1+ recommendations.

## Scope

### Allowed
- Reading all 24 files + their dependencies in pnp3 and pnp4.

### Forbidden
- Universal.

## Notes

- 24 files in 1 week = ~2-3 files per day at audit pace. Feasible.
- For the largest files, prioritize understanding the "top theorem" and its statement; details of lemmas are less critical for an audit.

## Output
Universal template.
