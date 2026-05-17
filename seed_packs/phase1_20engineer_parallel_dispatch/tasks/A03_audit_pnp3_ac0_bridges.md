# A03: Audit `pnp3/Magnification/AC0*.lean` + `Asymptotic*Collapse.lean`

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reason: scope overlap with A07 (`pnp4/Pnp4/AlgorithmsToLowerBounds/`) and A08
> (`pnp4/Pnp4/Frontier/`), both of which already cover AC⁰/MCSP/bridge surfaces.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** A03 | **Phase:** 0 | **Estimated:** 1 week | **Difficulty:** medium | **Type:** markdown-only

## Goal

Audit the AC⁰/locality bridge files in `pnp3/Magnification/` (~6 files, ~1,500 LOC). Identify how AC⁰[p] lower bounds connect to magnification → DAG collapse → `NP_not_subset_PpolyDAG`.

## Files

| File | Suspected role |
| --- | --- |
| `pnp3/Magnification/AC0LocalityBridge.lean` | AC⁰ locality bridge |
| `pnp3/Magnification/AC0AtlasBridge.lean` | AC⁰ atlas bridge |
| `pnp3/Magnification/AC0ApproxFamilyBridge.lean` | AC⁰ approximating family bridge |
| `pnp3/Magnification/AsymptoticDAGCollapse.lean` | Asymptotic DAG collapse theorem |
| `pnp3/Magnification/AsymptoticFormulaCollapse.lean` | Asymptotic formula collapse theorem |

Plus any `AC0*.lean` not listed above (cross-check via `find`).

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A03_pnp3_ac0_bridges_<handle>.md`

### Required sections

1. **Executive summary**: AC⁰ → DAG collapse pipeline complete? What's the input requirement (e.g., "AC⁰[p] lower bound of shape X")?
2. **File-by-file audit** with signatures.
3. **AC⁰[p] → P/poly bridge map**: which AC⁰ lower bounds (in pnp4 `AlgorithmsToLowerBounds`) feed into which `Magnification/AC0*` bridges → which `FinalResult*` → `ResearchGapWitness`.
4. **Asymptotic collapse coverage**: what input shape `AsymptoticDAGCollapse` / `AsymptoticFormulaCollapse` consume.
5. **Cross-track integration with pnp4**: which existing `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pSuperPolynomialBridge.lean` and friends already feed in (look for explicit imports).
6. **Phase 1+ recommendations**.
7. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] All AC⁰/Asymptotic files audited.
- [ ] Pipeline map drawn (text or markdown diagram).
- [ ] At least 3 concrete Phase 1+ recommendations.

## Scope

### Allowed
- Reading audited files + dependencies in pnp3 and pnp4.

### Forbidden
- Universal.

## Output
Universal template.
