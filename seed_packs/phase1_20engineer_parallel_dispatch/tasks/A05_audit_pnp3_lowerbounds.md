# A05: Audit `pnp3/LowerBounds/`

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reason: `_Partial` files are largely covered by A10's cross-cutting inventory;
> deeper audit of LowerBounds is maintainability not shortest-path. Re-evaluate
> after wave-1 synthesis if AC⁰[p] routes become critical.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** A05 | **Phase:** 0 | **Estimated:** 1 week | **Difficulty:** medium | **Type:** markdown-only

## Goal

Audit the `pnp3/LowerBounds/` directory, including the two large `_Partial.lean` files (~2,290 LOC total). Map what's actually proven about formula lower bounds, anti-checker constructions, and how they feed into the magnification pipeline.

## Files (initial list; complete via `find pnp3/LowerBounds -name "*.lean"`)

| File | LOC | Suspected |
| --- | --- | --- |
| `pnp3/LowerBounds/AntiChecker_Partial.lean` | 2,068 | Anti-checker construction for partial-MCSP |
| `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean` | 222 | Core formula lower bound for partial-MCSP |
| (Any other `pnp3/LowerBounds/*.lean`) | varies | per `find` discovery |

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A05_pnp3_lowerbounds_<handle>.md`

### Required sections

1. **Executive summary**: what level of lower-bound formalization exists in `pnp3/LowerBounds/`? Restricted to partial-MCSP?
2. **File-by-file audit**.
3. **Anti-checker theorem map**: what does the anti-checker construction prove, against what circuit class, at what threshold?
4. **Formula LB chain**: `LB_Formulas_Core_Partial` → which downstream files? Does it feed `Facts_Magnification_Partial.lean` (OPS trigger)?
5. **Coverage gaps**: what's missing for full MCSP / AC⁰[p] / DAG-track lower bounds?
6. **Phase 1+ recommendations**.
7. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] AntiChecker_Partial.lean — must be at least header + top-level theorem-signature-level audit; not necessarily line-by-line for 2,068 LOC.
- [ ] LB_Formulas_Core_Partial — full audit feasible.
- [ ] At least 3 Phase 1+ recommendations.

## Scope

### Allowed
- Reading all `pnp3/LowerBounds/*.lean`.

### Forbidden
- Universal.

## Output
Universal template.
