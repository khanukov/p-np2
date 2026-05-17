# A06: Audit `pnp3/Models/` + non-trust-root `pnp3/Complexity/`

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reason: broad audit of model + complexity layers; valuable for maintainability
> but not shortest-path to wave-1 objectives. Trust-root files in `pnp3/Complexity/`
> are already protected by build invariants.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** A06 | **Phase:** 0 | **Estimated:** 1 week | **Difficulty:** medium | **Type:** markdown-only

## Goal

Audit `pnp3/Models/*.lean` (MCSP variant definitions, partial-MCSP, circuit models) and the non-trust-root parts of `pnp3/Complexity/` (everything outside `Interfaces.lean` and `PsubsetPpolyInternal/`). Map MCSP/circuit model coverage.

## Files (discover via `find`)

```bash
find pnp3/Models pnp3/Complexity -name "*.lean" | grep -v PsubsetPpolyInternal | grep -v "^pnp3/Complexity/Interfaces.lean"
```

Likely includes:
- `pnp3/Models/Model_PartialMCSP.lean` (or similar) — partial-MCSP definition
- `pnp3/Models/Circuit.lean` and friends — circuit models
- Other `pnp3/Complexity/*.lean` non-internal files

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A06_pnp3_models_complexity_<handle>.md`

### Required sections

1. **Executive summary**: how complete is the MCSP/circuit-model formalization?
2. **MCSP variants**: partial-MCSP, exact-MCSP, gap-MCSP, search-MCSP — which are defined; which align with pnp4 `SearchMCSPCompressionProblem`?
3. **Circuit model audit**: `DagCircuit`, `FormulaCircuit`, `Pnp3.Models.Circuit` — what's the relationship?
4. **Truth-table infrastructure**: `Pnp3.Models.Partial.tableLen`, `TruthTable`, related.
5. **Non-trust-root `pnp3/Complexity/`**: file-by-file audit; identify what's used externally.
6. **Phase 1+ recommendations**: e.g., "extend partial-MCSP to formula-MCSP variant for X target".
7. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] All discovered files audited at top-level theorem/structure granularity.
- [ ] MCSP-variant cross-reference table.
- [ ] At least 3 Phase 1+ recommendations.

## Scope

### Allowed
- Reading `pnp3/Models/*` and `pnp3/Complexity/*` (except `Interfaces.lean` and `PsubsetPpolyInternal/` — those are trust-root, read-only by everyone, but readable; don't recommend edits to them).

### Forbidden
- Universal.

## Output
Universal template.
