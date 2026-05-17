# A04: Audit `pnp3/Barrier/`

**Engineer:** A04 | **Phase:** 0 | **Estimated:** 3 days | **Difficulty:** low-medium | **Type:** markdown-only

## Goal

Audit the 4 minimal barrier interface files in `pnp3/Barrier/`. Identify exact API surface, gaps for pnp4 extensions (B01-B03 will build on these), and any places where the minimal interface is already inhabited or proven non-trivial.

## Files

| File | LOC | Suspected |
| --- | --- | --- |
| `pnp3/Barrier/NaturalProofs.lean` | ~45 | RR triad interface |
| `pnp3/Barrier/Relativization.lean` | ~30 | Oracle-parametric statement scheme |
| `pnp3/Barrier/Algebrization.lean` | varies | AW interface |
| `pnp3/Barrier/Bypass.lean` | varies | Bypass-witness interface |

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A04_pnp3_barrier_<handle>.md`

### Required sections

1. **Executive summary**: are these 4 files trust-root-frozen? What's the boundary between "interface" (frozen) vs "concrete witnesses" (extensible in pnp4)?
2. **File-by-file**: list every `structure`, `def`, `theorem` with signature.
3. **Existing inhabitations**: are there any places in the repo that construct `RelativizationBypassWitness` or `NaturalProofBypassWitness` instances?
4. **Gaps for pnp4 extensions** (informs B01/B02/B03 tasks):
   - What concrete content is missing for each barrier?
   - What additional pnp4-side structures would augment without modifying pnp3?
5. **Cross-reference with `pnp3/Tests/BarrierAudit.lean`** if present.
6. **Phase 1+ recommendations** (likely "B01-B03 implementations should target these gaps").
7. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] All 4 barrier files audited verbatim (small files, full reads expected).
- [ ] Each barrier's gap-for-pnp4 explicitly enumerated.

## Scope

### Allowed
- Reading `pnp3/Barrier/*.lean` and any test/audit files referencing them.

### Forbidden
- Universal.

## Output
Universal template.
