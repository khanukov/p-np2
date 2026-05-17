# A01: Audit `pnp3/Magnification/*_Partial.lean`

**Engineer:** A01 | **Phase:** 0 — Repo audit | **Estimated:** 1 week | **Difficulty:** medium | **Type:** markdown-only

## Goal

Produce a comprehensive markdown audit of the 6 `*_Partial.lean` files under `pnp3/Magnification/`. Identify what's proven, what's staged as `Prop` placeholder, what's missing for pnp4 integration. Output: completion checklist for Phase 1+ dispatch.

## Files to audit

| File | LOC | Suspected content |
| --- | --- | --- |
| `pnp3/Magnification/Facts_Magnification_Partial.lean` | 235 | OPS-style triggers for partial-MCSP |
| `pnp3/Magnification/PipelineStatements_Partial.lean` | 286 | Magnification pipeline statements |
| `pnp3/Magnification/LocalityProvider_Partial.lean` | 3,677 | CHOPRS-style locality provider |
| `pnp3/Magnification/LocalityInterfaces_Partial.lean` | 57 | Locality interface definitions |
| `pnp3/Magnification/LocalityLift_Partial.lean` | 100 | Locality lift lemmas |
| `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` | 119 | Bridge from partial-MCSP to magnification |

**Total:** ~4,474 LOC.

## Deliverable

```
seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A01_pnp3_magnification_partial_<handle>.md
```

### Required sections

1. **Executive summary** (1 paragraph)
   - Are these files complete for partial-MCSP variant? Yes/No/Partial.
   - Is there a usable pnp4 integration path? Yes/No/Needs work.

2. **File-by-file audit** (one subsection per file)
   - Top-level structures and theorems (list with signatures).
   - What's proven (kernel-checked theorems).
   - What's staged as `Prop` placeholder (count + list).
   - Use of `Classical.choose` (count + locations).
   - Use of `sorry`, `admit`, `axiom`, `opaque` (must be zero; flag if any).
   - Trust-root dependencies (which `pnp3/Complexity/Interfaces.lean` definitions are used).

3. **Cross-file dependency graph**
   - Which files import which.
   - Are there cycles or hidden dependencies on `_Partial` siblings?

4. **Coverage matrix: partial-MCSP vs full-MCSP vs AC⁰[p]**
   - What's covered for partial-MCSP (the `_Partial` scope).
   - What's covered for full MCSP.
   - What's covered for AC⁰[p].
   - Gaps for each variant.

5. **pnp4 integration analysis**
   - Which `_Partial` theorems are usable from pnp4 (via existing imports)?
   - Which need adapter modules in pnp4?
   - Which require operator decision before integration (e.g., re-stating in pnp4-native form)?

6. **Recommended Phase 1+ completion tasks**
   - List of specific Lean tasks the operator should consider dispatching after this audit lands.
   - Each task: title, scope, estimated time, dependency on other Phase 1+ tasks.

7. **Honest caveats**
   - Document any place where the audit's claims rely on incomplete reading or where deeper investigation is needed.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Markdown report at exact path.
- [ ] All 6 files audited (no skipping; if a file is too large to read in detail, audit by structure-and-headers and document this).
- [ ] All 7 required sections present and substantive.
- [ ] Cross-file dependency graph as a text or markdown diagram.
- [ ] Recommended Phase 1+ tasks list with at least 3 concrete proposals (or "no completion tasks needed" with justification).
- [ ] No Lean files modified.

## Scope

### Allowed
- Reading all files in `pnp3/Magnification/`.
- Reading dependencies (`pnp3/Complexity/Interfaces.lean`, `pnp3/Models/*`).
- Writing the markdown audit report at the specified path.

### Forbidden
- ❌ Any Lean edits.
- ❌ Universal forbiddens (COMMON §3).

## Verification commands (operator)

```bash
ls seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A01_*.md
wc -l seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A01_*.md  # expect 200-500 LOC
grep -c "^#" seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A01_*.md  # at least 8 section headers
```

## Output

Universal template (COMMON §12). Add: "Audit completeness: <% of LOC carefully read>", "Recommended Phase 1+ tasks count: <N>".
