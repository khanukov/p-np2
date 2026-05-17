# A10: Cross-cutting audit of `_Partial`/`_Legacy`/TODO/placeholder markers

**Engineer:** A10 | **Phase:** 0 | **Estimated:** 3 days | **Difficulty:** low-medium | **Type:** markdown-only

## Goal

Repository-wide search for code markers indicating incomplete work, legacy code, placeholders, or staged `Prop` obligations. Produce a comprehensive inventory.

## Search patterns

```bash
# In pnp3 and pnp4:
rg -nl "_Partial\|_Legacy" --type lean pnp3 pnp4    # files with these suffixes
rg -n "TODO\|FIXME\|XXX\|HACK" pnp3 pnp4
rg -n "placeholder" pnp3 pnp4
rg -n "True\s*--\s*placeholder" pnp3 pnp4           # `Prop` placeholder pattern
rg -n "noncomputable" pnp3 pnp4                     # may indicate avoided constructivity
rg -n "Classical\.choose" pnp3 pnp4                 # classical hot spots
rg -n "axiom\s" pnp3 pnp4                           # any axiom declarations (should be 0)
```

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A10_partial_legacy_markers_<handle>.md`

### Required sections

1. **Executive summary**: total marker counts; concerning hot spots.
2. **`_Partial` file inventory**: list all files with this suffix; brief role of each (cross-reference A01/A05 for the magnification ones).
3. **`_Legacy` file inventory**.
4. **TODO/FIXME/HACK locations**: file:line + 1-line context. Categorize: code-style / actual TODO / known-incomplete.
5. **`placeholder` keyword locations**.
6. **`Prop` placeholder pattern (e.g., `True  -- placeholder`)**: locations + structures.
7. **`noncomputable` audit**: list every `noncomputable def`; categorize as (a) standard exponent extraction OK, (b) avoidable with effort, (c) genuinely required.
8. **`Classical.choose` audit**: locations; categorize as above.
9. **`axiom` declarations**: should be zero — flag any.
10. **Phase 1+ recommendations**: prioritize the most concerning markers for cleanup or completion.
11. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] All 9 marker categories searched repo-wide.
- [ ] Each `_Partial` file referenced with its role.
- [ ] At least 5 concrete Phase 1+ cleanup/completion recommendations.

## Scope

### Allowed
- Reading any file; running `rg`, `grep`, `find`.

### Forbidden
- Universal.

## Output
Universal template.
