# A09: Audit `outputs/nogolog.jsonl` formal_witness fields

**Engineer:** A09 | **Phase:** 0 | **Estimated:** 3 days | **Difficulty:** medium | **Type:** markdown-only

## Goal

Verify that every existing NoGo entry's `formal_witness` field actually corresponds to a kernel-checked Lean theorem in the repo with matching content. Detect any stale, misnamed, or broken `formal_witness` claims.

## Files

```
outputs/nogolog.jsonl
```

Entries (as of audit time):
- NOGO-000001 .. NOGO-000005 — older entries (verify each)
- NOGO-000006 — `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean:101`
- NOGO-000007 — `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean:89`
- NOGO-000008 — `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean:207`
- NOGO-000009 — `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean:268`

(Plus any earlier entries — read jsonl completely.)

## Deliverable

`seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A09_nogolog_formal_witnesses_<handle>.md`

### Required sections

1. **Executive summary**: are all `formal_witness` fields valid (file exists, theorem at claimed line exists, signature matches description)?
2. **Per-NoGo verification table**:
   | NoGo ID | formal_witness path | File exists? | Theorem at line? | Signature matches `structural_pattern`? | Kernel-checked? |
3. **Compilation check**: do all referenced Lean files compile? (`lake build PnP3 Pnp4` already does this, but explicit confirmation per NoGo.)
4. **`status` field consistency**: each NoGo has `status: formalized` — verify the formal_witness actually formalizes the claim.
5. **`supersedes` chain**: NOGO-000007 generalizes 000006; verify the chain.
6. **Regression test verification**: each NoGo has `regression_test` field; verify those files exist and compile.
7. **Recommendations**:
   - Any broken or stale `formal_witness`? File for repair via Phase 1+.
   - Any place where the JSONL claim overstates what the Lean theorem proves? Document mismatch.
8. **Honest caveats**.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Report at exact path.
- [ ] Every NoGo entry in jsonl audited (count: must match line count of `outputs/nogolog.jsonl`).
- [ ] Per-NoGo verification table complete.
- [ ] Any mismatches documented as Phase 1+ repair tasks.

## Scope

### Allowed
- Reading `outputs/nogolog.jsonl` and all referenced Lean files.
- Running `lake build` to verify compilation status.

### Forbidden
- ❌ Editing `outputs/nogolog.jsonl`.
- ❌ Editing any referenced Lean file.
- Universal.

## Output
Universal template.
