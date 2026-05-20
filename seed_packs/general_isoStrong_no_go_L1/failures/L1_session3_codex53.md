# L1 session 3 structured failure (codex53)

## Executive verdict

INCONCLUSIVE_NEEDS_L2

## Attempted targets

- `is_consistent_general_diagonal_table_implies_trace_in_image`
- `general_diagonal_z_not_yes_of_label_not_in_trace_image`
- `exists_valid_agreeing_not_yes_under_general_slack`

## Precise blockers

1. **Trace-image family constant resolution in this module scope**

   In `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, references to
   `circuitsOfSizeAtMost` inside newly added theorem statements/proofs were not
   resolving to the expected counting constant from `Counting.CircuitCounting`.
   Lean elaborated it as a fresh metavariable/implicit (`x✝`), which then
   cascaded into image-membership and contradiction goals not closing.

2. **YES-membership bridge rewrite shape mismatch**

   For the target theorem
   `general_diagonal_z_not_yes_of_label_not_in_trace_image`, the direct rewrite
   path from
   `encodePartial (...) ∈ (gapSliceOfParams p).Yes`
   to an existential `⟨C, hSize, hCons⟩` required a more robust local bridge
   term than the attempted direct rewriting; the intermediate term shape in this
   file did not match the expected rewrite pattern without additional local
   helper lemmas.

3. **Subtype layering over `((Finset.univ \ D).attach)` in generalized trace**

   The generalized bridge proof over
   `traceCircuitOnRows ((Finset.univ \ D).attach) (fun a => a.1)` requires
   careful normalization of nested subtype projections (`a.1`, `a.1.1`, etc.)
   and alignment with `assignmentIndex_vecOfNat_eq`. The attempted proof
   skeleton reached local equalities but still left unresolved projection-shape
   obligations under this module’s elaboration context.

## Why this is L2-worthy

All blockers are proof-engineering/type-shape issues (namespace resolution,
rewrite bridge packaging, subtype normalization), not conceptual contradictions
with the intended theorem statements. The mathematical route remains plausible,
but requires a dedicated L2 cleanup pass with helper lemmas local to
`GeneralIsoStrongNoGoProbe`.

## Next action

open_general_isoStrong_no_go_L2_design
