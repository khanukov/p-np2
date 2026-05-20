# L1 session 2 structured failure (codex53)

## Scope and intent
Attempted to land the session-2 general not-YES bridge in:
- `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`

Target theorem:
- `exists_valid_agreeing_not_yes_under_general_slack`

## What was attempted
Implemented (then reverted) the planned general-diagonal stack:
1. `generalDiagonalPartialTable`
2. `general_diagonal_z_valid`
3. `general_diagonal_z_agrees_on_D`
4. `is_consistent_general_diagonal_table_implies_trace_in_image`
5. `general_diagonal_z_not_yes_of_label_not_in_trace_image`
6. final composition theorem

## Precise blockers (Lean elaboration)
When compiling `Tests.GeneralIsoStrongNoGoProbe`, Lean reported stable elaboration/typeclass failures in this file:

1. **`Bitstring`/`circuitsOfSizeAtMost` not resolved in local context**
   - Errors of form `Function expected at Bitstring` and `Function expected at circuitsOfSizeAtMost`.
   - This indicates missing namespace openings/import alignment for these constants in this file’s current import/open profile.

2. **Subtype level mismatch around free-row index type**
   - Error form:
     - `Subtype.mk j` expected `{x // x ∈ Finset.univ \ D}` but received `Fin (...)`.
   - And later a goal with doubly-subtyped free-row index:
     - `a : {x // x ∈ (Finset.univ \ D).attach}`.
   - This indicates coercion/attachment mismatch between expected free-row domain and the concrete `label`/trace domain in the attempted statements.

3. **Bridge extraction mismatch for Yes-membership path**
   - Attempted direct route via `gapSlice` membership to `PartialMCSP_YES` did not fully elaborate under the file’s current local setup; unresolved goals persisted after extracting witness circuit.

## Why reverted
To keep repository green and avoid landing a broken probe file, the attempted edits to
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean` were reverted.

## Suggested next unblock sequence (session 2b)
1. First land a tiny local helper lemma in this file fixing the free-row type alias:
   - e.g. `abbrev FreeRows (p D) := (Finset.univ \ D).attach`.
2. Rebuild only the trace-equality lemma using that alias to avoid attach/subtype drift.
3. Add explicit namespace opens (`ComplexityInterfaces`, `Counting`) used by constants before introducing theorem statements with `Bitstring`/`circuitsOfSizeAtMost`.
4. Reuse the exact `gapSlice_yes_iff` pipeline from `IsoStrongConclusionProbe` with identical unfolding order, then generalize.
