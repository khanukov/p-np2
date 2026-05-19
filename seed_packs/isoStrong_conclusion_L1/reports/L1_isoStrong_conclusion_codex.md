## 1. Executive verdict

YELLOW_ONE_OF_THREE_LANDED

## 2. What landed

- `traceSize1CandidateOnRows`
- `exists_label_not_in_finite_trace_family`
- `diagonalPartialTable`
- `diagonal_z_valid`

## 3. Corrected trace argument

The key correction is to separate **variable-index traces** from **truth-table-row traces**.

- The old abstract helper `traceSize1CandidateOnFree` uses an embedding into `Fin n`, i.e. variable coordinates.
- For the concrete diagonalisation over free truth-table rows, we need rows in `Fin (2^n)` and must evaluate projection candidates via `Nat.testBit row i`.
- The new `traceSize1CandidateOnRows` does exactly that:
  - constants stay constant on all rows;
  - input candidate `i` returns the `i`-th bit of the row index.

This aligns the diagonal label with the MCSP partial-table coordinate semantics and avoids the false global shortcut about YES cardinality.

## 4. Remaining blockers

1. `diagonal_z_agrees_on_D`:

```lean
theorem diagonal_z_agrees_on_D
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \ D).attach → Bool) :
    AgreeOnValues D yYes (encodePartial (diagonalPartialTable p yYes D label))
```

2. Conversion from YES witness at `sYES = 1` to `Size1Candidate p.n` trace identity on free rows:

```lean
(∃ C, Circuit.size C ≤ 1 ∧ is_consistent C (decodePartial z))
  → ∃ c : Size1Candidate p.n, ...
```

3. The full contradiction lemma:

```lean
theorem diagonal_z_not_yes_of_label_not_trace ... :
  ¬ encodePartial (diagonalPartialTable p yYes D label) ∈ (gapSliceOfParams p).Yes
```

4. Final composition lemma:

```lean
theorem exists_valid_agreeing_not_yes_under_slack ...
```

## 5. Next action

open_isoStrong_conclusion_L1_session_3
