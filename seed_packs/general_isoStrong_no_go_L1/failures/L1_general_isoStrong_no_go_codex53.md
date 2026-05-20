# L1 general iso-strong no-go failure report (codex53)

## 1. What was attempted

Attempted to land the core general diagonal theorem
`exists_valid_agreeing_not_yes_under_general_slack` directly in
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, using counting bricks from
`Tests.CircuitCountTraceBoundProbe` and the canonical diagonal pattern from
`Tests.IsoStrongConclusionProbe`.

## 2. Exact theorem target

```lean
theorem exists_valid_agreeing_not_yes_under_general_slack
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack :
      circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - D.card)) :
    ∃ z : Bitstring (partialInputLen p),
      ValidEncoding p z ∧
      AgreeOnValues D yYes z ∧
      ¬ z ∈ (gapSliceOfParams p).Yes
```

## 3. Where it broke

Two concrete blockers in this session:

1. notation/type-level friction around free-row subtype expressions and
   set-difference notation in the generalized diagonal table path;
2. proof search/normalization complexity escalation in the direct full
   theorem script while assembling the not-YES contradiction through
   `gapSlice_yes_iff` and `decodePartial_encodePartial` rewrites.

## 4. Local vs global obstruction

Local obstruction: this is a proof engineering blockage in the staging script,
not evidence of a global impossibility.

## 5. Recommended next move

Open `open_general_isoStrong_no_go_L1_session_2` and proceed by first landing
small helper lemmas in isolation:
- finite-image “label not in trace image” lemma on explicit `Finset` targets;
- generalized `is_consistent`-to-trace equality for bounded-size circuits;
- then compose into the final core diagonal theorem.
