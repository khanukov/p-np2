/-!
  pnp3/AC0/MultiSwitching/FullSwitching.lean

  This file previously contained the axiom `ac0_formula_locality`,
  which claimed that any `AC0Formula n d` depends on at most `n / 4`
  of its input coordinates.

  ## Why the axiom was removed

  The axiom was **FALSE** as stated.  `AC0Formula.atom` wraps an
  arbitrary function `Core.BitVec n → Bool`, so
  `AC0Formula.atom parity` at depth 0 depends on all `n` coordinates,
  violating the `n / 4` bound.

  The intended mathematical content (multi-switching for bounded-depth
  formulas with literal atoms) requires formulas where depth-0 atoms are
  *literals* (single variables or their negations), not arbitrary
  functions.  The current `AC0Formula` type does not enforce this.

  ## Current approach

  The locality is now provided as a field (`decideLocal`) of the solver
  types, populated by the axiom `ppoly_circuit_locality` in
  `ThirdPartyFacts/PpolyFormula.lean`.  This axiom encapsulates the
  entire chain: P/poly → circuit → literal formula → multi-switching →
  locality, without going through the overly-general `AC0Formula` type.

  ## Future work

  To prove locality from first principles:
  1. Define `AC0LitFormula` with literal atoms (var/negVar)
  2. Prove multi-switching for `AC0LitFormula`
  3. Have `ppoly_circuit_locality` produce `AC0LitFormula`
  4. Derive locality as a theorem
-/
