# TODO / Roadmap (constructive closure)

Updated to match the current code state in `pnp3/`.

## Current checkpoint

- Active final chain is conditional and machine-checked.
- Bridge is localized to `gapPartialMCSP_Language p`.
- New constructive target interfaces are in place:
  - `GapPartialMCSPFormulaReifier`
  - `GapPartialMCSPFormulaizer`
  - `..._with_formulaizer` theorem family in bridge/final modules.
- Partial locality-lift now has a certificate-driven wrapper:
  - `stableRestriction_of_certificate`
  - `locality_lift_partial_of_certificate`
  (still requires explicit bound `hCardHalf`).

## Priority A (highest): close localized embed constructively

Goal: replace external localized embed goal hypothesis

`GapPartialMCSPPpolyRealToPpolyFormulaGoal p`

with a theorem obtained from:

`GapPartialMCSPFormulaizer p`.

### A1. Build explicit formula family

- Implement `familyOf` for an `InPpoly` witness of `gapPartialMCSP_Language p`.
- Avoid ad-hoc semantics: target `ComplexityInterfaces.FormulaCircuit`.

### A2. Prove semantic correctness

- Prove `familyCorrect` pointwise:
  `FormulaCircuit.eval (familyOf w n) x = gapPartialMCSP_Language p n x`.

### A3. Prove polynomial size bound

- Prove `familyPoly`:
  `FormulaCircuit.size (familyOf w n) <= n^c + c` for some global `c`.

### A4. Wire into active final chain

- Instantiate `NP_not_subset_PpolyFormula_final_with_formulaizer`.
- Remove dependence on `GapPartialMCSPPpolyRealToPpolyFormulaGoal` from the active path.

## Priority B: replace restriction provider hypothesis by constructive theorem

Current provider interface in active path:

`StructuredLocalityProviderPartial` (restriction-style witness).

### B1. Construct provider from switching/shrinkage witnesses

- Produce `RestrictionLocalityPartial p` from strict structured `PpolyFormula` witness.
- Keep bounds (`polylogBudget`) aligned with the current solver interfaces.
- Route through certificate API where possible:
  `ShrinkageCertificate.Provider` -> `stableRestriction_of_certificate` -> locality lift.

### B1.1 Discharge `hCardHalf` constructively

- Prove/derive the half-table bound for certificate restrictions in the target provider path:
  `restriction.alive.card ≤ Partial.tableLen p.n / 2`.
- Remove ad hoc/manual passing of this bound for the main path.

### B2. Remove provider hypothesis from external variants

- Replace `..._external` usage with constructive provider theorem.

## Priority C: close Part A witness externality

External witness-backed facts still required:

- `partial_shrinkage_for_AC0`
- `shrinkage_for_localCircuit`

### C1. Formalize witness constructors

- Internal constructors for `AC0CircuitWitness`.
- Internal constructors for `LocalCircuitWitness`.

### C2. Integrate with locality provider

- Use internal shrinkage constructors to derive B1 constructively.

## Completion criteria (100% constructive target)

1. `rg "^axiom " -g"*.lean" pnp3` remains empty.
2. `NP_not_subset_PpolyFormula_final` no longer needs external bridge/provider assumptions.
3. After non-uniform interface upgrade (`PpolyReal`), restore a sound `P ≠ NP` final bridge.
4. `lake build` and `scripts/check.sh` pass with no conditional gates.
