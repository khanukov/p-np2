# Final Axiom Analysis (PNP3)

**Updated**: 2026-02-20

## 1. Active axiom count

- Active `axiom` declarations in `pnp3/`: **0**
- `sorry`/`admit` in active `pnp3/`: **0**

## 2. What is still external (but non-axiomatic)

1. Localized bridge goals in `pnp3/ThirdPartyFacts/PpolyFormula.lean`:
   - `GapPartialMCSPPpolyRealToPpolyFormulaGoal p`
2. Witness-backed shrinkage inputs in `pnp3/ThirdPartyFacts/Facts_Switching.lean`
   (through `FamilyIsAC0` / `FamilyIsLocalCircuit`).
3. Partial locality-lift card bounds (`hCardHalf`-style) in
   `pnp3/ThirdPartyFacts/PartialLocalityLift.lean` for certificate-driven flow.

## 3. Important correction

The active result should be described as a **conditional partial-track
separation** (`NP ⊄ PpolyFormula` under explicit hypotheses), not as an
unconditional final `P ≠ NP` theorem.

## 4. Current constructive blockers

- Constructive localized bridge (`GapPartialMCSPFormulaizer p` path).
- Constructive provider path that discharges `hCardHalf` automatically.
- Full internalization of Part A witness construction.

## 5. Conclusion

The repository is in a clean formal state (0 active axioms), with explicit and
narrowly-scoped remaining hypotheses documented in `STATUS.md`, `TODO.md`, and
`AXIOMS_FINAL_LIST.md`.
