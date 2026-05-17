# E13: Pich-Santhanam bounded arithmetic unprovability surface

**Engineer:** E13 | **Phase:** A | **Estimated:** 3 weeks | **Difficulty:** high | **Dependencies:** none

## Goal

Formalize the **statement** of Pich-Santhanam's bounded-arithmetic unprovability framework as a Lean typed surface: certain feasible proof systems (S^1_2, APC_1, PV) cannot prove strong circuit lower bounds.

## Source material

* Pich, Santhanam, "Why are Proof Complexity Lower Bounds Hard?", FOCS 2019.
* DOI: 10.1109/FOCS.2019.00080.
* Follow-up: Pich-Santhanam STOC 2021, "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly". DOI: 10.1145/3406325.3451117.
* Carmosino-Kabanets-Kolokolova-Oliveira FOCS 2021, "LEARN-Uniform Circuit Lower Bounds and Provability in Bounded Arithmetic". DOI: 10.1109/FOCS52979.2021.00080.

## Deliverable

```
pnp4/Pnp4/Literature/PichSanthanam/UnprovabilitySurface.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace PichSanthanam

/-- Abstract feasible theory (S^1_2, APC_1, PV, etc.). -/
structure FeasibleTheory where
  name : String  -- e.g., "S^1_2"
  -- Abstract: proves Φ iff there's a feasibly-presentable derivation
  proves : Prop → Prop

/-- A "circuit lower-bound statement" parameterized by language and threshold. -/
structure CircuitLowerBoundFormula where
  language : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage
  threshold : Nat
  asProp : Prop  -- "L requires circuits of size ≥ threshold"

/-- Pich-Santhanam unprovability: feasible theory T cannot prove certain CLB formulas. -/
structure PSUnprovability where
  theory : FeasibleTheory
  -- For any "feasibly natural" CLB formula Φ, T does not prove Φ.
  -- The full statement requires defining "feasibly natural"; here we capture it as a Prop.
  isFeasiblyNatural : CircuitLowerBoundFormula → Prop
  unprovabilityTheorem : 
    ∀ Φ : CircuitLowerBoundFormula, 
      isFeasiblyNatural Φ → ¬ theory.proves Φ.asProp

/-- LEARN-uniform witnessing extraction (Carmosino-Kabanets-Kolokolova-Oliveira). -/
structure LEARNUniformWitnessing where
  theory : FeasibleTheory
  extractsLEARN : Prop
  -- Standard claim: if T proves a circuit upper-bound formula, an efficient learner exists.
```

### Lemmas

```lean
theorem PSUnprovability.contraposition 
    (PSU : PSUnprovability) 
    (Φ : CircuitLowerBoundFormula) 
    (hN : PSU.isFeasiblyNatural Φ) 
    (hProves : PSU.theory.proves Φ.asProp) : False :=
  PSU.unprovabilityTheorem Φ hN hProves
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `FeasibleTheory`, `CircuitLowerBoundFormula`, `PSUnprovability`, `LEARNUniformWitnessing` structures.
- [ ] `contraposition` theorem proven.
- [ ] Module doc-comment cites all three papers (Pich-Santhanam 2019/2021, Carmosino et al. 2021).
- [ ] **No claim** that any specific theory or formula instantiates the structure.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/PichSanthanam/UnprovabilitySurface.lean`.

### Forbidden
- Universal.
- ❌ No formalization of the actual KPT witnessing theorem (multi-year work).
- ❌ No claim that any specific lower-bound proof is feasibly natural.

## Notes

- This is the most abstract task in Phase A. The deliverable is a clean typed surface that lets future work plug in concrete `FeasibleTheory` and `CircuitLowerBoundFormula` instances.
- 3-week estimate (1 extra) reflects the conceptual breadth.

## Output
Universal template.
