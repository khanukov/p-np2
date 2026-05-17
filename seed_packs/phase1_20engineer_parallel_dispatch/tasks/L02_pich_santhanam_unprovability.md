# L02: Pich-Santhanam bounded arithmetic unprovability surface

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reason: long-horizon literature investment not on shortest path to the active
> bottleneck. May be revived if a feasible-unprovability angle becomes the
> operator focus.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** L02 | **Phase:** 2 — Literature | **Estimated:** 3 weeks | **Difficulty:** high

## Goal

Formalize the Pich-Santhanam bounded-arithmetic unprovability framework as a Lean typed surface: certain feasible proof systems (S^1_2, APC_1, PV) cannot prove strong circuit lower bounds. Plus Carmosino-Kabanets-Kolokolova-Oliveira LEARN-uniform witnessing connection.

## Source material

* Pich, Santhanam, "Why are Proof Complexity Lower Bounds Hard?", FOCS 2019. DOI: 10.1109/FOCS.2019.00080.
* Pich, Santhanam, "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly", STOC 2021. DOI: 10.1145/3406325.3451117.
* Carmosino, Kabanets, Kolokolova, Oliveira, "LEARN-Uniform Circuit Lower Bounds and Provability in Bounded Arithmetic", FOCS 2021.

## Deliverable

```
pnp4/Pnp4/Literature/PichSanthanam/UnprovabilitySurface.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace PichSanthanam

/-- Abstract feasible theory. -/
structure FeasibleTheory where
  name : String  -- e.g., "S^1_2", "APC_1", "PV"
  proves : Prop → Prop

/-- Circuit lower-bound formula. -/
structure CircuitLowerBoundFormula where
  language : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage
  threshold : Nat
  asProp : Prop

/-- Pich-Santhanam unprovability statement. -/
structure PSUnprovability where
  theory : FeasibleTheory
  isFeasiblyNatural : CircuitLowerBoundFormula → Prop
  unprovabilityTheorem : ∀ Φ, isFeasiblyNatural Φ → ¬ theory.proves Φ.asProp

/-- LEARN-uniform witnessing (Carmosino-Kabanets-Kolokolova-Oliveira). -/
structure LEARNUniformWitnessing where
  theory : FeasibleTheory
  extractsLEARN : Prop
```

### Lemmas

```lean
theorem PSUnprovability.contraposition 
    (PSU : PSUnprovability) (Φ : CircuitLowerBoundFormula) 
    (hN : PSU.isFeasiblyNatural Φ) (hProves : PSU.theory.proves Φ.asProp) : False :=
  PSU.unprovabilityTheorem Φ hN hProves
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `FeasibleTheory`, `CircuitLowerBoundFormula`, `PSUnprovability`, `LEARNUniformWitnessing` structures.
- [ ] `contraposition` theorem proven.
- [ ] Module doc-comment cites all 3 papers.

### Honest caveats
- This is a typed surface. The actual bounded-arithmetic metatheorems (KPT witnessing, APC_1, S^1_2) would require multi-year formalization work.

## Scope

### Allowed
- New module at `pnp4/Pnp4/Literature/PichSanthanam/UnprovabilitySurface.lean`.

### Forbidden
- Universal.
- ❌ No formalization of actual proof-theoretic metatheorems.

## Output
Universal template.
