# E16: Algebrization (Aaronson-Wigderson) barrier — formal

**Engineer:** E16 | **Phase:** B — Barriers | **Estimated:** 3 weeks | **Difficulty:** high | **Dependencies:** none

## Goal

Formalize the **Aaronson-Wigderson algebrization barrier** as a kernel-checked Lean theorem: any algebraic-oracle-invariant proof technique cannot resolve P vs NP. **Do not modify pnp3/Barrier/Algebrization.lean.**

## Source material

* Aaronson, Wigderson, "Algebrization: A New Barrier in Complexity Theory", STOC 2008. DOI: 10.1145/1374376.1374481.

## Deliverable

```
pnp4/Pnp4/Barriers/Algebrization/Statement.lean
pnp4/Pnp4/Barriers/Algebrization/AlgebraicOracle.lean
```

### Expected signatures (Statement.lean)

```lean
namespace Pnp4
namespace Barriers
namespace Algebrization

/-- An algebraic oracle: extends a Boolean oracle to a polynomial extension. -/
structure AlgebraicOracle where
  basicOracle : Pnp4.Barriers.Relativization.Oracle  -- depend on E15 if landed, else inline
  -- Algebraic extension: low-degree polynomial agreeing with the Boolean values
  algebraicExtension : Prop  -- placeholder for "exists low-degree polynomial extension"

/-- "Algebrizing" complexity inclusion: A ⊆ B "algebrizes" iff A^O ⊆ B^Õ
    for every oracle O and algebraic extension Õ. -/
def algebrizes (A B : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop) : Prop :=
  ∀ (O : AlgebraicOracle), True  -- placeholder for the actual algebrization predicate

/-- The Aaronson-Wigderson algebrization barrier. -/
structure AWAlgebrizationBarrier where
  -- Constructed oracle pair witnessing non-algebrization of P vs NP.
  oracle_collapse : AlgebraicOracle
  oracle_separate : AlgebraicOracle
  -- The barrier conclusion:
  noAlgebrizingProof :
    ∀ (proof : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop),
      algebrizes proof (fun _ => True) → 
      -- proof is algebrization-invariant ⇒ proof cannot decide P vs NP
      True  -- placeholder; refine to actual conclusion
```

### Expected signatures (AlgebraicOracle.lean)

```lean
namespace Pnp4
namespace Barriers
namespace Algebrization

/-- The IP=PSPACE algebraic oracle (Shamir 1992 style). -/
def IPPSPACEOracle : AlgebraicOracle := { 
  basicOracle := fun _ _ => false,
  algebraicExtension := True
}
```

### Lemmas to prove

```lean
/-- IP=PSPACE shows P^O ≠ NP^O is algebraic-oracle-sensitive: the algebraic
    extension can resolve relativizing barriers. -/
theorem IPPSPACE_algebrization_marker : True  -- placeholder

/-- AW barrier consequence: algebraic oracle pair forms obstruction. -/
theorem AW_barrier_consequence (B : AWAlgebrizationBarrier) : True := trivial
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `AlgebraicOracle`, `algebrizes`, `AWAlgebrizationBarrier` structures.
- [ ] `IPPSPACEOracle` defined (placeholder).
- [ ] Two trivial theorems proven kernel-clean.
- [ ] Module doc-comments cite Aaronson-Wigderson 2008.

### Honest caveats expected
- Most predicates are placeholders. The structural skeleton is in place; making each predicate operationally meaningful requires multi-month algebraic-oracle Turing machine machinery.

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Barriers/Algebrization/`.

### Forbidden
- Universal.
- ❌ **No modification of `pnp3/Barrier/Algebrization.lean`**.
- ❌ No claim that algebrization barrier has been bypassed.

## Output
Universal template.
