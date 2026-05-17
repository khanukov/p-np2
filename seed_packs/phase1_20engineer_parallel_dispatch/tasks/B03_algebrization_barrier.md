# B03: Algebrization (Aaronson-Wigderson) barrier — pnp4 extension

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reason: spec defines `algebrizes` as `True`-typed placeholder, allows
> `algebraicExtension := True`, and the named theorems are `trivial`. This is a
> wrapper surface, not a kernel-checked barrier theorem. Cancelled this phase.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** B03 | **Phase:** 3 — Barriers | **Estimated:** 3 weeks | **Difficulty:** high

## Goal

Extend the minimal `pnp3/Barrier/Algebrization.lean` with pnp4-side formalization of the Aaronson-Wigderson algebrization barrier: low-degree polynomial extensions of Boolean oracles + IP=PSPACE-style algebraic-oracle witness + barrier statement.

**Do not modify `pnp3/Barrier/Algebrization.lean`.**

## Source material

* Aaronson, Wigderson, "Algebrization: A New Barrier in Complexity Theory", STOC 2008. DOI: 10.1145/1374376.1374481.

## Deliverable

```
pnp4/Pnp4/Barriers/Algebrization/Statement.lean
pnp4/Pnp4/Barriers/Algebrization/AlgebraicExtension.lean
```

### Expected signatures (Statement.lean)

```lean
namespace Pnp4
namespace Barriers
namespace Algebrization

structure AlgebraicOracle where
  basicOracle : Pnp4.Barriers.Relativization.Oracle  -- (optional dependency on B02)
  algebraicExtension : Prop  -- existence of low-degree polynomial extension

def algebrizes (A B : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop) : Prop :=
  ∀ (O : AlgebraicOracle), True  -- placeholder for algebrization predicate

structure AWAlgebrizationBarrier where
  oracle_collapse : AlgebraicOracle
  oracle_separate : AlgebraicOracle
  noAlgebrizingProof : ∀ (proof : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop), 
    algebrizes proof (fun _ => True) → True
```

### Expected signatures (AlgebraicExtension.lean)

```lean
/-- The IP=PSPACE algebraic oracle (Shamir 1992 style); placeholder. -/
def IPPSPACEOracle : AlgebraicOracle := { 
  basicOracle := fun _ _ => false,
  algebraicExtension := True 
}
```

### Lemmas

```lean
theorem AW_barrier_consequence (B : AWAlgebrizationBarrier) : True := trivial

theorem IPPSPACE_algebrization_marker : True := trivial
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Two modules at exact paths.
- [ ] `AlgebraicOracle`, `algebrizes`, `AWAlgebrizationBarrier` structures.
- [ ] Two trivial theorems proven kernel-clean.
- [ ] Doc-comments cite Aaronson-Wigderson 2008.
- [ ] **`pnp3/Barrier/Algebrization.lean` unchanged**.

### Honest caveats
- Most fields are placeholders. The skeleton is in place; making each operationally meaningful requires multi-month algebraic-oracle TM machinery.

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Barriers/Algebrization/`.
- Optional dependency on B02 (Relativization) for the `Oracle` type — if B02 hasn't landed, define a local placeholder.

### Forbidden
- Universal.
- ❌ Editing `pnp3/Barrier/Algebrization.lean`.

## Output
Universal template.
