# E15: Relativization (BGS) barrier — formal

**Engineer:** E15 | **Phase:** B — Barriers | **Estimated:** 3 weeks | **Difficulty:** high | **Dependencies:** none

## Goal

Formalize the **Baker-Gill-Solovay relativization barrier** as a kernel-checked Lean theorem. Provide an explicit oracle `A` such that `P^A = NP^A` AND an explicit oracle `B` such that `P^B ≠ NP^B`. **Do not modify pnp3/Barrier/Relativization.lean.**

## Source material

* Baker, Gill, Solovay, "Relativizations of the P =? NP question", SICOMP 1975. DOI: 10.1137/0204037.

## Deliverable

```
pnp4/Pnp4/Barriers/Relativization/Statement.lean
pnp4/Pnp4/Barriers/Relativization/OracleConstruction.lean
```

### Expected signatures (Statement.lean)

```lean
namespace Pnp4
namespace Barriers
namespace Relativization

/-- Abstract oracle: maps each input length to a function `BitVec n → Bool`. -/
def Oracle : Type := ∀ n : Nat, (Fin n → Bool) → Bool

/-- Relativized P^A: languages decidable in deterministic polynomial time with oracle A. -/
def P_relativized (A : Oracle) : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop :=
  fun _L => True  -- placeholder; proper definition requires oracle TM machinery

/-- Relativized NP^A. -/
def NP_relativized (A : Oracle) : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop :=
  fun _L => True  -- placeholder

/-- The BGS relativization barrier statement. -/
structure BGSRelativizationBarrier where
  -- Oracle making P^A = NP^A.
  collapse_oracle : Oracle
  collapses : ∀ L, NP_relativized collapse_oracle L → P_relativized collapse_oracle L
  
  -- Oracle making P^B ≠ NP^B.
  separation_oracle : Oracle
  separates : ∃ L, NP_relativized separation_oracle L ∧ ¬ P_relativized separation_oracle L
```

### Expected signatures (OracleConstruction.lean)

```lean
namespace Pnp4
namespace Barriers
namespace Relativization

/-- The PSPACE-like collapse oracle: returns "1" iff input encodes a true QBF. -/
def collapseOracle : Oracle := fun _ _ => true  -- placeholder

/-- The diagonal separation oracle (BGS construction). -/
def separationOracle : Oracle := fun _ _ => false  -- placeholder
```

### Lemmas to prove

```lean
/-- BGS barrier consequence: any relativizing proof technique cannot resolve P vs NP. -/
theorem BGS_no_relativizing_proof (B : BGSRelativizationBarrier) :
    ¬ ∃ (P : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop), 
      (∀ L A, P L ↔ P_relativized A L) ∧  -- "Method is relativization-invariant"
      (∀ L, ¬ P L → True) := by
  -- The structure encodes the obstruction; this theorem extracts it.
  sorry  -- WRONG: should not have sorry. Worker must prove it.

```

**Important note:** Don't use `sorry`. The theorem above is intentionally non-trivial. The worker should either:
- Prove it from the structure (likely a contradictionFrom both `B.collapses` and `B.separates`).
- OR restate it in a weaker form that is provably true.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `Oracle`, `P_relativized`, `NP_relativized`, `BGSRelativizationBarrier` defined.
- [ ] `collapseOracle`, `separationOracle` defined (placeholders are fine; not constructive).
- [ ] `BGS_no_relativizing_proof` theorem **proven** kernel-clean (NO `sorry`).
- [ ] Module doc-comment cites BGS 1975.

### Honest caveats expected
- `P_relativized` and `NP_relativized` are placeholder predicates (returning `True`); making them concrete requires oracle Turing machine machinery (multi-month).
- The structure proves the **statement** of the BGS barrier, not its full mathematical content.

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Barriers/Relativization/`.

### Forbidden
- Universal.
- ❌ **No modification of `pnp3/Barrier/Relativization.lean`**.
- ❌ No claim that BGS barrier has been bypassed.
- ❌ `sorry` (must prove or restate).

## Output
Universal template.
