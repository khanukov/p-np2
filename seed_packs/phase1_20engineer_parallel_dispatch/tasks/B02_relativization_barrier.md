# B02: Relativization (BGS) barrier — concrete oracle witnesses

> **DEFERRED (2026-05-17 plan reduction).** Not dispatchable in the current wave.
> Reason: spec explicitly authorizes placeholder relativized predicates and
> placeholder oracles; honest caveat acknowledges that making them concrete
> would require multi-month oracle-TM machinery. Wrapper surface, not a
> kernel-checked barrier theorem. Cancelled this phase.
> See `AUDIT_2026-05-17_PLAN_REDUCTION.md`.

**Engineer:** B02 | **Phase:** 3 — Barriers | **Estimated:** 3 weeks | **Difficulty:** high

## Goal

Extend the minimal `pnp3/Barrier/Relativization.lean` with pnp4-side **concrete oracle constructions**: an oracle making `P^A = NP^A` and another making `P^B ≠ NP^B`. Land kernel-checked `BGSRelativizationBarrier` instances.

**Do not modify `pnp3/Barrier/Relativization.lean`.**

## Source material

* Baker, Gill, Solovay, "Relativizations of the P =? NP question", SICOMP 1975. DOI: 10.1137/0204037.

## Deliverable

```
pnp4/Pnp4/Barriers/Relativization/Statement.lean
pnp4/Pnp4/Barriers/Relativization/CollapseOracle.lean
pnp4/Pnp4/Barriers/Relativization/SeparationOracle.lean
```

### Expected signatures (Statement.lean)

```lean
namespace Pnp4
namespace Barriers
namespace Relativization

def Oracle : Type := ∀ n : Nat, (Fin n → Bool) → Bool

def P_relativized (A : Oracle) : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop := ...
def NP_relativized (A : Oracle) : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop := ...

structure BGSRelativizationBarrier where
  collapse_oracle : Oracle
  collapses : ∀ L, NP_relativized collapse_oracle L → P_relativized collapse_oracle L
  separation_oracle : Oracle
  separates : ∃ L, NP_relativized separation_oracle L ∧ ¬ P_relativized separation_oracle L
```

### Expected signatures (CollapseOracle.lean)

```lean
/-- PSPACE-style collapse oracle (sketch; concrete construction multi-month). -/
def collapseOracle : Oracle := fun _ _ => false  -- placeholder; document as such
```

### Expected signatures (SeparationOracle.lean)

```lean
/-- BGS diagonal separation oracle (sketch). -/
def separationOracle : Oracle := fun _ _ => false  -- placeholder
```

### Lemmas

```lean
theorem BGS_no_relativizing_proof (B : BGSRelativizationBarrier) : 
    ¬ ∃ (P : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop),
      (∀ L A, P L ↔ P_relativized A L) ∧ (∀ L, ¬ P L) := by
  -- Routine contradiction from B.collapses and B.separates.
  ...
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Three modules at exact paths.
- [ ] `Oracle`, `P_relativized`, `NP_relativized`, `BGSRelativizationBarrier` defined.
- [ ] `BGS_no_relativizing_proof` theorem **proven kernel-clean** (no `sorry`).
- [ ] Two oracle placeholders (collapse + separation) defined.
- [ ] **`pnp3/Barrier/Relativization.lean` unchanged**.

### Honest caveats
- `P_relativized` and `NP_relativized` are placeholder predicates (returning a trivial `Prop`); making them concrete requires oracle TM machinery (multi-month). The structure proves the **statement** of the BGS barrier, not its full mathematical content.

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Barriers/Relativization/`.

### Forbidden
- Universal.
- ❌ Editing `pnp3/Barrier/Relativization.lean`.
- ❌ `sorry` in any final committed Lean.

## Output
Universal template.
