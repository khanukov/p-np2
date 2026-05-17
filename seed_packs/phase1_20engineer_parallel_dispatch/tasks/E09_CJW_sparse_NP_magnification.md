# E09: CJW 2019 sparse-NP-language magnification statement

**Engineer:** E09 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** none

## Goal

Formalize Chen-Jin-Williams 2019's **sparse-NP-language magnification** as a Lean typed surface: "if `L` is any sparse NP language, then a weak lower bound for `L` magnifies to a strong one".

## Source material

* Chen, Jin, Williams, "Hardness Magnification for all Sparse NP Languages", FOCS 2019.
* DOI: 10.1109/FOCS.2019.00077; ECCC TR19-118.

## Deliverable

```
pnp4/Pnp4/Literature/CJW2019/SparseNPMagnification.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace CJW2019

/-- A language is `α`-sparse if `|L ∩ {0,1}^n| ≤ n^α` for all `n`. -/
def IsSparse (α : Nat) (L : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage) : Prop :=
  ∀ n : Nat, (Finset.univ.filter (fun x : Pnp4.AlgorithmsToLowerBounds.BitVec n => L n x)).card ≤ n ^ α

/-- CJW magnification statement: any sparse NP language admits weak-to-strong
    magnification under the FML formula model. -/
structure CJWMagnificationStatement (α : Nat) (L : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage) where
  is_sparse : IsSparse α L
  -- "L ∉ FML[n^{1+ε}]" for some ε > 0
  weakBound : Prop
  -- "NP ⊄ FML[n^c]" for some c
  strongBound : Prop
  magnifies : weakBound → strongBound

/-- CJW's "sufficient sparsity" condition: `α = O(log n)` is enough. -/
def CJW_sufficient_sparsity (α : Nat) : Prop :=
  α ≤ 1  -- placeholder; CJW's actual condition is more nuanced
```

### Lemmas

```lean
theorem IsSparse.empty (α : Nat) : 
    IsSparse α (fun _ _ => false)

theorem IsSparse.monotone {α₁ α₂ : Nat} (h : α₁ ≤ α₂) {L} 
    (hα : IsSparse α₁ L) : IsSparse α₂ L
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `IsSparse`, `CJWMagnificationStatement`, `CJW_sufficient_sparsity` defined.
- [ ] Two lemmas proven kernel-clean.
- [ ] Module doc-comment cites CJW 2019 / FOCS 2019.
- [ ] **No claim** about specific NP languages being sparse or about magnification holding unconditionally.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/CJW2019/SparseNPMagnification.lean`.

### Forbidden
- Universal.
- ❌ No claim that any specific NP language is `α`-sparse for a useful `α`.

## Output
Universal template.
