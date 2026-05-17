# L01: Hirahara search-to-decision MCSP surface

**Engineer:** L01 | **Phase:** 2 — Literature | **Estimated:** 2 weeks | **Difficulty:** high

## Goal

Formalize Hirahara's **search-to-decision reduction for MCSP** (FOCS 2018+) as a Lean typed surface: "a polynomial-time decision algorithm for MCSP yields a search algorithm at related complexity".

## Source material

* Shuichi Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS 2018. DOI: 10.1109/FOCS.2018.00021; arXiv:1804.05985.
* Hirahara, "Unexpected Hardness Results for Kolmogorov Complexity Under Uniform Reductions", STOC 2020. arXiv:2003.02485.

## Deliverable

```
pnp4/Pnp4/Literature/Hirahara2018/SearchToDecision.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace Hirahara2018

/-- Decision MCSP solver. -/
structure MCSPDecisionSolver where
  decide : ∀ (n s : Nat), (Fin (2^n) → Bool) → Bool
  correctness : Prop  -- abstract: decide n s tt = true iff ∃ circuit ≤ size s

/-- Search MCSP solver. -/
structure MCSPSearchSolver where
  search : ∀ (n : Nat), (Fin (2^n) → Bool) → Option (Pnp3.Models.Circuit n)
  correctness : Prop

/-- Hirahara reduction: decision → search at poly overhead. -/
structure HiraharaReduction where
  fromDecisionToSearch : MCSPDecisionSolver → MCSPSearchSolver
  runtimeOverhead : Nat → Nat  -- polynomial overhead schedule
  correctness : Prop
```

### Lemmas

```lean
/-- The reduction exists as data; we don't prove its existence. -/
def HiraharaReduction.witness_marker : Prop := True

theorem HiraharaReduction.compositional 
    (R₁ R₂ : HiraharaReduction) : 
    ∃ R₃ : HiraharaReduction, True := ⟨R₁, trivial⟩
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `MCSPDecisionSolver`, `MCSPSearchSolver`, `HiraharaReduction` structures.
- [ ] `compositional` theorem proven.
- [ ] Module doc-comment cites Hirahara FOCS 2018 + STOC 2020.

### Honest caveats
- The reduction is captured as a `def` field, not as a proven theorem. The actual mathematical proof is multi-month.

## Scope

### Allowed
- New module at `pnp4/Pnp4/Literature/Hirahara2018/SearchToDecision.lean`.

### Forbidden
- Universal.
- ❌ No claim that the reduction is formally proven.

## Output
Universal template.
