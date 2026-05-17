# E12: Hirahara search-to-decision MCSP reduction surface

**Engineer:** E12 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** high | **Dependencies:** none

## Goal

Formalize the **statement** of Hirahara's search-to-decision reduction for MCSP (FOCS 2018 et seq.) as a typed surface: "a worst-case decision algorithm for MCSP yields a search algorithm at related complexity".

## Source material

* Shuichi Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS 2018.
* DOI: 10.1109/FOCS.2018.00021; arXiv:1804.05985.
* Follow-up: Hirahara, "Unexpected Hardness Results for Kolmogorov Complexity Under Uniform Reductions", STOC 2020. arXiv:2003.02485.

## Deliverable

```
pnp4/Pnp4/Literature/Hirahara2018/SearchToDecision.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace Hirahara2018

/-- Decision-MCSP solver: decides whether a truth table has circuits ≤ size s. -/
structure MCSPDecisionSolver where
  decide : ∀ (n s : Nat), (Fin (2^n) → Bool) → Bool
  -- decide n s tt = true iff ∃ circuit C of size ≤ s computing tt
  correctness : Prop  -- placeholder for actual semantic correctness

/-- Search-MCSP solver: given a truth table, produces a min-size circuit. -/
structure MCSPSearchSolver where
  search : ∀ (n : Nat), (Fin (2^n) → Bool) → Option (Pnp3.Models.Circuit n)
  correctness : Prop

/-- Hirahara's search-to-decision statement: a polynomial-time decision solver
    can be converted into a poly-time search solver at a small overhead. -/
structure HiraharaReduction where
  fromDecisionToSearch :
    MCSPDecisionSolver → MCSPSearchSolver
  runtimeOverhead : Nat  -- polynomial overhead factor
  correctness : Prop  -- "the resulting search solver is correct in the same regime as the input decision solver"
```

### Lemmas

```lean
theorem HiraharaReduction.exists_marker : True  
  -- placeholder: existence of the reduction is a literature reference
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `MCSPDecisionSolver`, `MCSPSearchSolver`, `HiraharaReduction` structures.
- [ ] `fromDecisionToSearch` field as data (not asserted theorem).
- [ ] Module doc-comment cites Hirahara FOCS 2018.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/Hirahara2018/SearchToDecision.lean`.

### Forbidden
- Universal.
- ❌ No claim that the reduction has been formally proven.
- ❌ No promotion to `accepted` status of any related guard.

## Output
Universal template.
