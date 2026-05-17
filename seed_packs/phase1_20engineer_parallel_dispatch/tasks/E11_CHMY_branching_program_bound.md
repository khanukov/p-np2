# E11: CHMY 2021 branching program lower bound for MKtP

**Engineer:** E11 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** none

## Goal

Formalize the **statement** of CHMY 2021's branching-program lower bound: a nondeterministic or parity branching program of size `o(N^{1.5}/log N)` cannot compute MKtP. Symmetric branching programs for MCSP have size at least `N^{1.5-o(1)}`.

## Source material

* CHMY 2021, DOI 10.4230/LIPIcs.STACS.2021.23.
* Specific theorem: §1 / §4 — branching program bounds.

## Deliverable

```
pnp4/Pnp4/Literature/CHMY2021/BranchingProgramBound.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace CHMY2021

/-- Abstract branching program with size measure. -/
structure BranchingProgram (N : Nat) where
  size : Nat
  isNondeterministic : Bool := false
  isParityBP : Bool := false

/-- CHMY MKtP bound for nondeterministic / parity BPs. -/
structure CHMY_MKtP_BP_LowerBound where
  computes_MKtP : BranchingProgram → Prop
  bound : ∀ (BP : BranchingProgram), 
    computes_MKtP BP → 
    (BP.isNondeterministic ∨ BP.isParityBP) → 
    BP.size ≥ ...  -- N^{1.5-o(1)} approximation

/-- CHMY MCSP bound for nondeterministic / co-nondeterministic / parity BPs. -/
structure CHMY_MCSP_BP_LowerBound where
  computes_MCSP : BranchingProgram → Prop
  bound : ∀ (BP : BranchingProgram), 
    computes_MCSP BP → 
    BP.size ≥ ...  -- N^{1.5-o(1)} approximation
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `BranchingProgram`, `CHMY_MKtP_BP_LowerBound`, `CHMY_MCSP_BP_LowerBound` structures defined.
- [ ] One arithmetic helper lemma (e.g., `N^{1.5}` approximation).
- [ ] Module doc-comment cites CHMY 2021 §1 + §4.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/CHMY2021/BranchingProgramBound.lean`.

### Forbidden
- Universal.
- ❌ No theorem proof — only typed statement.

## Output
Universal template.
