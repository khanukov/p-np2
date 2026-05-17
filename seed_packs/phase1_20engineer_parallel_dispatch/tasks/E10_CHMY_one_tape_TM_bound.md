# E10: CHMY 2021 one-tape TM lower bound for MCSP

**Engineer:** E10 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** none

## Goal

Formalize the **statement** of CHMY 2021's one-tape TM lower bound for MCSP: a randomized two-sided-error one-tape TM with an additional one-way read-only input tape cannot compute `MCSP[2^{μ₂·n}]` in time `N^{1.99}` for some `μ₂ > μ₁`.

## Source material

* Cheraghchi, Hirahara, Myrisiotis, Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", STACS 2021.
* DOI: 10.4230/LIPIcs.STACS.2021.23; journal: 10.1007/s00224-022-10113-9.

## Deliverable

```
pnp4/Pnp4/Literature/CHMY2021/OneTapeTMBound.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace CHMY2021

/-- Abstract one-tape randomized TM with read-only input tape. -/
structure OneTapeRandomizedTM where
  runTime : Nat → Nat
  errorProb : Rat  -- two-sided bounded error, e.g., 1/3

/-- CHMY's lower bound statement for `MCSP[s(n)]`. -/
structure CHMY_OneTapeTM_LowerBound where
  μ₁ μ₂ : Rat
  μ_ordered : μ₁ < μ₂
  -- For input length N = 2^n:
  -- No `OneTapeRandomizedTM` with runTime ≤ N^{1.99} computes MCSP at threshold 2^{μ₂·n}
  bound : ∀ (M : OneTapeRandomizedTM),
    (∀ n, M.runTime (2^n) ≤ (2^n) ^ (199/100) + 1) → 
    Prop  -- "M does not compute MCSP[2^{μ₂·n}]"

/-- The specific N^{1.99} runtime threshold. -/
def CHMY_runtime_threshold (N : Nat) : Nat := N ^ 2 / 100  -- approximation of N^1.99

theorem CHMY_threshold_polynomial (N : Nat) : 
    CHMY_runtime_threshold N ≤ N ^ 2
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `OneTapeRandomizedTM`, `CHMY_OneTapeTM_LowerBound` structures defined.
- [ ] `CHMY_runtime_threshold` defined as a Nat function.
- [ ] One arithmetic lemma proven kernel-clean.
- [ ] Module doc-comment cites CHMY 2021 verbatim.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/CHMY2021/OneTapeTMBound.lean`.

### Forbidden
- Universal.
- ❌ No claim that the CHMY theorem is proven in Lean — only the statement is typed.

## Output
Universal template.
