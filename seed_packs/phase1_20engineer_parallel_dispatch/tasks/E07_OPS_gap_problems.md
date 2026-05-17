# E07: OPS 2021 Gap-MCSP / Gap-MKtP problem definitions

**Engineer:** E07 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** none

## Goal

Formalize Oliveira-Pich-Santhanam 2021's **Gap-MCSP** and **Gap-MKtP** promise problems as Lean structures with explicit threshold parameters `s_1(N), s_2(N)`.

## Source material

* OPS, "Hardness Magnification Near State-of-the-Art Lower Bounds", Theory of Computing 17(11), 2021.
* DOI: 10.4086/toc.2021.v017a011.
* Specific definitions: §1 / §2 Gap-MCSP and Gap-MKtP with thresholds.

## Deliverable

```
pnp4/Pnp4/Literature/OPS2021/GapProblems.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace OPS2021

/-- A Gap promise problem with two thresholds `s_1 ≤ s_2`. -/
structure GapPromiseProblem where
  N : Nat  -- input length (typically 2^n for truth-table-input problems)
  s_1 : Nat → Nat  -- low threshold
  s_2 : Nat → Nat  -- high threshold (s_2 > s_1)
  thresholdOrdered : ∀ n, s_1 n ≤ s_2 n
  yesPromise : (Fin N → Bool) → Prop  -- "complexity ≤ s_1(N)"
  noPromise : (Fin N → Bool) → Prop   -- "complexity > s_2(N)"
  yes_no_disjoint : ∀ f, yesPromise f → ¬ noPromise f

/-- Gap-MCSP with thresholds `s_1, s_2`: complexity measured by circuit size. -/
def GapMCSP (s_1 s_2 : Nat → Nat) (N : Nat) : GapPromiseProblem := { ... }

/-- Gap-MKtP: complexity measured by Kolmogorov-style time-bounded complexity. -/
def GapMKtP (s_1 s_2 : Nat → Nat) (N : Nat) : GapPromiseProblem := { ... }

/-- OPS's standard parameter regime: `s_2(N) = 2^{β·n}`, `s_1(N) = 2^{β·n} / cn`. -/
def OPS_standard_regime (β c : Nat) (N : Nat) : (Nat → Nat) × (Nat → Nat) := ...
```

### Lemmas to prove

```lean
theorem GapMCSP_thresholds_ordered (s_1 s_2 : Nat → Nat) 
    (h : ∀ n, s_1 n ≤ s_2 n) (N : Nat) :
    (GapMCSP s_1 s_2 N).thresholdOrdered = h

theorem OPS_standard_regime_log (β c : Nat) (N : Nat) (hβ : 0 < β) :
    ∃ k : Nat, (OPS_standard_regime β c N).2 N ≤ N ^ k + k
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `GapPromiseProblem` structure defined with thresholds + promise sets + disjointness.
- [ ] `GapMCSP`, `GapMKtP`, `OPS_standard_regime` all defined as concrete `def`s.
- [ ] Two basic theorems proven kernel-clean.
- [ ] Module doc-comment cites OPS 2021 §1-2 explicitly.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/OPS2021/GapProblems.lean`.
- Standard universal items.

### Forbidden
- Universal.
- ❌ No claim that Gap-MCSP is hard for any specific class.

## Output
Universal template.
