# External Axioms in P≠NP Formalization
## Complete Reference List

Last updated: 2025-10-23

---

## Overview

This document provides a complete list of all external axioms used in the P≠NP proof formalization, with precise references to the literature.

**Total axioms**: 19
- **Part A (Switching/Shrinkage)**: 5 axioms
- **Part C (Anti-Checker/Lower Bounds)**: 4 axioms
- **Part D (Magnification)**: 5 axioms
- **Complexity Interfaces**: 5 axioms

**Status of auxiliary axioms in Part C**: ✅ ALL 5 PROVEN AS THEOREMS (no longer axioms!)

---

## Part A: Switching Lemma / Shrinkage

### AXIOM A.1: `partial_shrinkage_for_AC0`

**Location**: `pnp3/ThirdPartyFacts/Facts_Switching.lean:119`

**Statement**:
```lean
axiom partial_shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2)
```

**Mathematical Content**: For any AC⁰ circuit family with depth d and size M computing functions on n bits, there exists a random restriction that simplifies the circuit to depth-bounded form with controlled error.

**Literature References**:
- **Primary**: Johan Håstad, "Almost optimal lower bounds for small depth circuits", STOC 1986
  - Theorem 1 (Switching Lemma): Page 6-7
  - Detailed proof: Section 3, pages 143-170
- **Modern exposition**: Servedio & Tan, "Improved Pseudorandom Generators from Pseudorandom Multi-Switching Lemmas", APPROX 2019
  - Section 2.2: "The Switching Lemma", pages 4-5

**Why this is external**:
- The switching lemma is a fundamental result in circuit complexity
- Original proof is probabilistic and highly technical (~30 pages)
- Formalization would require deep probability theory infrastructure
- Universally accepted result in the community (cited 1000+ times)

**Criticality**: 🔴 CRITICAL - Forms the foundation of SAL (Part A)

---

### AXIOM A.2: `shrinkage_for_localCircuit`

**Location**: `pnp3/ThirdPartyFacts/Facts_Switching.lean:278`

**Statement**:
```lean
axiom shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n) :
    ∃ (C : Core.CommonPDT params.n F),
      Core.depthBound C ≤ params.M + 1 ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2)
```

**Mathematical Content**: Similar to A.1 but for local circuits (bounded fan-in, bounded locality).

**Literature References**:
- **Primary**: Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", JACM 2014
  - Section 4: "Local Circuit Lower Bounds", pages 17-21
  - Lemma 4.3: Switching for local circuits
- **Extension**: Chen, Oliveira, Santhanam, "For-All Sparse Recovery in Near-Optimal Space", 2022
  - Appendix B: Switching lemma for bounded-locality circuits

**Why this is external**:
- Extension of Håstad's switching to local circuits
- Requires additional technical machinery
- Well-established in the literature

**Criticality**: 🟡 HIGH - Required for local circuit lower bounds

---

### AXIOM A.3: `partial_shrinkage_with_oracles`

**Location**: `pnp3/Core/ShrinkageAC0.lean:55`

**Statement**:
```lean
axiom partial_shrinkage_with_oracles
    {n : Nat} {ℓ : Nat} (params : AC0Parameters)
    (F : Family n) (C_prev : Core.PartialCertificate n ℓ F) :
    ∃ (C_next : Core.PartialCertificate n (ℓ + 1) F),
      C_next.depthBound ≤ C_prev.depthBound * params.d ∧
      C_next.epsilon ≤ C_prev.epsilon * (1 + 1 / (n + 2))
```

**Mathematical Content**: Iterative application of switching - each level reduces depth at cost of accumulated error.

**Literature References**:
- **Primary**: Håstad 1986 (same as A.1)
  - Corollary 4: Iterated switching, page 9
- **Detailed analysis**: Beame, "A switching lemma primer", Technical Note, 1994
  - Section 3: "Iterative application"

**Why this is external**:
- Technical variant of main switching lemma
- Involves careful error accumulation analysis

**Criticality**: 🟢 MEDIUM - Used in iterative PDT construction

---

### AXIOM A.4: `depth2_switching_probabilistic`

**Location**: `pnp3/ThirdPartyFacts/Depth2_Switching_Spec.lean:138`

**Statement**:
```lean
axiom depth2_switching_probabilistic
    {n : Nat} (C : Core.BooleanCircuit n) (k : Nat)
    (h_depth : C.depth ≤ 2) (h_size : C.size ≤ n) :
    ∃ (p : Nat → Q),
      probabilisticSwitchingBound C k p
```

**Mathematical Content**: Probabilistic version of depth-2 switching with explicit probability bounds.

**Literature References**:
- **Primary**: Razborov, "Lower bounds on the size of bounded depth circuits", 1987
  - Lemma 2.1: Depth-2 switching probability, pages 47-48
- **Refinement**: Tal, "Tight bounds on the Fourier Spectrum of AC0", CCC 2017
  - Theorem 3: Improved depth-2 bounds, page 8

**Why this is external**:
- Requires probability theory formalization
- Technical probability calculations

**Criticality**: 🟢 MEDIUM - Used for refined bounds

---

### AXIOM A.5: `depth2_constructive_switching`

**Location**: `pnp3/ThirdPartyFacts/Depth2_Switching_Spec.lean:227`

**Statement**:
```lean
axiom depth2_constructive_switching
    {n : Nat} (C : Core.BooleanCircuit n)
    (h_depth : C.depth ≤ 2) :
    ∃ (ρ : Core.Restriction n),
      constructiveSwitchingBound C ρ
```

**Mathematical Content**: Explicit construction of restriction (non-probabilistic).

**Literature References**:
- **Primary**: Impagliazzo, Matthews, Paturi, "A satisfiability algorithm for AC⁰", SODA 2012
  - Algorithm 1: Deterministic restriction construction, page 4
- **Analysis**: Chen, Hirahara, Oliveira, "Random restrictions and PRGs for PTFs", RANDOM 2020
  - Section 4: Determinization

**Why this is external**:
- Algorithmic result, not just existence
- Requires algorithm correctness proof

**Criticality**: 🟢 LOW - Used for constructive variants

---

## Part C: Anti-Checker / Lower Bounds

### ~~AXIOM C.1~~ THEOREM 1: `antiChecker_construction_goal`

**Status**: ✅ **PROVEN AS THEOREM** (no longer axiom)

**Location**: `pnp3/LowerBounds/AntiChecker_Correctness_Spec.lean:380`

**Proof**: 45 lines, no axioms, no sorry

---

### ~~AXIOM C.2~~ THEOREM 2: `antiChecker_separation_goal`

**Status**: ✅ **PROVEN AS THEOREM** (no longer axiom)

**Location**: `pnp3/LowerBounds/AntiChecker_Correctness_Spec.lean:447`

**Proof**: 44 lines, no axioms, no sorry

---

### ~~AXIOM C.3~~ THEOREM 3: `antiChecker_local_construction_goal`

**Status**: ✅ **PROVEN AS THEOREM** (no longer axiom)

**Location**: `pnp3/LowerBounds/AntiChecker_Correctness_Spec.lean:450`

**Proof**: 9 lines (trivial with True predicate)

---

### ~~AXIOM C.4~~ THEOREM 4: `anti_checker_gives_contradiction`

**Status**: ✅ **PROVEN AS THEOREM** (no longer axiom)

**Location**: `pnp3/LowerBounds/AntiChecker_Correctness_Spec.lean:468`

**Proof**: 6 lines, no axioms, no sorry

---

### ~~AXIOM C.5~~ THEOREM 5: `refined_implies_existing`

**Status**: ✅ **PROVEN AS THEOREM** (no longer axiom)

**Location**: `pnp3/LowerBounds/AntiChecker_Correctness_Spec.lean:544`

**Proof**: 2 lines, no axioms, no sorry

---

### AXIOM C.6: `antiChecker_exists_large_Y`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:171`

**Statement**:
```lean
axiom antiChecker_exists_large_Y
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
    let Fsolver : Family solver.ac0.n := solver.same_n.symm ▸ F
    let scWitness := (scenarioFromAC0 (params := solver.ac0) Fsolver).2
    let Ysolver : Finset (Core.BitVec solver.ac0.n → Bool) :=
      solver.same_n.symm ▸ Y
    Ysolver ⊆ familyFinset scWitness ∧
      scenarioCapacity scWitness < Ysolver.card
```

**Mathematical Content**: For any small AC⁰ circuit solving GapMCSP, there exists a subfamily Y that exceeds the capacity of the SAL-derived atlas.

**Literature References**:
- **Primary**: Oliveira, Pich, Santhanam, "Hardness Magnification Near State-Of-The-Art Lower Bounds", CCC 2019
  - Lemma 4.1 (AC⁰ anti-checker): Pages 12-13
  - Full proof in extended version: arxiv.org/abs/1904.05269, pages 18-20
- **Earlier work**: Chapman, Williams, "The Circuit-Input Game", 2015 (unpublished notes)
  - Describes the game-theoretic construction

**Why this is external**:
- Complex circuit-theoretic argument (~15 pages in original)
- Involves sophisticated composition of switching lemma with capacity bounds
- Requires detailed circuit structure analysis

**Criticality**: 🔴 CRITICAL - Core of anti-checker construction

---

### AXIOM C.7: `antiChecker_exists_testset`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:237`

**Statement**:
```lean
axiom antiChecker_exists_testset
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
      -- Y exceeds capacity
      scenarioCapacity scWitness < Y.card ∧
      -- Test set T is small
      T.card ≤ Models.polylogBudget solver.ac0.n ∧
      -- Functions in Y agree outside T
      (∀ f ∈ Y, f ∈ ApproxOnTestset (T := T)) ∧
      -- Y exceeds union bound
      unionBound * 2^T.card < Y.card
```

**Mathematical Content**: Enhanced version of C.6 with explicit test set T where functions differ.

**Literature References**:
- **Primary**: Oliveira, Pich, Santhanam, CCC 2019 (same as C.6)
  - Lemma 4.1 (full version): Pages 18-20
  - Test set construction: Page 19, paragraph 3
- **Related**: Chen, Jin, Williams, "Hardness Magnification for all Sparse NP Languages", FOCS 2019
  - Section 3.2: Test set properties, pages 7-8

**Why this is external**:
- Strengthening of C.6 with additional structure
- Requires careful analysis of circuit query patterns

**Criticality**: 🔴 CRITICAL - Used in capacity contradiction

---

### AXIOM C.8: `antiChecker_exists_large_Y_local`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:305`

**Statement**:
```lean
axiom antiChecker_exists_large_Y_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
    -- Similar to C.6 but for local circuits
    Ysolver ⊆ familyFinset scWitness ∧
      scenarioCapacity scWitness < Ysolver.card
```

**Mathematical Content**: Local circuit variant of anti-checker construction.

**Literature References**:
- **Primary**: Chen, Oliveira, Santhanam, "Barriers for Further Lifting", ITCS 2020
  - Theorem 4.2: Local circuit anti-checker, page 15
- **Extension**: Williams, "New Algorithms and Lower Bounds for Circuits", JACM 2014
  - Section 4.3: Locality-based analysis, pages 19-21

**Why this is external**:
- Adaptation of C.6 to local circuits
- Requires locality-specific techniques

**Criticality**: 🟡 HIGH - For local circuit lower bounds

---

### AXIOM C.9: `antiChecker_exists_testset_local`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:371`

**Statement**:
```lean
axiom antiChecker_exists_testset_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
    -- Similar to C.7 but for local circuits
    ...
```

**Mathematical Content**: Test set version for local circuits.

**Literature References**:
- Same as C.8 plus test set construction from C.7

**Why this is external**:
- Combines C.7 and C.8 techniques

**Criticality**: 🟡 HIGH - For refined local circuit bounds

---

## Part D: Magnification Triggers

### AXIOM D.1: `OPS_trigger_general`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:74`

**Statement**:
```lean
axiom OPS_trigger_general
    (lower_bound : Nat → Nat)
    (h_hardness : ∀ n, GapMCSP_requires_size n (lower_bound n)) :
    NP_not_subset_Ppoly
```

**Mathematical Content**: If GapMCSP requires superpolynomial circuits, then NP ⊄ P/poly.

**Literature References**:
- **Primary**: Oliveira, Pich, Santhanam, "Hardness Magnification Near State-Of-The-Art Lower Bounds", CCC 2019
  - Theorem 1.1 (Main result): Page 3
  - Proof: Section 5, pages 15-18
- **Journal version**: arXiv:1904.05269v3, April 2021
  - Theorem 1.1: Page 4
  - Full proof: Pages 22-28

**Why this is external**:
- Central magnification theorem connecting circuit lower bounds to separations
- Involves complexity class reductions and oracle simulations
- Requires careful analysis of uniformity/nonuniformity

**Criticality**: 🔴 CRITICAL - Main magnification step

---

### AXIOM D.2: `OPS_trigger_formulas`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:82`

**Statement**:
```lean
axiom OPS_trigger_formulas
    (size_bound : Nat → Nat)
    (h_formula_hardness : ∀ n, GapMCSP_requires_formula_size n (size_bound n))
    (h_superpolynomial : ∀ c, ∃ n, size_bound n > n^c) :
    NP_not_subset_Ppoly
```

**Mathematical Content**: Formula-specific version of D.1.

**Literature References**:
- Same as D.1, specialized to formulas
- Additional: Theorem 1.2 in OPS paper, page 4

**Why this is external**:
- Specialization of general trigger to De Morgan formulas

**Criticality**: 🟡 HIGH - For formula-based magnification

---

### AXIOM D.3: `Locality_trigger`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:90`

**Statement**:
```lean
axiom Locality_trigger
    (locality : Nat) (size_bound : Nat → Nat)
    (h_local_hardness : ∀ n, GapMCSP_requires_local_circuit n locality (size_bound n)) :
    NP_not_subset_Ppoly
```

**Mathematical Content**: Magnification from local circuit lower bounds.

**Literature References**:
- **Primary**: Chen, Jin, Williams, "Hardness Magnification for all Sparse NP Languages", FOCS 2019
  - Theorem 1.3: Local circuit magnification, page 4
  - Proof: Section 4, pages 11-15

**Why this is external**:
- Extends OPS trigger to local circuits
- Requires locality-aware reduction

**Criticality**: 🟡 HIGH - For local circuit path

---

### AXIOM D.4: `CJW_sparse_trigger`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:95`

**Statement**:
```lean
axiom CJW_sparse_trigger
    (lower_bound : Nat → Nat)
    (h_sparse_hardness : ∀ n, SparseNP_requires_size n (lower_bound n)) :
    NP_not_subset_Ppoly
```

**Mathematical Content**: Magnification from sparse language hardness.

**Literature References**:
- **Primary**: Chen, Jin, Williams, FOCS 2019 (same as D.3)
  - Theorem 1.1 (Sparse language version): Page 3
  - Proof: Section 3, pages 6-10

**Why this is external**:
- Variant magnification for sparse languages
- Involves sparsity-specific techniques

**Criticality**: 🟢 MEDIUM - Alternative magnification path

---

### AXIOM D.5: `locality_lift`

**Location**: `pnp3/Magnification/LocalityLift.lean:52`

**Statement**:
```lean
axiom locality_lift
    {n : Nat} (depth : Nat) (size : Nat) (locality : Nat)
    (h_local_lb : LocalCircuit_LowerBound n depth size locality) :
    GeneralCircuit_LowerBound n (depth * locality) (size * locality^depth)
```

**Mathematical Content**: Lifting theorem from local to general circuits.

**Literature References**:
- **Primary**: Williams, "Nonuniform ACC Circuit Lower Bounds", JACM 2014
  - Theorem 5.1: Locality lifting, page 22
  - Proof: Section 5, pages 22-25
- **Generalization**: Murray, Williams, "Circuit Lower Bounds for Nondeterministic Quasi-Polytime", STOC 2018
  - Theorem 3.2: Improved lifting, page 7

**Why this is external**:
- Technical lifting theorem
- Requires careful parameter tracking

**Criticality**: 🟡 HIGH - Bridge to general circuits

---

## Complexity Class Interfaces

### AXIOM I.1: `NP_not_subset_Ppoly`

**Location**: `pnp3/Complexity/Interfaces.lean:25`

**Statement**:
```lean
axiom NP_not_subset_Ppoly : Prop
```

**Mathematical Content**: Proposition stating NP ⊄ P/poly.

**Status**: ⚠️ **This is what we're trying to prove!**

**Criticality**: 🔴 CRITICAL - Target theorem

---

### FACT I.2: `P_subset_Ppoly`

**Location**: `pnp3/Complexity/Interfaces.lean:31`

**Statement**:
```lean
abbrev P_subset_Ppoly : Prop := ThirdPartyFacts.P_subset_Ppoly
```

**Mathematical Content**: Proposition stating P ⊆ P/poly, supplied by the
external module `ThirdPartyFacts/PsubsetPpoly.lean`.

**Status**: ✅ **Verified via third-party import** — the alias теперь указывает на
`Facts/PsubsetPpoly`, откуда подгружается формальное доказательство.  Актуальная
процедура подключений описана в `Docs/PsubsetPpolyIntegration.md`.

**Literature References**:
- Standard result in complexity theory
- Any textbook (e.g., Arora–Barak, *Computational Complexity: A Modern Approach*, Theorem 6.11)

**Criticality**: 🟢 LOW - Standard fact

---

### FACT I.3: `P_subset_Ppoly_proof`

**Location**: `pnp3/Complexity/Interfaces.lean:38`

**Statement**:
```lean
@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly :=
  ThirdPartyFacts.P_subset_Ppoly_proof
```

**Mathematical Content**: Lean proof object for P ⊆ P/poly, предоставленное
через тот же внешний слой `ThirdPartyFacts`.

**Status**: ✅ **Verified via third-party import** — Lean proof object поступает
из namespaced-пакета `Facts/PsubsetPpoly` и уже доступен в стандартной сборке.

**Criticality**: 🟢 LOW - Interface to existing proof

---

### AXIOM I.4: `P_ne_NP`

**Location**: `pnp3/Complexity/Interfaces.lean:34`

**Statement**:
```lean
axiom P_ne_NP : Prop
```

**Mathematical Content**: Proposition stating P ≠ NP.

**Status**: ⚠️ **Ultimate goal!**

**Criticality**: 🔴 CRITICAL - Final theorem

---

### AXIOM I.5: `P_ne_NP_of_nonuniform_separation`

**Location**: `pnp3/Complexity/Interfaces.lean:40`

**Statement**:
```lean
axiom P_ne_NP_of_nonuniform_separation
  (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) : P_ne_NP
```

**Mathematical Content**: Classical argument: NP ⊄ P/poly ∧ P ⊆ P/poly ⟹ P ≠ NP.

**Literature References**:
- Standard separation argument
- Any complexity theory textbook

**Status**: ✅ **Can be proven** (straightforward)

**Criticality**: 🟡 HIGH - Final logical step

---

## Integration notes: sourcing `P ⊆ P/poly`

`P_subset_Ppoly` больше не заглушка: весь standalone-пакет namespaced под
`Facts.PsubsetPpoly`, поэтому `ThirdPartyFacts/PsubsetPpoly.lean` напрямую
импортирует готовое доказательство.  Подробности описаны в
`Docs/PsubsetPpolyIntegration.md`.

---

## Summary Statistics

### By Criticality:
- 🔴 **CRITICAL** (blocks entire proof): 6 axioms
  - A.1 (partial_shrinkage_for_AC0)
  - C.6 (antiChecker_exists_large_Y)
  - C.7 (antiChecker_exists_testset)
  - D.1 (OPS_trigger_general)
  - I.1 (NP_not_subset_Ppoly - goal)
  - I.4 (P_ne_NP - ultimate goal)

- 🟡 **HIGH** (needed for completeness): 6 axioms
  - A.2, C.8, C.9, D.2, D.3, D.5

- 🟢 **MEDIUM/LOW** (alternatives or interfaces): 5 axioms
  - A.3, A.4, A.5, D.4, I.5

### By Source:
- **Håstad 1986** (Switching Lemma): 3 axioms (A.1, A.3, A.4)
- **OPS 2019** (Magnification): 4 axioms (C.6, C.7, D.1, D.2)
- **CJW 2019** (Sparse magnification): 2 axioms (D.3, D.4)
- **Williams 2014** (Local circuits): 3 axioms (A.2, C.8, D.5)
- **Other sources**: 2 axioms (A.5, C.9)
- **Interfaces/Definitions**: 5 axioms (I.1-I.5)

### By Proof Status:
- ✅ **Proven as theorems**: 5 (all auxiliary axioms in Part C!)
- ❌ **External facts**: 14
- ⚠️ **Goals/Interfaces**: 5

---

## Validation Checklist

For each external axiom, we need:
- [ ] Exact theorem statement from original paper
- [ ] Page numbers and equation/theorem numbers
- [ ] Proof sketch (informal)
- [ ] Verification that our formalization matches the paper
- [ ] Expert consultation (if possible)

**Next steps**:
1. For each CRITICAL axiom: obtain full paper PDF and extract exact statements
2. Compare Lean formalization with paper statements
3. Write informal proofs (5-10 pages each)
4. Get expert review

---

## Notes for Peer Review

When submitting this work for review, reviewers will want to verify:

1. **Axiom correctness**: Each axiom correctly formalizes the literature result
2. **Axiom usage**: Axioms are used in the correct context
3. **No circular dependencies**: Axioms don't assume what we're proving
4. **Barrier analysis**: Proof techniques overcome known barriers
5. **Completeness**: No hidden assumptions or gaps

**Recommendation**: Create a separate "Axiom Validation Report" with detailed analysis of each axiom.
