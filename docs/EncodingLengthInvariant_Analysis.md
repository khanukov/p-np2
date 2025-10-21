# Analysis: Encoding Length Invariant (Critical Issue)

**Date:** 2025-10-21
**File:** `pnp3/ThirdPartyFacts/SwitchingLemma.lean:474`
**Status:** ⚠️ **CRITICAL MATHEMATICAL GAP**

## Executive Summary

The barcode encoding algorithm in `encodeRestriction` has a **critical unproven property**: it assumes that `buildSteps ρ t` returns a list of exactly length `t`, but this is currently stated with `sorry` (line 474). This is not a minor technical detail—it's a fundamental requirement for the switching lemma proof to work.

**If this property does not hold, the entire barcode injection method fails, and the switching lemma proof is invalid.**

---

## The Problem

### Current Code (Line 408-474)

```lean
noncomputable def encodeRestriction (F : DNF n) (k t : Nat)
    (ρ : Restriction n)
    (hbad : ∃ tree : PDT n, tree.depth ≥ t ∧
             ∀ x, Core.mem ρ x → DNF.eval F x = true) :
    Barcode n t :=
  let rec buildSteps (ρ_current : Restriction n) (steps_left : Nat) :
      List (BarcodeStep n) :=
    match steps_left with
    | 0 => []
    | s + 1 =>
        match firstAliveTerm? F ρ_current with
        | none => []  -- ⚠️ RETURNS EMPTY!
        | some termIdx =>
            match getTerm? F termIdx with
            | none => []  -- ⚠️ RETURNS EMPTY!
            | some T =>
                match firstUnassignedLit? T ρ_current with
                | none => []  -- ⚠️ RETURNS EMPTY!
                | some (litIdx, ℓ) =>
                    let falsifyingVal := !ℓ.val
                    let step : BarcodeStep n :=
                      { termIdx := termIdx
                      , litIdx := litIdx
                      , val := falsifyingVal }
                    let ρ_next := setVar ρ_current ℓ.idx falsifyingVal
                    step :: buildSteps ρ_next s

  let steps := buildSteps ρ t
  ⟨steps, by sorry⟩  -- ⚠️ Need proof: steps.length = t
```

### The Issue

The algorithm has **three exit points** where it returns `[]` (empty list):

1. **Line 419**: No alive term found → `none => []`
2. **Line 423**: Term lookup fails → `none => []`
3. **Line 427**: No unassigned literal → `none => []`

If any of these cases occur before `t` steps are completed, then:
- `buildSteps ρ t` returns a list of length < t
- The subtype construction `Barcode n t := { steps : List _ // steps.length = t }` **fails**
- The entire encoding is undefined!

---

## What Needs to Be Proven

### The Length Invariant Lemma

```lean
lemma buildSteps_length (F : DNF n) (ρ : Restriction n) (t : Nat)
    (hbad : ∃ tree : PDT n, tree.depth ≥ t ∧
             ∀ x, Core.mem ρ x → DNF.eval F x = true) :
    (buildSteps F ρ t).length = t
```

### What This Requires

This lemma requires proving that **at each step i < t**:
- There exists at least one **alive term** in F under ρ_i
- That term has at least one **unassigned literal** under ρ_i

Where ρ_i is the restriction after i encoding steps.

---

## The Logical Chain (What Should Work)

From switching lemma theory, the following logical chain should hold:

### 1. Base Case: DT ≥ 1 implies alive term exists

```lean
lemma DT_ge_one_implies_alive (F : DNF n) (ρ : Restriction n)
    (h : DT(F|ρ) ≥ 1) :
    ∃ termIdx, firstAliveTerm? F ρ = some termIdx
```

**Intuition:** If the decision tree has depth ≥ 1, the formula is not decided yet on subcube ρ. Therefore:
- Not all terms are killed (else formula = false, DT = 0)
- No term is satisfied (else formula = true, DT = 0)
- So at least one term must be **alive**

**Status:** Has `sorry` at line 173

---

### 2. Recursive Case: DT decreases after encoding step

```lean
lemma DT_decreases_after_step (F : DNF n) (ρ : Restriction n) (t : Nat)
    (h : DT(F|ρ) ≥ t+1)
    (step : BarcodeStep n)
    (ρ' : Restriction n := setVar ρ step_var step_val) :
    DT(F|ρ') ≥ t
```

**Intuition:** Each encoding step:
- Picks an alive term T
- Falsifies one literal in T (killing that term)
- Reduces the decision tree depth by at least 1

**Status:** Not formalized yet

---

### 3. Composition: Induction on t

By induction on t:
- **Base:** t = 0 → buildSteps returns `[]` → length 0 ✓
- **Step:** If DT(F|ρ) ≥ t+1:
  - By (1): ∃ alive term → buildSteps makes first step
  - By (2): DT(F|ρ') ≥ t after first step
  - By IH: buildSteps ρ' t has length t
  - Therefore: buildSteps ρ (t+1) has length t+1 ✓

**Status:** Requires (1) and (2) to be proven first

---

## The Hypothesis Problem

### Current Hypothesis

```lean
hbad : ∃ tree : PDT n, tree.depth ≥ t ∧
        ∀ x, Core.mem ρ x → DNF.eval F x = true
```

### Issues with Current Formulation

1. **"There exists A tree with depth ≥ t"**
   - This doesn't say the tree COMPUTES F|ρ
   - Could be any random tree!
   - Should say: "the MINIMUM tree computing F|ρ has depth ≥ t"

2. **"F evaluates to true everywhere on ρ"**
   - If F|ρ ≡ true (constant function), then DT = 0 (just return true)
   - This contradicts depth ≥ t for t > 0!
   - Unclear what this condition is trying to capture

### What the Hypothesis Should Be

Based on switching lemma literature, it should capture:

```lean
-- The decision tree complexity of F restricted to ρ is at least t
def DT_complexity (F : DNF n) (ρ : Restriction n) (t : Nat) : Prop :=
  ∀ (tree : PDT n),
    (∀ x, Core.mem ρ x → tree_computes F x tree) →
    tree.depth ≥ t
```

Or more directly:
```lean
-- At each step i < t, we can make progress
def can_encode_t_steps (F : DNF n) (ρ : Restriction n) (t : Nat) : Prop :=
  ∀ i < t,
    let ρ_i := (apply i encoding steps to ρ)
    firstAliveTerm? F ρ_i ≠ none
```

---

## Possible Approaches to Fix

### Option 1: Prove the Lemma (Correct Approach)

**Requirements:**
1. Define decision tree complexity formally for DNF
2. Prove `DT_ge_one_implies_alive` (line 173)
3. Prove `DT_decreases_after_step`
4. Prove length invariant by induction

**Effort:** 2-5 days of focused proof work
**Risk:** Medium - requires reasoning about decision trees
**Value:** Mathematically complete proof

---

### Option 2: Refactor the Algorithm

Change `encodeRestriction` to use a **dependent type**:

```lean
-- Return the list AND a proof that encoding succeeded for t steps
def encodeRestrictionSafe (F : DNF n) (ρ : Restriction n) (t : Nat) :
    Option (Σ' (steps : List (BarcodeStep n)), steps.length = t) :=
  -- Try to build t steps, return None if failed
  ...
```

Then in switching lemma:
```lean
-- Only count restrictions where encoding succeeded
match encodeRestrictionSafe F ρ t with
| some barcode => count it
| none => skip (formula was decided before t steps)
```

**Effort:** 1-2 days
**Risk:** Low - just refactoring
**Value:** Makes the gap explicit, doesn't prove correctness

---

### Option 3: Test with Concrete Examples

Create specific test cases to check if algorithm works:

```lean
-- Test: Simple formula that should allow t steps
example :
  let F := (x₁ ∧ x₂ ∧ x₃) ∨ (x₄ ∧ x₅ ∧ x₆)  -- 2 terms, width 3
  let ρ := fun i => none                       -- Empty restriction
  let t := 2
  let steps := buildSteps F ρ t
  steps.length = 2 := by
  -- Try to prove this concretely
  sorry
```

**Effort:** 1 day
**Risk:** Low - just testing
**Value:** Builds confidence, might find bugs

---

## Impact on Step A Completeness

### Without This Proof

The barcode injection method is **incomplete**:
- We cannot establish the injection `B_t → Barcodes`
- The counting argument `Pr[DT ≥ t] ≤ (5pk)^t` is unproven
- **Switching lemma is unproven**
- **Step A is incomplete**

### With This Proof

The barcode method works:
- ✓ Injection is valid
- ✓ Counting argument goes through
- ✓ Switching lemma proven (modulo probability theory)
- ✓ Step A mathematically complete (modulo external facts)

---

## Related Unproven Lemmas

These lemmas are needed to support the length invariant proof:

### 1. `firstAliveTerm?_some_of_DT_ge_one` (Line 173)

```lean
lemma firstAliveTerm?_some_of_DT_ge_one (F : DNF n) (ρ : Restriction n)
    (h : ∃ t : PDT n, t.depth ≥ 1 ∧ ∀ x, Core.mem ρ x → DNF.eval F x = true) :
    firstAliveTerm? F ρ ≠ none := by
  sorry
```

**What it claims:** If depth ≥ 1, there's an alive term
**Why blocked:** Need to formalize DT-DNF relationship
**Effort:** 1-2 days

---

### 2. `firstAliveTerm?_some_alive` (Line 167)

```lean
lemma firstAliveTerm?_some_alive (F : DNF n) (ρ : Restriction n) (idx : Nat)
    (h : firstAliveTerm? F ρ = some idx) :
    ∃ T, getTerm? F idx = some T ∧ TermStatus.ofTerm T ρ = TermStatus.alive := by
  sorry  -- Need lemma about List.findIdx?
```

**What it claims:** If `findIdx?` returns `some idx`, the element at idx satisfies the predicate
**Why blocked:** Need `List.findIdx?` API lemma from Mathlib
**Effort:** 1 hour (should exist in library)

---

## Recommendations

### Immediate (This Week)

1. **Test the algorithm** with concrete examples
   - Manually construct small DNF formulas
   - Verify buildSteps returns correct length
   - Look for counterexamples

2. **Clarify the hypothesis** `hbad`
   - What does it really mean?
   - Is the current formulation correct?
   - Consult switching lemma references

### Short-term (1-2 Weeks)

3. **Prove base case** `DT_ge_one_implies_alive`
   - Formalize decision tree semantics for DNF
   - Prove contrapositive: if no alive term, then DT = 0

4. **Prove or find** `List.findIdx?` properties in Mathlib

### Medium-term (2-4 Weeks)

5. **Prove length invariant** by induction
   - Use base case + recursive case
   - Complete the sorry at line 474

6. **Or refactor** if proof is too difficult
   - Use Option type approach
   - Make gaps explicit

---

## Conclusion

The encoding length invariant is **the most critical mathematical gap** in Step A. Without it:
- The barcode injection method is incomplete
- The switching lemma cannot be proven
- Step A cannot be considered complete

**Action Required:** Either prove this lemma or find a counterexample showing the algorithm fails. This is not optional for mathematical completeness.

**Estimated Effort:** 2-5 days for proof, or 1-2 days for refactor + tests

**Priority:** ⚠️ **HIGHEST - This blocks Step A completion**
