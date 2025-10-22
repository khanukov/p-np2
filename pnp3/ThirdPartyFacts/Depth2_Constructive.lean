import Core.BooleanBasics
import Core.PDT
import Core.PDTSugar
import Core.ShrinkageWitness
import ThirdPartyFacts.Facts_Switching
import ThirdPartyFacts.ConstructiveSwitching

/-!
  pnp3/ThirdPartyFacts/Depth2_Constructive.lean

  Constructive proofs for depth-2 switching lemma in simple cases.

  This module builds upon ConstructiveSwitching.lean (empty family and constants)
  to handle simple depth-2 formulas:
  - Single literals: x₁, ¬x₁
  - Single clauses (OR): x₁ ∨ x₂ ∨ ... ∨ xₖ
  - Single terms (AND): x₁ ∧ x₂ ∧ ... ∧ xₖ

  **Goal**: Demonstrate that the constructive approach scales to non-trivial
  depth-2 cases, validating the formalization before tackling general switching.

  **Strategy**:
  1. For single literals: PDT with depth 1
  2. For single clauses: PDT that fixes variables in the clause
  3. For single terms: similar approach

  **Why This Matters**:
  - Shows constructive approach works beyond trivial cases
  - Provides test cases for full depth-2 proof
  - Validates numerical bounds match theory
-/

namespace Pnp3
namespace ThirdPartyFacts
namespace Depth2Constructive

open Core
open ConstructiveSwitching

/-! ### Helper functions for subcube restrictions -/

/--
Create a subcube that restricts variable i to false.
All other variables remain free (none).
-/
def restrictToFalse (n : Nat) (i : Fin n) : Subcube n :=
  fun j => if j = i then some false else none

/--
Create a subcube that restricts variable i to true.
All other variables remain free (none).
-/
def restrictToTrue (n : Nat) (i : Fin n) : Subcube n :=
  fun j => if j = i then some true else none

/--
The "full" subcube - all variables free.
-/
def fullSubcube (n : Nat) : Subcube n :=
  fun _ => none

/-! ### Lemmas about memB and restrictions -/

/--
A point x is in restrictToFalse n i iff x i = false.
-/
lemma memB_restrictToFalse {n : Nat} (i : Fin n) (x : Core.BitVec n) :
    memB (restrictToFalse n i) x = (x i == false) := by
  unfold memB restrictToFalse
  simp [List.all_iff_forall]
  constructor
  · intro h
    specialize h i (List.mem_finRange _)
    simp at h
    exact h
  · intro hi j _
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]

/--
A point x is in restrictToTrue n i iff x i = true.
-/
lemma memB_restrictToTrue {n : Nat} (i : Fin n) (x : Core.BitVec n) :
    memB (restrictToTrue n i) x = (x i == true) := by
  unfold memB restrictToTrue
  simp [List.all_iff_forall]
  constructor
  · intro h
    specialize h i (List.mem_finRange _)
    simp at h
    exact h
  · intro hi j _
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]

/-! ### Single literal case -/

/--
A single positive literal: f(x) = xᵢ for some index i.
This is the simplest non-constant function.
-/
def singleLiteral (n : Nat) (i : Fin n) : Core.BitVec n → Bool :=
  fun x => x i

/--
**Theorem**: Single literal has simple shrinkage with trunk depth 1.

**Construction**:
- Create PDT with one branch on variable i
- Left child (xᵢ=false): leaf with restrictToFalse
- Right child (xᵢ=true): leaf with restrictToTrue
- This perfectly represents the function with depth 1, error 0

**Note**: ℓ is the tail depth bound (0 for exact representation),
depthBound is the trunk depth (1 for single branch).
-/
theorem partial_shrinkage_single_literal {n : Nat} (i : Fin n) :
    let f : Core.BitVec n → Bool := singleLiteral n i
    let F : Family n := [f]
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ F),
      ℓ = 0 ∧
      C.depthBound = 1 ∧
      C.epsilon = 0 := by
  intro f F
  -- Build a PDT that branches on variable i:
  -- - Left child (i=false): leaf with restrictToFalse
  -- - Right child (i=true): leaf with restrictToTrue
  let β_false := restrictToFalse n i
  let β_true := restrictToTrue n i
  let tree := PDT.node i (PDT.leaf β_false) (PDT.leaf β_true)

  -- This tree has depth 1 (one branch)
  have h_depth : PDT.depth tree = 1 := by
    simp [tree, PDT.depth]

  -- Key insight: selectors should only include subcubes where f evaluates to true
  -- For f(x) = x[i], this is only when x[i] = true, so selectors = [β_true]
  refine ⟨0, {
    witness := PartialDT.ofPDT tree
    depthBound := 1
    epsilon := 0
    trunk_depth_le := by
      simp [PartialDT.ofPDT]
      exact Nat.le_of_eq h_depth
    selectors := fun g => if g = f then [β_true] else []
    selectors_sub := by
      intro g γ hg hγ
      simp [F] at hg
      subst hg
      simp at hγ
      -- γ ∈ [β_true], so γ = β_true
      cases hγ
      -- Need to show β_true ∈ PDT.leaves tree = [β_false, β_true]
      rw [PartialDT.realize_ofPDT]
      have : PDT.leaves tree = [β_false, β_true] := by
        simp [tree]
      rw [this]
      right; rfl
    err_le := by
      intro g hg
      simp [F] at hg
      subst hg
      -- Show errU f [β_true] ≤ 0
      simp
      -- Use errU_eq_zero_of_agree: if f x = coveredB [β_true] x for all x, then errU = 0
      apply le_of_eq
      apply errU_eq_zero_of_agree
      intro x
      -- Need: f x = coveredB [β_true] x
      -- f x = x i (by definition of singleLiteral)
      -- coveredB [β_true] x = memB (restrictToTrue n i) x = (x i == true)
      simp [f, singleLiteral, β_true, coveredB]
      rw [memB_restrictToTrue]
      -- Now need: x i = (x i == true)
      cases x i <;> simp
  }, rfl, rfl, rfl⟩

/--
A single negative literal: f(x) = ¬xᵢ for some index i.
-/
def singleNegLiteral (n : Nat) (i : Fin n) : Core.BitVec n → Bool :=
  fun x => !(x i)

theorem partial_shrinkage_single_neg_literal {n : Nat} (i : Fin n) :
    let f : Core.BitVec n → Bool := singleNegLiteral n i
    let F : Family n := [f]
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ F),
      ℓ = 1 ∧
      C.depthBound = 1 ∧
      C.epsilon = 0 := by
  intro f F
  sorry  -- Similar to positive literal

/-! ### Single clause case (OR of literals) -/

/--
A single clause (OR of k literals) on n variables.
Represented as a list of (index, polarity) pairs.
-/
structure SingleClause (n : Nat) where
  literals : List (Fin n × Bool)  -- (variable index, is_positive)
  deriving Repr

/--
Evaluate a single clause on an assignment.
-/
def evalClause {n : Nat} (clause : SingleClause n) (x : Core.BitVec n) : Bool :=
  clause.literals.any fun (i, pos) => if pos then x i else !(x i)

/-! ### Documentation and next steps -/

/-
**Current Status**:
- Specifications for single literals and clauses defined
- Structure in place for constructive proofs
- Main theorems have `sorry` placeholders

**Required for Completion**:
1. **PDT Branching Constructor**: Need to extend PDT.lean with:
   ```lean
   | branch (i : Fin n) (left right : PDT n) : PDT n
   ```
   This allows explicit decision trees, not just leaves.

2. **Subcube Operations**: Need helpers to restrict subcubes:
   - `restrictToTrue : Subcube n → Fin n → Subcube n`
   - `restrictToFalse : Subcube n → Fin n → Subcube n`

3. **Error Computation**: For single literals, show that:
   - Branching tree perfectly represents the function
   - errU = 0 (no approximation error)

4. **Integration**: Once these are proven, they can replace part of
   `partial_shrinkage_for_AC0` for the d=2, k=1 case.

**Estimated Effort**:
- PDT branching: 1-2 days (extend existing PDT infrastructure)
- Single literal proofs: 2-3 days (adapt ConstructiveSwitching approach)
- Single clause proofs: 1 week (more complex, need induction)
- Total: ~2 weeks for this module

**Impact**:
- Demonstrates constructive approach works for non-trivial cases
- Provides concrete examples for testing
- Reduces axiom surface area from "all depth-2" to "complex depth-2"
-/

end Depth2Constructive
end ThirdPartyFacts
end Pnp3
