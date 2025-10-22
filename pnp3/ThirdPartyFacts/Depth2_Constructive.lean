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
      ℓ = 0 ∧
      C.depthBound = 1 ∧
      C.epsilon = 0 := by
  intro f F
  sorry  -- Similar to positive literal, selectors = [restrictToFalse n i]

/-! ### Single term case (AND of literals) -/

/--
Create a subcube that restricts multiple variables according to a pattern.
For each (i, b) pair, restricts variable i to value b.
-/
def restrictToPattern (n : Nat) (pattern : List (Fin n × Bool)) : Subcube n :=
  fun j =>
    match pattern.find? (fun p => p.1 == j) with
    | some (_, b) => some b
    | none => none

/--
A single term (AND of positive literals): f(x) = x[i₁] ∧ x[i₂] ∧ ... ∧ x[iₖ]

Example: singleTerm n [i, j, k] = fun x => x[i] && x[j] && x[k]
-/
def singleTerm (n : Nat) (indices : List (Fin n)) : Core.BitVec n → Bool :=
  fun x => indices.all (fun i => x i)

/--
Helper: create subcube where all listed variables are set to true.
-/
def restrictAllToTrue (n : Nat) (indices : List (Fin n)) : Subcube n :=
  restrictToPattern n (indices.map (fun i => (i, true)))

/--
Build PDT for AND term by sequential branching.

For indices = [i₁, i₂, ..., iₖ]:
- Branch on i₁:
  - Left (false): leaf with i₁=false
  - Right (true): recursively build for [i₂, ..., iₖ]
-/
def buildAndPDT (n : Nat) : List (Fin n) → PDT n
  | [] => PDT.leaf (fullSubcube n)  -- Empty AND = true everywhere
  | [i] => PDT.node i (PDT.leaf (restrictToFalse n i)) (PDT.leaf (restrictToTrue n i))
  | i :: rest =>
      PDT.node i
        (PDT.leaf (restrictToFalse n i))  -- If x[i]=false, AND is false
        (buildAndPDT n rest)               -- If x[i]=true, continue with rest

/--
Depth of AND PDT equals the length of the indices list.
-/
lemma depth_buildAndPDT {n : Nat} (indices : List (Fin n)) :
    PDT.depth (buildAndPDT n indices) = indices.length := by
  induction indices with
  | nil => simp [buildAndPDT, PDT.depth]
  | cons i rest ih =>
    cases rest with
    | nil => simp [buildAndPDT, PDT.depth]
    | cons j rest' =>
      simp [buildAndPDT, PDT.depth, ih]
      sorry  -- Need to show depth of node is 1 + depth of right child

/--
Direct definition: subcube with both i and j set to true.
This is simpler than using restrictToPattern for proofs.
-/
def restrictBothToTrue (n : Nat) (i j : Fin n) : Subcube n :=
  fun k => if k = i ∨ k = j then some true else none

/--
Lemma: memB for subcube with both variables true.
-/
lemma memB_restrictBothToTrue {n : Nat} (i j : Fin n) (h_ne : i ≠ j) (x : Core.BitVec n) :
    memB (restrictBothToTrue n i j) x = (x i && x j) := by
  unfold memB restrictBothToTrue
  simp [List.all_iff_forall]
  constructor
  · intro h
    have hi := h i (List.mem_finRange _)
    have hj := h j (List.mem_finRange _)
    simp at hi hj
    exact ⟨hi, hj⟩
  · intro ⟨hi, hj⟩ k _
    by_cases hk : k = i ∨ k = j
    · cases hk with
      | inl hki => subst hki; simp [hi]
      | inr hkj => subst hkj; simp [hj]
    · simp [hk]

/--
Lemma: A point x is in restrictAllToTrue iff all indexed variables are true.
-/
lemma memB_restrictAllToTrue {n : Nat} (indices : List (Fin n)) (x : Core.BitVec n) :
    memB (restrictAllToTrue n indices) x = indices.all (fun i => x i) := by
  unfold memB restrictAllToTrue restrictToPattern
  sorry  -- Need to prove equivalence of checking pattern matches

/--
**Theorem**: Single term (AND) has shrinkage with trunk depth = |indices|.

**Construction**:
- For f(x) = x[i₁] ∧ x[i₂] ∧ ... ∧ x[iₖ]
- Build PDT by sequentially branching on each variable
- Depth = k (number of variables in the term)
- Selectors = [subcube where all variables are true]
- Error = 0 (perfect coverage)

**Example**: f(x) = x[0] ∧ x[1]
- Tree: branch on x[0], then on x[1]
- Depth = 2
- Selectors = [subcube with x[0]=true, x[1]=true]
-/
/--
Special case: Single term with 2 variables x[i] ∧ x[j].
This is easier to prove directly before generalizing.
-/
theorem partial_shrinkage_single_term_two {n : Nat} (i j : Fin n) (h_ne : i ≠ j) :
    let f : Core.BitVec n → Bool := fun x => x i && x j
    let F : Family n := [f]
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ F),
      ℓ = 0 ∧
      C.depthBound = 2 ∧
      C.epsilon = 0 := by
  intro f F
  -- Build tree: branch on i, then on j
  let β_i_false := restrictToFalse n i
  let β_j_false := restrictToFalse n j
  let β_both_true := restrictBothToTrue n i j

  -- Inner tree (for when x[i]=true): branch on j
  let inner_tree := PDT.node j
    (PDT.leaf β_j_false)
    (PDT.leaf β_both_true)

  -- Outer tree: branch on i
  let tree := PDT.node i
    (PDT.leaf β_i_false)
    inner_tree

  have h_depth : PDT.depth tree = 2 := by
    unfold tree inner_tree
    simp [PDT.depth]
    -- depth (node i (leaf _) (node j (leaf _) (leaf _)))
    -- = 1 + max (depth (leaf _)) (depth (node j ...))
    -- = 1 + max 0 (1 + max 0 0)
    -- = 1 + max 0 1 = 1 + 1 = 2
    rfl

  refine ⟨0, {
    witness := PartialDT.ofPDT tree
    depthBound := 2
    epsilon := 0
    trunk_depth_le := by
      simp [PartialDT.ofPDT]
      exact Nat.le_of_eq h_depth
    selectors := fun g => if g = f then [β_both_true] else []
    selectors_sub := by
      intro g γ hg hγ
      simp [F] at hg
      subst hg
      simp at hγ
      cases hγ  -- γ = β_both_true
      rw [PartialDT.realize_ofPDT]
      -- Show β_both_true ∈ PDT.leaves tree
      -- tree = node i (leaf β_i_false) (node j (leaf β_j_false) (leaf β_both_true))
      -- leaves tree = [β_i_false, β_j_false, β_both_true]
      unfold tree inner_tree
      simp [PDT.leaves]
      right; right; rfl
    err_le := by
      intro g hg
      simp [F] at hg
      subst hg
      simp
      apply le_of_eq
      apply errU_eq_zero_of_agree
      intro x
      -- Show: f x = coveredB [β_both_true] x
      -- f x = x i && x j
      -- coveredB [β_both_true] x = memB β_both_true x
      -- β_both_true restricts both i and j to true
      simp [f, coveredB, β_both_true]
      rw [memB_restrictBothToTrue _ _ _ h_ne]
      -- Now both sides are x i && x j
      rfl
  }, rfl, rfl, rfl⟩

theorem partial_shrinkage_single_term {n : Nat} (indices : List (Fin n))
    (h_nodup : indices.Nodup) :
    let f : Core.BitVec n → Bool := singleTerm n indices
    let F : Family n := [f]
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ F),
      ℓ = 0 ∧
      C.depthBound = indices.length ∧
      C.epsilon = 0 := by
  intro f F
  sorry  -- Will use buildAndPDT with induction on indices.length

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
