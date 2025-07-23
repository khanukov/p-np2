import Pnp.BoolFunc.Sensitivity
import Pnp.BoolFunc
import Pnp.DecisionTree

open BoolFunc

namespace BoolFunc

variable {n : ℕ}

-- This axiom summarises the decision-tree construction for families of
-- low-sensitivity Boolean functions.  The result is classical: if every
-- member of `F` has sensitivity at most `s`, then one can build a decision
-- tree of depth `O(s * log n)` simultaneously for all functions in the
-- family (see Gopalan--Moshkovitz--Oliveira).  Each root-to-leaf path yields
-- a rectangular subcube that is monochromatic for the whole family.  The
-- number of such subcubes is therefore at most an exponential in
-- `s * log₂ (n + 1)`.  We keep the statement as an axiom here and rely on
-- the external combinatorial argument.
-- TODO: replace this axiom with the formal decision-tree construction.
axiom decisionTree_cover
  {n : Nat} (F : Family n) (s C : Nat) [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n))


/-- Trivial base case: if all functions in the family are constant on the full
cube, we can cover all ones with just that cube.  This lemma acts as a base case
for the eventual recursive construction of `decisionTree_cover`. -/
lemma decisionTree_cover_of_constant
  {n : Nat} (F : Family n) (s C : Nat) [Fintype (Point n)]
  (hconst : ∃ b, ∀ f ∈ F, ∀ x, f x = b) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := by
  classical
  rcases hconst with ⟨b, hb⟩
  -- The full cube represented as a subcube.
  let R : Subcube n :=
    { idx := ∅,
      val := by
        intro i hi
        exact False.elim <| Finset.notMem_empty _ hi }
  have hmem : ∀ x : Point n, x ∈ₛ R := by
    intro x i hi; cases hi
  have hmono : Subcube.monochromaticForFamily R F := by
    refine ⟨b, ?_⟩
    intro f hf x hx
    simpa using hb f hf x
  refine ⟨{R}, ?_, ?_, ?_⟩
  · intro R' hR'
    have hR : R' = R := by simpa using Finset.mem_singleton.mp hR'
    simpa [hR] using hmono
  · intro f hf x hx
    refine ⟨R, by simp, ?_⟩
    simpa using hmem x
  · have hcard : ({R} : Finset (Subcube n)).card = 1 := by simp
    have hpos : 0 < Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) :=
      pow_pos (by decide) _
    have : 1 ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) :=
      Nat.succ_le_of_lt hpos
    simpa [hcard] using this
lemma monochromaticFor_of_family_singleton {R : Subcube n} {f : BFunc n} :
    Subcube.monochromaticForFamily R ({f} : Family n) →
    Subcube.monochromaticFor R f := by
  intro h
  rcases h with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x hx
  have := hb f (by simp) hx
  simpa using this

/-- A decision tree with depth `d` has at most `2 ^ d` leaf subcubes. -/
lemma tree_depth_bound (t : DecisionTree n) :
    (DecisionTree.leaves_as_subcubes t).card ≤ 2 ^ DecisionTree.depth t := by
  simpa using DecisionTree.leaves_as_subcubes_card_le_pow_depth (t := t)

/--
Convert an explicit decision tree into a rectangle cover.
If every leaf of `t` is monochromatic for `F` and the tree covers all
`1`-inputs, then the leaf subcubes themselves form the desired cover.
The size bound follows from `tree_depth_bound`.
-/
lemma decisionTree_cover_of_tree
  {n s C : Nat} (F : Family n) (t : DecisionTree n) [Fintype (Point n)]
  (hmono : ∀ R ∈ DecisionTree.leaves_as_subcubes t,
      Subcube.monochromaticForFamily R F)
  (hcov : ∀ f ∈ F, ∀ x, f x = true →
      ∃ R ∈ DecisionTree.leaves_as_subcubes t, x ∈ₛ R)
  (hdepth : DecisionTree.depth t ≤ C * s * Nat.log2 (Nat.succ n)) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := by
  classical
  let Rset := DecisionTree.leaves_as_subcubes t
  have hcard_le : Rset.card ≤ 2 ^ DecisionTree.depth t :=
    DecisionTree.tree_depth_bound (t := t)
  have hcard : Rset.card ≤ 2 ^ (C * s * Nat.log2 (Nat.succ n)) := by
    exact le_trans hcard_le
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hdepth)
  refine ⟨Rset, ?_, ?_, hcard⟩
  · intro R hR; exact hmono R hR
  · intro f hf x hx; exact hcov f hf x hx

/-- **Low-sensitivity cover** (statement only).  If every function in the
    family has sensitivity at most `s`, then there exists a small set of
    subcubes covering all ones of the family.  The proof will use decision
    trees or the Gopalan--Moshkovitz--Oliveira bound.  Here we only record the
    statement. -/
lemma low_sensitivity_cover (F : Family n) (s C : ℕ)
    [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := by
  classical
  simpa using decisionTree_cover (F := F) (s := s) (C := C) Hsens

/-/ Variant of `low_sensitivity_cover` for a single Boolean function.
    This skeleton assumes a suitable decision tree for `f` of depth
    `O(s * log n)`.  All remaining steps are placeholders. -/
lemma low_sensitivity_cover_single
  (n s C : ℕ) (f : BoolFunc.BFunc n)
    [Fintype (BoolFunc.Point n)]
    (Hsens : BoolFunc.sensitivity f ≤ s) :
  ∃ Rset : Finset (BoolFunc.Subcube n),
    (∀ R ∈ Rset, BoolFunc.Subcube.monochromaticFor R f) ∧
    (∀ x : BoolFunc.Point n, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := by
  classical
  have hfamily : ∀ g ∈ ({f} : Family n), sensitivity g ≤ s := by
    intro g hg
    have hg' : g = f := by simpa [Finset.mem_singleton] using hg
    simpa [hg'] using Hsens
  obtain ⟨Rset, hmono, hcov, hcard⟩ :=
    decisionTree_cover (F := ({f} : Family n)) (s := s) (C := C) hfamily
  refine ⟨Rset, ?_, ?_, hcard⟩
  · intro R hR
    have := hmono R hR
    exact monochromaticFor_of_family_singleton this
  · intro x hx
    simpa using hcov f (by simp) x hx

end BoolFunc

