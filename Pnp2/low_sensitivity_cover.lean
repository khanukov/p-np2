import Pnp2.BoolFunc.Sensitivity
import Pnp2.BoolFunc
import Pnp2.DecisionTree

open BoolFunc

namespace BoolFunc

variable {n : ℕ}

-- This axiom summarises the decision-tree construction for families of
-- low-sensitivity Boolean functions.  The underlying combinatorial result
-- (due to Gopalan--Moshkovitz--Oliveira) shows that a single decision tree of
-- depth `O(s * log n)` suffices to compute every function in the family.
-- Each leaf of that tree corresponds to a rectangular subcube on which all
-- functions agree.  The number of such subcubes is therefore bounded by an
-- exponential in `s * log₂ (n + 1)`.  We assume this theorem as an axiom in
-- the current development.
axiom decisionTree_cover
  {n : Nat} (F : Family n) (s C : Nat) [Fintype (Point n)]
    (Hsens : ∀ f ∈ F, sensitivity f ≤ s) :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n))

/-!
The lemma states that a family of low-sensitivity Boolean functions admits a
compact cover by monochromatic subcubes.  Its proof is expected to recursively
build a decision tree, branching on sensitive coordinates until each leaf is
constant.  Formalising this construction is ongoing work, so we keep the result
as an axiom and document the intended approach here. -/

/-- Trivial base case: if all functions in the family are constant on the full
cube, we can cover all ones with just that cube.  This lemma acts as a base case
for the eventual recursive construction of `decisionTree_cover`. -/
lemma decisionTree_cover_of_constant
  {n : Nat} (F : Family n) (s C : Nat) [Fintype (Point n)]
  (Hsens : ∀ f ∈ F, sensitivity f ≤ s)
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

/--
  Degenerate base case: the empty family has no `1`-inputs to cover.
  Returning the empty set of rectangles trivially satisfies the
  monochromaticity and coverage requirements.
-/
lemma decisionTree_cover_empty
  {n s C : Nat} [Fintype (Point n)] :
  ∃ Rset : Finset (Subcube n),
    (∀ R ∈ Rset, Subcube.monochromaticForFamily R (∅ : Family n)) ∧
    (∀ f ∈ (∅ : Family n), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
    Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := by
  classical
  refine ⟨∅, ?_, ?_, ?_⟩
  · intro R hR; simpa using hR
  · intro f hf; simpa using hf
  · have : 0 ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := Nat.zero_le _
    simpa using this

lemma monochromaticFor_of_family_singleton {R : Subcube n} {f : BFunc n} :
    Subcube.monochromaticForFamily R ({f} : Family n) →
    Subcube.monochromaticFor R f := by
  intro h
  rcases h with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x hx
  have := hb f (by simp) hx
  simpa using this

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
  -- Treat `{f}` as a family and apply `decisionTree_cover`.
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

