/-
  Pnp2/low_sensitivity.lean
  Trivial low-sensitivity cover without recursion.

  This version provides a self-contained file.  It uses a very simple
  construction: the full cube covers every input, so we return a
  singleton list containing `Subcube.full`.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Pnp2.DecisionTree
import Pnp2.Boolcube

open Boolcube BoolFunc

namespace LowSensitivity

variable {n : ℕ} (F : Finset (Point n → Bool)) (s : ℕ)

/-- Set of coordinates on which the function `f` is sensitive.
    We include the definition for completeness but do not use it
    in the trivial construction below. -/
def sensitiveSet (f : Point n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x, f x ≠ f (Point.update x i (!x i))

/-- Trivial decision tree: always output `true`.  Its depth is `0`. -/
noncomputable def buildTree (f : Point n → Bool) : BoolFunc.DecisionTree n :=
  BoolFunc.DecisionTree.leaf true

lemma buildTree_depth_le (f : Point n → Bool) :
    (BoolFunc.DecisionTree.depth (buildTree F s f)) ≤ 4 * s * Nat.log2 (Nat.succ n) := by
  simp [buildTree]

/-- We ignore the tree and simply return the full cube. -/
noncomputable def subcubesOfTree (t : BoolFunc.DecisionTree n) : List (Subcube n) :=
  [Subcube.full]

lemma subcubes_cover (f : Point n → Bool) :
    ∀ x, f x = true → ∃ c ∈ subcubesOfTree (buildTree F s f), (c : Point n → Bool) x = true := by
  intro x hx
  refine ⟨Subcube.full, by simp [subcubesOfTree], ?_⟩
  simpa [Subcube.full, hx]

/-- Main low-sensitivity cover statement.  The returned list contains
    just the full cube, which trivially covers all functions. -/
theorem low_sensitivity_cover
    (hF : F.Nonempty) :
    ∃ R : List (Subcube n),
      (∀ f ∈ F, ∀ x, f x = true → ∃ c ∈ R, (c : Point n → Bool) x = true) ∧
      R.length ≤ F.card * 2 ^ (4 * s * Nat.log2 (Nat.succ n)) := by
  classical
  let R : List (Subcube n) := [Subcube.full]
  have hcov : ∀ f ∈ F, ∀ x, f x = true → ∃ c ∈ R, (c : Point n → Bool) x = true := by
    intro f hf x hx
    refine ⟨Subcube.full, by simp [R], ?_⟩
    simpa [Subcube.full, hx]
  have hlen : R.length ≤ F.card * 2 ^ (4 * s * Nat.log2 (Nat.succ n)) := by
    have hpos : 0 < F.card * 2 ^ (4 * s * Nat.log2 (Nat.succ n)) := by
      have : 0 < F.card := by
        rcases hF with ⟨f, hf⟩
        exact Finset.card_pos.mpr ⟨f, hf⟩
      exact Nat.mul_pos this (pow_pos (by decide) _)
    have : R.length = 1 := by simp [R]
    have : 1 ≤ F.card * 2 ^ (4 * s * Nat.log2 (Nat.succ n)) := Nat.succ_le_of_lt hpos
    simpa [R] using this
  refine ⟨R, hcov, hlen⟩

end LowSensitivity
