import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Pnp.DecisionTree
import Pnp.Boolcube
import Pnp.BoolFunc

open Boolcube

namespace LowSensitivity

open BoolFunc

variable {n : ℕ} (F : Finset (BoolFunc.Point n → Bool)) (s : ℕ)

/-- The full cube viewed as a `BoolFunc.Subcube`. -/
def fullSubcube : BoolFunc.Subcube n :=
  { idx := ∅, val := fun i h => False.elim <| Finset.not_mem_empty _ h }

/-- Set of coordinates on which the function `f` is sensitive. -/
def sensitiveSet (f : BoolFunc.Point n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x, f x ≠ f (BoolFunc.Point.update x i (!x i))

/-- Trivial decision tree: always output `true`.  Its depth is `0`. -/
noncomputable def buildTree (f : BoolFunc.Point n → Bool) : BoolFunc.DecisionTree n :=
  BoolFunc.DecisionTree.leaf true

lemma buildTree_depth_le (f : BoolFunc.Point n → Bool) :
    (BoolFunc.DecisionTree.depth (buildTree f)) ≤ 4 * s * Nat.log2 (Nat.succ n) := by
  have : (BoolFunc.DecisionTree.depth (buildTree f)) = 0 := by
    simp [buildTree, BoolFunc.DecisionTree.depth]
  simpa [this] using Nat.zero_le (4 * s * Nat.log2 (Nat.succ n))

/-- We ignore the tree and simply return the full cube. -/
noncomputable def subcubesOfTree (t : BoolFunc.DecisionTree n) : List (BoolFunc.Subcube n) :=
  [fullSubcube (n := n)]

lemma subcubes_cover (f : BoolFunc.Point n → Bool) :
    ∀ x, f x = true → ∃ c ∈ subcubesOfTree (buildTree f), x ∈ₛ c := by
  intro x hx
  refine ⟨fullSubcube (n := n), by simp [subcubesOfTree, fullSubcube], ?_⟩
  simp [fullSubcube, Subcube.mem]

/-- Main low-sensitivity cover statement.  The returned list contains
    just the full cube, which trivially covers all functions. -/
theorem low_sensitivity_cover
    (hF : F.Nonempty) :
    ∃ R : List (BoolFunc.Subcube n),
      (∀ f ∈ F, ∀ x, f x = true → ∃ c ∈ R, x ∈ₛ c) ∧
      R.length ≤ F.card * 2 ^ (4 * s * Nat.log2 (Nat.succ n)) := by
  classical
  let R : List (BoolFunc.Subcube n) := [fullSubcube (n := n)]
  have hcov : ∀ f ∈ F, ∀ x, f x = true → ∃ c ∈ R, x ∈ₛ c := by
    intro f hf x hx
    refine ⟨fullSubcube (n := n), by simp [R, fullSubcube], ?_⟩
    simp [fullSubcube, Subcube.mem]
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
