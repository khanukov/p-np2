import Pnp2.BoolFunc
import Pnp2.BoolFunc.Sensitivity
import Pnp2.DecisionTree
import Pnp2.low_sensitivity_cover
-- Note: the historical cover modules are not fully maintained.
-- We focus on the foundational parts that still compile cleanly.

open BoolFunc

namespace LegacyTests

/-- The support of a constant false function is empty. -/
lemma support_const_false (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

/-- A trivial decision tree has at most `2 ^ depth` leaves. -/
example :
    (DecisionTree.leaf true : DecisionTree 1).leaf_count ≤
      2 ^ (DecisionTree.depth (DecisionTree.leaf true : DecisionTree 1)) := by
  have hx :=
    DecisionTree.leaf_count_le_pow_depth
      (t := (DecisionTree.leaf true : DecisionTree 1))
  exact hx

/-- The low-sensitivity cover for a single function exists. -/
example (n s C : ℕ) (f : BFunc n) [Fintype (Point n)]
    (Hs : sensitivity f ≤ s) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticFor R f) ∧
      (∀ x : Point n, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (C * s * Nat.log2 (Nat.succ n)) := by
  classical
  simpa using
    BoolFunc.low_sensitivity_cover_single
      (n := n) (s := s) (C := C) (f := f) Hs

end LegacyTests
