import Pnp2.Agreement
import Pnp2.BoolFunc
import Pnp2.BoolFunc.Support
import Pnp2.DecisionTree
import Pnp2.low_sensitivity_cover

open BoolFunc
open Agreement

namespace Pnp2Tests

/-- The support of a constantly false function is empty. -/
example (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

/-- Modifying an irrelevant coordinate leaves the function unchanged. -/
example (x : Point 2) (b : Bool) :
    (fun y : Point 2 => y 0) x = (fun y : Point 2 => y 0) (Point.update x 1 b) := by
  classical
  have hi : (1 : Fin 2) ∉ support (fun y : Point 2 => y 0) := by
    simp [support]
  simpa using
    BoolFunc.eval_update_not_support
      (f := fun y : Point 2 => y 0) (i := 1) hi x b

/-- If two points agree on all coordinates of `K`, the second lies in the same subcube. -/
example {n : ℕ} {K : Finset (Fin n)} {x y : Point n}
    (h : ∀ i, i ∈ K → x i = y i) :
    y ∈ₛ Subcube.fromPoint x K := by
  simpa using Agreement.mem_fromPoint_of_agree (K := K) (x := x) (y := y) h

/-- Every non-trivial function evaluates to `true` somewhere on its support. -/
example :
    ∃ x, (fun y : Point 1 => y 0) x = true := by
  classical
  have hmem : (0 : Fin 1) ∈ support (fun y : Point 1 => y 0) := by
    have hx : (fun y : Point 1 => y 0) (fun _ => false) ≠
        (fun y : Point 1 => y 0) (Point.update (fun _ => false) 0 true) := by
      simp [Point.update]
    exact mem_support_iff.mpr ⟨fun _ => false, hx⟩
  have hsupp : support (fun y : Point 1 => y 0) ≠ (∅ : Finset (Fin 1)) := by
    intro hempty
    simp [hempty] at hmem
  exact BoolFunc.exists_true_on_support (f := fun y : Point 1 => y 0) hsupp

/-- A trivial tree has depth zero and one leaf subcube. -/
example :
    (DecisionTree.leaves_as_subcubes (DecisionTree.leaf true : DecisionTree 1)).card = 0 :=
by
  simp [DecisionTree.leaves_as_subcubes]

/-- The depth bound lemma from the legacy library. -/
example (t : DecisionTree 2) :
    (DecisionTree.leaves_as_subcubes t).card ≤ 2 ^ DecisionTree.depth t :=
by
  simpa using DecisionTree.tree_depth_bound (t := t)

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

end Pnp2Tests
