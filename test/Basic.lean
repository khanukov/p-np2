import Pnp.BoolFunc
import Pnp.BoolFunc.Support
import Pnp.DecisionTree
import Pnp.Agreement
import Pnp.Boolcube

open BoolFunc

namespace BasicTests

/-- The support of a constant false function is empty. -/
lemma support_const_false (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  ext i
  simp [support]

-- We can also verify that toggling an irrelevant coordinate leaves a
-- function unchanged by direct calculation.
example (x : Point 2) (b : Bool) :
    let f : BFunc 2 := fun y => y 0
    f x = f (Point.update x 1 b) := by
  classical
  let f : BFunc 2 := fun y => y 0
  have hneq : (0 : Fin 2) ≠ 1 := by decide
  simp [Point.update, hneq]

-- `eval_update_not_support` automatically shows that modifying a
-- non-essential coordinate leaves a function unchanged.
example (x : Point 2) (b : Bool) :
    (fun y : Point 2 => y 0) x = (fun y : Point 2 => y 0) (Point.update x 1 b) := by
  classical
  have hi : (1 : Fin 2) ∉ support (fun y : Point 2 => y 0) := by
    simp [support]
  have hx :=
    BoolFunc.eval_update_not_support
      (f := fun y : Point 2 => y 0) (i := 1) hi x b
  exact hx

-- A trivial decision tree has at most `2 ^ depth` leaves.
example :
    (DecisionTree.leaf true : DecisionTree 1).leaf_count ≤
      2 ^ (DecisionTree.depth (DecisionTree.leaf true : DecisionTree 1)) := by
  have hx :=
    DecisionTree.leaf_count_le_pow_depth
      (t := (DecisionTree.leaf true : DecisionTree 1))
  exact hx

example {n : ℕ} (x : Point n) :
    x ∈ₛ Agreement.Subcube.fromPoint (n := n) x Finset.univ := by
  classical
  intro i hi
  simp [Agreement.Subcube.fromPoint]

-- There exists a point where a non-trivial function evaluates to `true`.
example :
    ∃ x, (fun y : Point 1 => y 0) x = true := by
  classical
  have hmem : (0 : Fin 1) ∈ support (fun y : Point 1 => y 0) := by
    classical
    have hx : (fun y : Point 1 => y 0) (fun _ => false) ≠
        (fun y : Point 1 => y 0) (Point.update (fun _ => false) 0 true) := by
      simp [Point.update]
    exact mem_support_iff.mpr ⟨fun _ => false, hx⟩
  have hsupp : support (fun y : Point 1 => y 0) ≠ (∅ : Finset (Fin 1)) := by
    intro hempty
    simp [hempty] at hmem
  exact BoolFunc.exists_true_on_support (f := fun y : Point 1 => y 0) hsupp

-- Basic lemmas from `Boolcube`
example (n : ℕ) :
    (Boolcube.Subcube.full : Boolcube.Subcube n).dim = n := by
  classical
  simpa using Boolcube.Subcube.dim_full (n := n)


end BasicTests
