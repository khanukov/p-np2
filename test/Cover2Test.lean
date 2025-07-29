import Pnp2.cover2

open Boolcube (Point Subcube)

open Cover2

namespace Cover2Test

/-- `mBound` is computed via the wrapper definition. -/
example : mBound 1 0 = 2 := by
  simp [mBound]

/-- Numeric bound specialised to trivial parameters using the positive version. -/
example : 2 * 0 + 1 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simp [numeric_bound_pos (n := 1) (h := 0) hn]

/-- `numeric_bound_pos` also holds when `n` is strictly positive. -/
example : 2 * 0 + 2 ≤ mBound 2 0 := by
  have hn : 0 < (2 : ℕ) := by decide
  simp [numeric_bound_pos (n := 2) (h := 0) hn]

/-- Doubling the bound for a smaller budget stays below the next budget. -/
example : 2 * mBound 1 0 ≤ mBound 1 1 := by
  simpa using two_mul_mBound_le_succ (n := 1) (h := 0)

/-- `pow_le_mBound_simple` for trivial parameters. -/
example : 1 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simp [pow_le_mBound_simple (n := 1) (h := 0) hn]

/-- `two_le_mBound` verifies the bound is at least `2`. -/
example : 2 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simp [two_le_mBound (n := 1) (h := 0) hn]

/-- Doubling the bound for `h = 0` stays below the next budget. -/
example : 2 * mBound 1 0 ≤ mBound 1 1 := by
  simpa using two_mul_mBound_le_succ (n := 1) (h := 0)

/-- Inserting a single rectangle stays within the next budget. -/
example :
    (insert Subcube.full (∅ : Finset (Subcube 1))).card ≤ mBound 1 1 := by
  classical
  have hcard : ( (∅ : Finset (Subcube 1)).card ) ≤ mBound 1 0 := by
    simp [mBound]
  have hn : 0 < (1 : ℕ) := by decide
  simpa using
    (card_insert_mBound_succ (n := 1) (h := 0)
      (Rset := (∅ : Finset (Subcube 1))) (R := Subcube.full)
      hcard hn)

/-- Nothing is covered by an empty set of rectangles. -/
example (x : Point 1) :
    Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
  simpa using Cover2.notCovered_empty (n := 1) (x := x)

/-- `NotCovered` is monotone under set inclusion. -/
example (x : Point 1) (R : Subcube 1)
    (hx : Cover2.NotCovered (n := 1) (Rset := {R}) x) :
    Cover2.NotCovered (n := 1) (Rset := (∅ : Finset (Subcube 1))) x := by
  have hsub : (∅ : Finset (Subcube 1)) ⊆ {R} := by
    intro r hr; cases hr
  simpa using
    Cover2.NotCovered.monotone (n := 1) (R₁ := (∅ : Finset (Subcube 1)))
      (R₂ := {R}) hsub hx

/-- A single full rectangle covers all `1`-inputs. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) := by
  exact Cover2.AllOnesCovered.full _

/-- `AllOnesCovered.superset` allows enlarging the rectangle set. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full, Subcube.full} : Finset (Subcube 1)) := by
  classical
  have hcov : Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) :=
    Cover2.AllOnesCovered.full _
  have hsub : ({Subcube.full} : Finset (Subcube 1)) ⊆ {Subcube.full, Subcube.full} := by
    intro R hR
    simp [Finset.mem_insert, Finset.mem_singleton] at hR
    simp [Finset.mem_insert, Finset.mem_singleton, hR]
  exact
    Cover2.AllOnesCovered.superset (F := {(fun _ : Point 1 => true)})
      (R₁ := {Subcube.full}) (R₂ := {Subcube.full, Subcube.full})
      hcov hsub

/-- The union of two covers is again a cover. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} ∪ {Subcube.full} : Finset (Subcube 1)) := by
  classical
  have hcov := Cover2.AllOnesCovered.full
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
  simpa using
    Cover2.AllOnesCovered.union (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (R₁ := {Subcube.full}) (R₂ := {Subcube.full}) hcov hcov

/-- Inserting a rectangle preserves coverage. -/
example :
    Cover2.AllOnesCovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      (insert Subcube.full {Subcube.full} : Finset (Subcube 1)) := by
  classical
  have hcov := Cover2.AllOnesCovered.full
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
  simpa using
    Cover2.AllOnesCovered.insert (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
      (Rset := {Subcube.full}) (R := Subcube.full) hcov

/-- If all `1`-inputs are covered by a single full rectangle, the uncovered set
is empty. -/
example :
    Cover2.uncovered (n := 1)
      ({(fun _ : Point 1 => true)} : BoolFunc.Family 1)
      ({Subcube.full} : Finset (Subcube 1)) = (∅ : Set (Sigma (fun _ => Point 1))) := by
  have hcov := Cover2.AllOnesCovered.full
      (F := ({(fun _ : Point 1 => true)} : BoolFunc.Family 1))
  simpa using
    Cover2.uncovered_eq_empty_of_allCovered
      (n := 1)
      (F := {(fun _ : Point 1 => true)})
      (Rset := {Subcube.full}) hcov

end Cover2Test

