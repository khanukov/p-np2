import Pnp2.cover2

open Boolcube (Point Subcube)
open BoolFunc (Family BFunc)
open Cover2

namespace Cover2Test

/-- `mBound` is computed via the wrapper definition. -/
example : mBound 1 0 = 2 := by
  simp [mBound]

/-- Numeric bound specialised to trivial parameters using the positive version. -/
example : 2 * 0 + 1 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simpa using numeric_bound_pos (n := 1) (h := 0) hn

/-- `numeric_bound_pos` also holds when `n` is strictly positive. -/
example : 2 * 0 + 2 ≤ mBound 2 0 := by
  have hn : 0 < (2 : ℕ) := by decide
  simpa using numeric_bound_pos (n := 2) (h := 0) hn

/-- Doubling the bound for a smaller budget stays below the next budget. -/
example : 2 * mBound 1 0 ≤ mBound 1 1 := by
  simpa using two_mul_mBound_le_succ (n := 1) (h := 0)

/-- `pow_le_mBound_simple` for trivial parameters. -/
example : 1 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simpa using pow_le_mBound_simple (n := 1) (h := 0) hn

/-- `two_le_mBound` verifies the bound is at least `2`. -/
example : 2 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simpa using two_le_mBound (n := 1) (h := 0) hn

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

/-- When no functions and no rectangles are present, there is no uncovered pair. -/
example :
    Cover2.firstUncovered (F := (∅ : Family 1))
      (Rset := (∅ : Finset (Subcube 1))) = none := by
  classical
  simp [Cover2.firstUncovered, Cover2.uncovered, Cover2.NotCovered]

end Cover2Test

