import Pnp2.cover2

open Cover2
open BoolFunc
open Boolcube

namespace Cover2Test

/-- `mBound` is computed via the wrapper definition. -/
example : mBound 1 0 = 2 := by
  simp [mBound]

/-- Numeric bound specialised to trivial parameters. -/
example : 2 * 0 + 1 ≤ mBound 1 0 := by
  simpa using numeric_bound (n := 1) (h := 0)

/-- Positivity of `mBound` when `n` is positive. -/
example : 0 < mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simpa [mBound] using mBound_pos (n := 1) (h := 0) hn

/-- Trivial instance of `NotCovered` for the empty set of rectangles. -/
example (x : Boolcube.Point 2) :
    NotCovered (Rset := (∅ : Finset (Boolcube.Subcube 2))) x := by
  simpa using notCovered_empty (n := 2) (x := x)

/-- `NotCovered` is monotone with respect to set inclusion. -/
example (x : Boolcube.Point 2) :
    NotCovered (Rset := (∅ : Finset (Boolcube.Subcube 2))) x := by
  have hx : NotCovered (Rset := (∅ : Finset (Boolcube.Subcube 2))) x := by
    simpa using notCovered_empty (n := 2) (x := x)
  simpa using
    (NotCovered.monotone (n := 2)
      (R₁ := (∅ : Finset (Boolcube.Subcube 2))) (R₂ := (∅ : Finset (Boolcube.Subcube 2)))
      (hsub := by intro R h; simpa using h) hx)


end Cover2Test

