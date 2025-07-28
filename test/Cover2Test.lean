import Pnp2.cover2

open Cover2

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

/-- `pow_le_mBound_simple` for trivial parameters. -/
example : 1 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simpa using pow_le_mBound_simple (n := 1) (h := 0) hn

/-- `two_le_mBound` verifies the bound is at least `2`. -/
example : 2 ≤ mBound 1 0 := by
  have hn : 0 < (1 : ℕ) := by decide
  simpa using two_le_mBound (n := 1) (h := 0) hn

end Cover2Test

