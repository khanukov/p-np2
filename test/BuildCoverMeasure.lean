import Pnp2.cover

open Cover BoolFunc

namespace BuildCoverMeasureTests

/-- The initial measure is bounded by `mBound`. -/
example {n h : ℕ} (F : Family n) :
    mu F h (∅ : Finset (Subcube n)) ≤ mBound n h :=
  mu_init_bound (F := F) (h := h)

/-- Running `buildCover` cannot increase the measure. -/
example {n h : ℕ} (F : Family n) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu F h (buildCover F h hH) ≤ mu F h (∅ : Finset (Subcube n)) :=
  mu_buildCover_le_start (F := F) (h := h) (hH := hH)

/-- After building a cover the measure collapses to `2 * h`. -/
example {n h : ℕ} (F : Family n) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu F h (buildCover F h hH) = 2 * h :=
  buildCover_mu (F := F) (h := h) (hH := hH)

end BuildCoverMeasureTests
