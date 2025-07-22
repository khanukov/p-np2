-- sat_via_cover.lean
-- ===================
--
-- Implementation of a simple SAT solver using the rectangle cover
-- returned by `coverFamily`.  The algorithm enumerates the rectangles
-- and tests one point in each.  If any point satisfies the function,
-- SAT is proven.

import Pnp2.cover
import Pnp2.BoolFunc

open Classical

namespace Boolcube
namespace Subcube

/-- `sample` picks a concrete point inside a subcube by assigning
    `false` to all free coordinates.  This is used by the SAT
    procedure as a witness for the rectangle. -/
noncomputable def sample {n : ℕ} (R : Subcube n) : Point n :=
  fun i => (R.fix i).getD false

lemma sample_mem {n : ℕ} (R : Subcube n) :
    R.Mem (sample R) := by
  intro i
  cases h : R.fix i <;> simp [sample, h]

end Subcube
end Boolcube

namespace CoverSAT

/--
`SATViaCover f hH` decides whether the Boolean function `f` is
satisfiable under the assumption that the singleton family `{f}`
has collision entropy at most `h`.  The function constructs the
cover provided by `coverFamily` and checks `f` on a single sample
point from each rectangle.
-/
noncomputable def SATViaCover {n : ℕ}
    (f : Boolcube.BFunc n) {h : ℕ}
    (hH : BoolFunc.H₂ ({f} : BoolFunc.Family n) ≤ (h : ℝ)) : Bool :=
  let cover := Cover.coverFamily (F := ({f} : BoolFunc.Family n))
      (h := h) hH
  cover.any (fun R => f (Boolcube.Subcube.sample R))

/--
`SATViaCover` is correct: it returns `true` iff there exists a
satisfying assignment for `f`.
-/
lemma SATViaCover_correct {n : ℕ} (f : Boolcube.BFunc n) {h : ℕ}
    (hH : BoolFunc.H₂ ({f} : BoolFunc.Family n) ≤ (h : ℝ)) :
    SATViaCover (n := n) f hH = true ↔ ∃ x, f x = true := by
  classical
  let cover := Cover.coverFamily (F := ({f} : BoolFunc.Family n))
      (h := h) hH
  constructor
  · -- If the procedure returns `true`, a rectangle produces a witness.
    intro hsat
    have hany := Finset.any_eq_true.mpr hsat
    rcases hany with ⟨R, hR, hval⟩
    refine ⟨_, hval⟩
  · -- Conversely, if a satisfying assignment exists, some rectangle
    -- from the cover contains it and forces `SATViaCover` to return `true`.
    intro hsat
    rcases hsat with ⟨x, hx⟩
    have hcov := (Cover.coverFamily_spec_cover
      (F := ({f} : BoolFunc.Family n)) (h := h) hH)
    have hmono := Cover.coverFamily_mono
      (F := ({f} : BoolFunc.Family n)) (h := h) hH
    have hxR := (hcov (f := f) (by simp) x hx)
    rcases hxR with ⟨R, hR, hxR⟩
    have hval : f (Boolcube.Subcube.sample R) = true := by
      rcases hmono R hR with ⟨b, hb⟩
      have hx' := hb f (by simp) hxR
      have hs := hb f (by simp) (Boolcube.Subcube.sample_mem R)
      -- The rectangle is monochromatic.  Since `x` yields `true`,
      -- every point of the rectangle does as well.
      simpa [hx'] using hs
    have hany : Finset.any cover (fun S => f (Boolcube.Subcube.sample S)) :=
      Finset.any_true_iff.mpr ⟨R, hR, hval⟩
    simpa [SATViaCover, cover] using hany

end CoverSAT

