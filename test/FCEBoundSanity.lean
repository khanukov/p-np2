import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.family_entropy_cover
import Pnp2.Cover.Bounds

open Classical
open BoolFunc
open Boolcube
open Cover2

/-- Constant `false` Boolean function on `n` variables. -/
noncomputable def constFalse (n : ℕ) : BFunc n := fun _ => false

/-- Singleton family containing only the constant `false` function. -/
noncomputable def singletonFamily (n : ℕ) : BoolFunc.Family n := {constFalse n}

lemma singleton_family_card (n : ℕ) :
    (singletonFamily n).card = 1 := by
  classical
  simp [singletonFamily]

lemma singleton_entropy (n : ℕ) :
    H₂ (singletonFamily n) = 0 := by
  classical
  simpa [singletonFamily]
    using H₂_card_one (F := singletonFamily n) (singleton_family_card n)

/--
A direct sanity check showing that `familyEntropyCover` exposes the strengthened
`mBound` cardinality estimate.
-/
example (hH : H₂ (singletonFamily 6) ≤ (2 : ℝ)) :
    (Boolcube.familyEntropyCover (F := singletonFamily 6) (h := 2)
        hH (by decide) (by decide)).rects.card ≤ Cover2.mBound 6 2 := by
  classical
  simpa using (Boolcube.familyEntropyCover (F := singletonFamily 6) (h := 2)
      hH (by decide) (by decide)).bound
