import OldAttempts.BoolFunc
import OldAttempts.Boolcube
import OldAttempts.Cover.SubcubeAdapters
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Classical
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

namespace Cover2

/-!
### Lifting monochromaticity through restrictions

The cover construction often restricts a family of Boolean functions to a
subcube where one coordinate is fixed.  The following lemmas explain how
monochromaticity of the restricted family can be transferred back to the
original family.  These results will support the recursion once the full cover
algorithm is ported.
-/

/--
If a subcube `R` fixes coordinate `i` to the value `b`, then every function in a
family `F` takes the same value on `R` provided that the restricted family
`F.restrict i b` is monochromatic on `R`.
-/
lemma lift_mono_of_restrict
    {n : ℕ} {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (Family.restrict F i b)) :
    Subcube.monochromaticForFamily R F := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f hf x hx
  -- membership in the restricted family comes from restricting a function of `F`
  have hf0 : BFunc.restrictCoord f i b ∈ Family.restrict F i b :=
    (Family.mem_restrict).2 ⟨f, hf, rfl⟩
  -- the point `x` agrees with the fixed value on the `i`‑th coordinate
  have hxib : x i = b := hfix x hx
  -- updating `x` at position `i` does not change it because `x i = b`
  have hxupdate : BoolFunc.Point.update x i b = x := by
    funext j; by_cases hji : j = i
    · subst hji; simp [BoolFunc.Point.update, hxib]
    · simp [BoolFunc.Point.update, hji]
  -- the restricted function is constant with colour `c` on `R`
  have htmp := hc (BFunc.restrictCoord f i b) hf0 x hx
  have : f x = c := by
    simpa [BFunc.restrictCoord, hxupdate] using htmp
  exact this

/--
A convenience wrapper for `lift_mono_of_restrict` that reuses the fixed-coordinate
hypothesis.
-/
lemma lift_mono_of_restrict_fixOne
    {n : ℕ} {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (Family.restrict F i b)) :
    Subcube.monochromaticForFamily R F :=
  lift_mono_of_restrict (F := F) (i := i) (b := b) (R := R) hfix hmono

end Cover2

