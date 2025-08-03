import Pnp2.BoolFunc
import Pnp2.Boolcube
import Pnp2.Cover.SubcubeAdapters

open Classical
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

namespace Cover2

/-!
### Lifting monochromaticity from restricted families

This short module gathers lemmas that allow us to transfer
monochromaticity information from a restricted family of Boolean functions
back to the original family.  They will be useful when working with the
recursive cover construction, where coordinates are fixed one by one.

The statements and proofs were previously located in `cover2.lean`,
but are isolated here for reusability and to keep the main file compact.
-/

/--
If a subcube `R` already fixes the `i`‑th coordinate to the value `b` and
a family `F` is monochromatic after restricting every function to that
coordinate, then `F` is also monochromatic on `R`.

The proof extracts the color `c` witnessing monochromaticity of the
restricted family and shows that every function in the original family
must take the value `c` on `R`.
-/
lemma lift_mono_of_restrict
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily R F := by
  classical
  -- Unpack the color `c` that the restricted family takes on `R`.
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f hf x hx
  -- After restriction, `f` belongs to the restricted family.
  have hf0 : f.restrictCoord i b ∈ F.restrict i b :=
    (BoolFunc.Family.mem_restrict).2 ⟨f, hf, rfl⟩
  -- Points of `R` have the fixed coordinate `b`.
  have hxib : x i = b := hfix x hx
  -- Updating the fixed coordinate leaves the point unchanged.
  have hxupdate : BoolFunc.update x i b = x := by
    funext j; by_cases hji : j = i
    · subst hji; simp [BoolFunc.update, hxib]
    · simp [BoolFunc.update, hji]
  -- Apply monochromaticity of the restricted family.
  have htmp := hc (f.restrictCoord i b) hf0 x hx
  -- Rewrite the hypothesis back in terms of the original function `f`.
  have : f x = c := by
    simpa [BFunc.restrictCoord, hxupdate] using htmp
  exact this

/--
A convenience wrapper around `lift_mono_of_restrict` that is useful when
the hypothesis that `R` fixes the coordinate `i` is immediately available.
-/
lemma lift_mono_of_restrict_fixOne
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily R F :=
  lift_mono_of_restrict (F := F) (i := i) (b := b) (R := R) hfix hmono

end Cover2

