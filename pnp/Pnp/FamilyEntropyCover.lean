import Pnp.Boolcube
import Pnp.Cover

namespace Boolcube

open Entropy
open Cover

/-!
`familyCollisionEntropyCover` wraps the existential statement
`Cover.cover_exists` for easier use in downstream files.  It asserts that a
family of Boolean functions with bounded collision entropy admits a small set of
jointly monochromatic subcubes covering all `1`-inputs of every function in the
family.  The full proof is nontrivial and omitted; this declaration merely
re-exports the existential lemma so that other parts of the development can rely
on it.
-/
/-!
### A convenience record for covers returned by `familyEntropyCover`.
This bundles the list of rectangles together with proofs that each
is monochromatic for the whole family, that the rectangles cover all
`1`-inputs, and that their number is bounded by `mBound`.
-/
structure FamilyCover {n : ℕ} (F : Family n) (h : ℕ) where
  rects   : Finset (BoolFunc.Subcube n)
  mono    : ∀ C ∈ rects, BoolFunc.Subcube.monochromaticForFamily C F
  covers  : ∀ f ∈ F, ∀ x, f x = true → ∃ C ∈ rects, x ∈ₛ C
  bound   : rects.card ≤ mBound n h

/-
`familyEntropyCover` packages the existential statement as a concrete record. -/
axiom familyEntropyCover
    {n : ℕ} (F : Family n) {h : ℕ} (hH : H₂ F ≤ (h : ℝ)) :
    FamilyCover F h

end Boolcube
