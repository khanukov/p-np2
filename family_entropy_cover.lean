import Boolcube
import Cover

namespace Boolcube

open Entropy
open Cover

/--
Family version of the collision entropy covering lemma.  The full proof
is nontrivial and currently omitted; this declaration serves as a
placeholder so that other parts of the development can depend on it.
-/
/--
`familyCollisionEntropyCover` wraps the existential statement `Cover.cover_exists`
for easier use in downstream files.  It asserts that a family of Boolean
functions with bounded collision entropy admits a small set of jointly
monochromatic subcubes covering all `1`‑inputs of every function in the family.
-/
theorem familyCollisionEntropyCover
  {n : ℕ} (F : Family n) {h : ℕ} (hH : H₂ F ≤ (h : ℝ)) :
  ∃ (T : Finset (Subcube n)),
    (∀ C ∈ T, Subcube.monochromaticForFamily C F) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ C, C ∈ T ∧ C.Mem x) ∧
    T.card ≤ mBound n h := by
  classical
  simpa using Cover.cover_exists (F := F) (h := h) hH

end Boolcube
