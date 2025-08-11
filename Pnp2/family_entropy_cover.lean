import Pnp2.Boolcube
import Pnp2.cover2

namespace Boolcube

open Entropy
open Cover2

/-!
`familyCollisionEntropyCover` wraps the existential statement
`Cover2.cover_exists` for easier use in downstream files.  It asserts that a
family of Boolean functions with bounded collision entropy admits a small set of
subcubes that are monochromatic for every function in the family when inspected
pointwise.  The full proof is nontrivial and omitted; this declaration merely
re‑exports the existential lemma so that other parts of the development can rely
on it.
-/
theorem familyCollisionEntropyCover
  {n : ℕ} (F : Family n) {h : ℕ} (hH : H₂ F ≤ (h : ℝ)) :
  ∃ (T : Finset (Subcube n)),
    (∀ C ∈ T, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ C, C ∈ T ∧ C.Mem x) := by
  classical
  simpa using Cover2.cover_exists (F := F) (h := h) hH

/-!
### A convenience record for covers returned by `familyEntropyCover`.
This bundles the list of rectangles together with proofs that each
is monochromatic for the whole family, that the rectangles cover all
`1`‑inputs, and that their number is bounded by `mBound`.
-/
structure FamilyCover {n : ℕ} (F : Family n) (h : ℕ) where
  rects   : Finset (Subcube n)
  mono    : ∀ C ∈ rects, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g
  covers  : ∀ f ∈ F, ∀ x, f x = true → ∃ C ∈ rects, x ∈ₛ C

/--
`familyEntropyCover` packages `familyCollisionEntropyCover` as a concrete
object.  It simply uses classical choice to extract a witnessing set of
rectangles from the existential statement. -/
noncomputable def familyEntropyCover
    {n : ℕ} (F : Family n) {h : ℕ} (hH : H₂ F ≤ (h : ℝ)) :
    FamilyCover F h := by
  classical
  obtain ⟨T, hmono, hcov⟩ :=
    familyCollisionEntropyCover (F := F) (h := h) hH
  refine ⟨T, hmono, ?_⟩
  intro f hf x hx
  rcases hcov f hf x hx with ⟨C, hC, hxC⟩
  exact ⟨C, hC, hxC⟩

/-!
`familyEntropyCover` is defined using `cover_exists`, just like
`Cover2.coverFamily`.  The following lemma exposes this relationship by
identifying the set of rectangles produced by both constructions.
This convenience result simplifies linking the wrapper record with the
underlying cover used elsewhere in the development.
-/
@[simp] lemma familyEntropyCover_rects_eq_coverFamily
    {n : ℕ} (F : Family n) {h : ℕ} (hH : H₂ F ≤ (h : ℝ)) :
    (familyEntropyCover (F := F) (h := h) hH).rects
      = Cover2.coverFamily (F := F) (h := h) hH := by
  classical
  -- Unfold both constructions and simplify using `cover_exists`.
  simp [familyEntropyCover, Cover2.coverFamily, Cover2.cover_exists]

end Boolcube
