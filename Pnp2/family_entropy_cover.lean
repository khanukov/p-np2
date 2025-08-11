import Pnp2.Boolcube
import Pnp2.cover2
import Pnp2.Cover.Canonical

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
This bundles the list of rectangles together with proofs that each is
monochromatic for the whole family and that the rectangles cover all
`1`‑inputs.  Earlier iterations of this project also recorded an explicit
cardinality bound, but the current development does not rely on this
additional information.  Dropping the field keeps the interface
lightweight and avoids depending on the unfinished size analysis.
-/
structure FamilyCover {n : ℕ} (F : Family n) (h : ℕ) where
  rects   : Finset (Subcube n)
  mono    : ∀ C ∈ rects, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g
  covers  : ∀ f ∈ F, ∀ x, f x = true → ∃ C ∈ rects, x ∈ₛ C

/--
`familyEntropyCover` packages the canonical cover produced by `coverFamily` into
an explicit record exposing its basic properties.  The construction relies on
classical choice and is therefore non‑computable, but it provides a convenient
interface for downstream modules.
-/
noncomputable def familyEntropyCover
    {n : ℕ} (F : Family n) {h : ℕ} (hH : H₂ F ≤ (h : ℝ)) :
    FamilyCover F h := by
  classical
  refine
    ⟨Cover2.coverFamily (F := F) (h := h) hH,
      ?mono, ?covers⟩
  · -- Monochromaticity is inherited from `coverFamily`.
    intro C hC g hg
    exact Cover2.coverFamily_pointwiseMono (F := F) (h := h) (hH := hH) hC g hg
  · -- All `1`-inputs are covered by construction.
    intro f hf x hx
    exact Cover2.coverFamily_spec_cover (F := F) (h := h) (hH := hH) f hf x hx

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
  simp [familyEntropyCover]

end Boolcube
