import Pnp2.cover

namespace Cover

open BoolFunc

variable {n : ℕ}

/-!
`buildCoverCompute` is a convenience wrapper around `Cover.buildCover`
that returns the resulting rectangles as a `List`.  The underlying
construction is identical to `buildCover`, so all previously proved
properties carry over to the list representation.
-/
noncomputable
partial def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  (buildCover (F := F) (h := h) hH).toList

/-- Specification of `buildCoverCompute`.  The list of rectangles covers
all `1`-inputs of every function in `F`, each rectangle is jointly
monochromatic, and the length of the list is bounded by `mBound`. -/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ f ∈ F, ∀ x, f x = true →
        ∃ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset, x ∈ₛ R) ∧
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤ mBound n h := by
  classical
  have hcov := buildCover_covers (F := F) (h := h) hH
  have hmono := buildCover_mono (F := F) (h := h) (hH := hH)
  have hcard := buildCover_card_bound (F := F) (h := h) (hH := hH)
  have hset :
      (buildCoverCompute (F := F) (h := h) hH).toFinset =
        buildCover (F := F) (h := h) hH := by
    simpa [buildCoverCompute] using
      (Finset.toList_toFinset (buildCover (F := F) (h := h) hH))
  have hlen :
      (buildCoverCompute (F := F) (h := h) hH).length =
        (buildCover (F := F) (h := h) hH).card := by
    simpa [buildCoverCompute] using
      (Finset.length_toList (buildCover (F := F) (h := h) hH))
  constructor
  · intro f hf x hx
    have := hcov f hf x hx
    rcases this with ⟨R, hR, hxR⟩
    refine ⟨R, ?_, hxR⟩
    simpa [hset] using hR
  constructor
  · intro R hR
    have hR' : R ∈ buildCover (F := F) (h := h) hH := by
      simpa [hset] using hR
    exact hmono R hR'
  · have := hcard
    simpa [hlen] using this

end Cover
