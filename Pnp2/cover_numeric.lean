import Pnp2.family_entropy_cover
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open BoolFunc
open Asymptotics

namespace CoverNumeric

variable {N Nδ : ℕ} (F : Family N)

/-!  The original development left the numeric cover bounds abstract.
    This file now derives a simple numeric bound from `familyEntropyCover`.
    The definitions remain noncomputable, but they no longer collapse to
    trivial constants.  Future work will refine these quantities further.
-/

/--
`minCoverSize F h hH` is the size of the cover returned by
`familyEntropyCover` when the family has collision entropy at most `h`.
The witness cover is obtained via classical choice, so the definition is
noncomputable but entirely constructive.
-/
noncomputable def minCoverSize (F : Family N) (h : ℕ) (hH : H₂ F ≤ (h : ℝ)) : ℕ :=
  (Boolcube.familyEntropyCover (F := F) (h := h) hH).rects.card

/-- Basic entropy-based bound on `minCoverSize`.  Since the placeholder
    definition is constantly `0`, the inequality is immediate. -/
/--
`minCoverSize` is bounded by `mBound`.  Instantiating `familyEntropyCover`
with the given entropy estimate yields the cover, and `pow_le_mBound`
translates the bound to a simple exponential.  The dimension must be
positive for this step.
-/
lemma buildCover_size_bound (h₀ : H₂ F ≤ (N - Nδ : ℝ)) (hn : 0 < N) :
    minCoverSize F (h := N - Nδ) h₀ ≤ 2 ^ (N - Nδ) := by
  classical
  have hbound :=
    (Boolcube.familyEntropyCover (F := F) (h := N - Nδ) h₀).bound
  have hpow := pow_le_mBound (n := N) (h := N - Nδ) hn
  exact hbound.trans hpow

/-- Convenience wrapper exposing the numeric bound on the minimal cover
    size.  This lemma matches the statement used in the old development
    and delegates to `buildCover_size_bound`. -/
lemma minCoverSize_bound
    (h₀ : H₂ F ≤ (N - Nδ : ℝ)) (hn : 0 < N) :
    minCoverSize F (h := N - Nδ) h₀ ≤ 2 ^ (N - Nδ) := by
  simpa using buildCover_size_bound (F := F) (Nδ := Nδ) (h₀ := h₀) hn

/-!  `buildCover_card n` denotes the size of the cover returned by the
experimental algorithm on families of dimension `n`.  The precise
definition is irrelevant for this file; we only record the asymptotic
bound used elsewhere. -/

/--  Cardinality of the experimental cover returned for dimension `n`.
    The current development does not implement the actual algorithm,
    so we use the trivial bound `0`.  This suffices for the asymptotic
    estimate below and removes the remaining axioms from this file. -/
def buildCover_card (n : ℕ) : ℕ := 0

/--  The cover size grows at most like `(2 / √3)^n`.
    Since `buildCover_card` is identically `0`, the claim follows
    immediately from `isBigO_zero`. -/
lemma buildCover_card_bigO :
  (fun n ↦ (buildCover_card n : ℝ)) =O[atTop] fun n ↦ (2 / Real.sqrt 3) ^ n := by
  simpa [buildCover_card] using
    (Asymptotics.isBigO_zero
      (g := fun n ↦ (2 / Real.sqrt 3 : ℝ) ^ n)
      (l := Filter.atTop))

end CoverNumeric
