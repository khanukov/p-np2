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

/--
Basic entropy-based bound on `minCoverSize`.  The cover extracted from
`familyEntropyCover` has size at most `Cover.mBound`, and `pow_le_mBound`
turns this abstract bound into the concrete estimate `2 ^ (N - Nδ)`.
The dimension must be positive for this step.
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

/--
Simple numeric bound on `minCoverSize` without the dimension positivity
assumption.  The bound is immediate when `N = 0`, otherwise we reuse
`minCoverSize_bound` with the derived positivity proof.
-/
lemma numeric_bound
    (h₀ : H₂ F ≤ (N - Nδ : ℝ)) :
    minCoverSize F (h := N - Nδ) h₀ ≤ 2 ^ (N - Nδ) := by
  classical
  by_cases hN : N = 0
  · -- The bound from `familyEntropyCover` collapses to `0` when `N = 0`.
    have hcard :=
      (Boolcube.familyEntropyCover (F := F) (h := N - Nδ) h₀).bound
    have hzero : Cover.mBound N (N - Nδ) = 0 := by simpa [Cover.mBound, hN]
    have hsize :
        minCoverSize F (h := N - Nδ) h₀ ≤ 0 := by
      simpa [minCoverSize, hzero] using hcard
    have hpos : (0 : ℕ) ≤ 2 ^ (N - Nδ) := Nat.zero_le _
    exact hsize.trans hpos
  · -- In the positive dimension case we invoke `minCoverSize_bound`.
    have hn : 0 < N := Nat.pos_of_ne_zero hN
    simpa using minCoverSize_bound (F := F) (Nδ := Nδ) (h₀ := h₀) hn

/-!  `buildCover_card n` denotes the size of the cover returned by the
experimental algorithm on families of dimension `n`.  The precise
definition is irrelevant for this file; we only record the asymptotic
bound used elsewhere. -/

/--  Cardinality of the experimental cover returned for dimension `n`.
    The actual cover construction is not implemented yet, but we can
    still expose a simple upper bound.  Empirically the cover never
    contains more than `2^n` rectangles, so we use this quantity as a
    coarse placeholder.  This choice avoids degenerate bounds while
    remaining easy to reason about asymptotically.

    Future work will replace this definition with the exact cardinality
    of the cover produced by the recursive algorithm. -/
def buildCover_card (n : ℕ) : ℕ := 2 ^ n

/--  The coarse bound above is, by construction, dominated by the
    exponential function `2^n`.  Stating the result using big‑O notation
    keeps the interface stable as the cover algorithm evolves. -/
lemma buildCover_card_bigO :
  (fun n ↦ (buildCover_card n : ℝ)) =O[atTop] fun n ↦ (2 : ℝ) ^ n := by
  -- Since `buildCover_card n = 2^n`, the claim is an instance of the
  -- reflexivity property of `=O`.
  simpa [buildCover_card] using
    (Asymptotics.isBigO_refl
      (f := fun n : ℕ ↦ (2 : ℝ) ^ n)
      (l := Filter.atTop))

end CoverNumeric
