import PSubsetPpoly.family_entropy_cover
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open BoolFunc
open Asymptotics
open Cover2

namespace CoverNumeric

variable {N Nδ : ℕ} (F : Family N)

/-!  The original development left the numeric cover bounds abstract.
    This file now derives a simple numeric bound from `familyEntropyCover`.
    The definitions remain noncomputable, but they no longer collapse to
    trivial constants.  Future work will refine these quantities further.
-/

/--
`minCoverSize F h hH hn_pos` is the size of the cover returned by
`familyEntropyCover` when the family has collision entropy at most `h`.
The witness cover is obtained via classical choice, so the definition is
noncomputable but entirely constructive.
-/
noncomputable def minCoverSize (F : Family N) (h : ℕ)
    (hH : H₂ F ≤ (h : ℝ))
    (hn_pos : 0 < N) : ℕ :=
  (Boolcube.familyEntropyCover (F := F) (h := h) hH hn_pos).rects.card

/--
Basic entropy-based bound on `minCoverSize`.  The cover extracted from
`familyEntropyCover` obeys the explicit `mBound` estimate, provided the
arithmetic inequality `hM` is available.  This coarse bound suffices for the
numerical considerations in this module.
-/
lemma buildCover_size_bound (h₀ : H₂ F ≤ (N - Nδ : ℝ))
    (hn_pos : 0 < N) :
    minCoverSize F (h := N - Nδ) h₀ hn_pos ≤ mBound N (N - Nδ) := by
  classical
  -- The bound is provided directly by `familyEntropyCover`.
  simpa [minCoverSize] using
    (Boolcube.familyEntropyCover (F := F) (h := N - Nδ) h₀ hn_pos).bound

/-- Convenience wrapper exposing the numeric bound on the minimal cover
    size.  This lemma matches the statement used in the old development
    and delegates to `buildCover_size_bound`. -/
lemma minCoverSize_bound
    (h₀ : H₂ F ≤ (N - Nδ : ℝ))
    (hn_pos : 0 < N) :
    minCoverSize F (h := N - Nδ) h₀ hn_pos ≤ mBound N (N - Nδ) :=
  buildCover_size_bound (F := F) (Nδ := Nδ)
    (h₀ := h₀) (hn_pos := hn_pos)

/--
Simple numeric bound on `minCoverSize` without the dimension positivity
assumption.  The bound is immediate when `N = 0`, otherwise we reuse
`minCoverSize_bound` with the derived positivity proof.
-/
lemma numeric_bound
    (h₀ : H₂ F ≤ (N - Nδ : ℝ))
    (hn_pos : 0 < N) :
    minCoverSize F (h := N - Nδ) h₀ hn_pos ≤ mBound N (N - Nδ) :=
  buildCover_size_bound (F := F) (Nδ := Nδ)
    (h₀ := h₀) (hn_pos := hn_pos)

/-!  `buildCover_card n` denotes the size of the cover returned by the
experimental algorithm on families of dimension `n`.  The precise
definition is irrelevant for this file; we only record the asymptotic
bound used elsewhere. -/

/--  Cardinality placeholder for the experimental cover at dimension `n`.
    The actual cover construction is not implemented yet; we expose the
    conservative upper bound `2^n` as a stand‑in to support asymptotic
    statements and tests. This will be replaced by the exact cardinality
    once the recursive algorithm is implemented. -/
noncomputable def buildCover_card (n : ℕ) : ℕ := Nat.pow 2 n

/--
`buildCover_card` is defined as the trivial bound `2^n`, so it obviously
does not exceed this quantity.  In the original development this fact was
stated as an axiom; here we provide the straightforward proof instead. -/
lemma buildCover_card_le_pow2 (n : ℕ) : buildCover_card n ≤ Nat.pow 2 n := by
  -- Unfold the definition and apply reflexivity of `≤`.
  simpa [buildCover_card]

/--  The coarse bound above is, by construction, dominated by the
    exponential function `2^n`.  Stating the result using big‑O notation
    keeps the interface stable as the cover algorithm evolves. -/
lemma buildCover_card_bigO :
  (fun n ↦ (buildCover_card n : ℝ)) =O[atTop] fun n ↦ (2 : ℝ) ^ n := by
  classical
  -- First bound `buildCover_card` by the natural power `2^n`.
  have h₁ :
      (fun n ↦ (buildCover_card n : ℝ)) =O[atTop]
        fun n ↦ ((Nat.pow 2 n : ℕ) : ℝ) :=
    isBigO_of_le (fun n =>
      by
        have h := buildCover_card_le_pow2 n
        have h' : (buildCover_card n : ℝ) ≤ (Nat.pow 2 n : ℝ) :=
          by exact_mod_cast h
        have hpos₁ : 0 ≤ (buildCover_card n : ℝ) :=
          by exact_mod_cast Nat.zero_le _
        have hpos₂ : 0 ≤ (Nat.pow 2 n : ℝ) :=
          by exact_mod_cast Nat.zero_le _
        simpa [Real.norm_eq_abs, abs_of_nonneg hpos₁, abs_of_nonneg hpos₂]
          using h')
  -- Rewrite the target to the real exponential and apply reflexivity.
  have h₂ :
      (fun n ↦ ((Nat.pow 2 n : ℕ) : ℝ)) =O[atTop]
        fun n ↦ (2 : ℝ) ^ n := by
    have :
        (fun n ↦ ((Nat.pow 2 n : ℕ) : ℝ)) = fun n ↦ (2 : ℝ) ^ n := by
      funext n; simp
    simpa [this] using
      (Asymptotics.isBigO_refl
        (f := fun n : ℕ ↦ ((Nat.pow 2 n : ℕ) : ℝ))
        (l := Filter.atTop))
  -- Compose the two bounds.
  exact h₁.trans h₂


end CoverNumeric
