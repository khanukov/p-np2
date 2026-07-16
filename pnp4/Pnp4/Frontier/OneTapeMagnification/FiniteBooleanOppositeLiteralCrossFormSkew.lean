import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralCorrelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Skew symmetry of an on-coordinate opposite-literal cross form

For a fixed dual word `W` containing the queried coordinate, exchanging the
two coordinate-free residual factors negates the complete selected
opposite-literal cross form.  The proof reindexes Fourier supports by
`alpha ↦ alpha ∆ W`.  This involution preserves the high/high predicate and
the union-dependent weight, while the opposite query literals contribute one
sign change.

Unlike the pointwise bulk cancellation, this identity includes every
degree-cutoff boundary term.  It is finite and exact: the weight is arbitrary,
and no positivity, rank, structured-code, or correlation premise is used.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteBooleanOppositeLiteralCorrelation

namespace FiniteBooleanOppositeLiteralCrossFormSkew

/-- Toggling a Fourier support by one fixed dual word is an involution. -/
def fixedDualToggleEquiv {N : Nat} (W : Finset (Fin N)) :
    Finset (Fin N) ≃ Finset (Fin N) :=
  (symmDiff_left_involutive W).toPerm (fun alpha => alpha ∆ W)

@[simp]
theorem fixedDualToggleEquiv_apply {N : Nat} (W alpha : Finset (Fin N)) :
    fixedDualToggleEquiv W alpha = alpha ∆ W :=
  rfl

/-- The high/high cutoff predicate is invariant under exchanging the two
endpoints of a fixed-dual pair. -/
theorem highHighAlias_symmDiff_right_iff {N cutoff : Nat}
    (W alpha : Finset (Fin N)) :
    highHighAlias cutoff W (alpha ∆ W) ↔
      highHighAlias cutoff W alpha := by
  unfold highHighAlias
  rw [symmDiff_symmDiff_cancel_right]
  tauto

/-- If the fixed dual word contains the query coordinate, exchanging the two
Fourier endpoints negates the opposite-literal coefficient product after the
two residual factors are exchanged. -/
theorem oppositeLiteral_coefficientProduct_symmDiff_skew_of_mem
    {N : Nat} (coordinate : Fin N)
    (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (W alpha : Finset (Fin N))
    (hcoordinateW : coordinate ∈ W) :
    coefficient (falseLiteralPart coordinate a) (alpha ∆ W) *
        coefficient (trueLiteralPart coordinate b) alpha =
      -(coefficient (falseLiteralPart coordinate b) alpha *
        coefficient (trueLiteralPart coordinate a) (alpha ∆ W)) := by
  rw [coefficient_falseLiteralPart coordinate a ha,
    coefficient_trueLiteralPart coordinate b hb,
    coefficient_falseLiteralPart coordinate b hb,
    coefficient_trueLiteralPart coordinate a ha]
  by_cases hcoordinateAlpha : coordinate ∈ alpha
  · have hcoordinateToggled : coordinate ∉ alpha ∆ W := by
      simp [Finset.mem_symmDiff, hcoordinateAlpha, hcoordinateW]
    simp [hcoordinateAlpha, hcoordinateToggled]
    ring
  · have hcoordinateToggled : coordinate ∈ alpha ∆ W := by
      simp [Finset.mem_symmDiff, hcoordinateAlpha, hcoordinateW]
    simp [hcoordinateAlpha, hcoordinateToggled]
    ring

/-- Summand-level skew symmetry.  Reindexing by `alpha ∆ W` swaps the union
support and the two cutoff degrees, so the preceding coefficient sign is the
only change. -/
theorem oppositeLiteralFixedDualTerm_symmDiff_skew_of_mem
    {N : Nat} (coordinate : Fin N)
    (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (alpha : Finset (Fin N))
    (hcoordinateW : coordinate ∈ W) :
    oppositeLiteralFixedDualTerm coordinate a b cutoff W weight
        (alpha ∆ W) =
      -oppositeLiteralFixedDualTerm coordinate b a cutoff W weight alpha := by
  unfold oppositeLiteralFixedDualTerm
  by_cases hhigh : highHighAlias cutoff W alpha
  · have htoggled : highHighAlias cutoff W (alpha ∆ W) :=
      (highHighAlias_symmDiff_right_iff W alpha).2 hhigh
    rw [if_pos htoggled, if_pos hhigh,
      symmDiff_symmDiff_cancel_right, Finset.union_comm]
    rw [oppositeLiteral_coefficientProduct_symmDiff_skew_of_mem
      coordinate a b ha hb W alpha hcoordinateW]
    ring
  · have htoggled : ¬ highHighAlias cutoff W (alpha ∆ W) := by
      intro h
      exact hhigh ((highHighAlias_symmDiff_right_iff W alpha).1 h)
    simp [hhigh, htoggled]

/-- **Exact on-coordinate skew symmetry.**  For any cutoff and any
union-support weight, a fixed-dual opposite-literal cross form whose dual word
contains the query coordinate is skew-symmetric in its two coordinate-free
residual factors. -/
theorem oppositeLiteralFixedDualCrossForm_skew_of_mem
    {N : Nat} (coordinate : Fin N)
    (a b : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (hb : DependsOnlyOn (Finset.univ.erase coordinate) b)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (hcoordinateW : coordinate ∈ W) :
    oppositeLiteralFixedDualCrossForm coordinate a b cutoff W weight =
      -oppositeLiteralFixedDualCrossForm coordinate b a cutoff W weight := by
  rw [oppositeLiteralFixedDualCrossForm_eq_sum_term,
    oppositeLiteralFixedDualCrossForm_eq_sum_term]
  let term := oppositeLiteralFixedDualTerm
    coordinate a b cutoff W weight
  have hreindex :
      (∑ alpha : Finset (Fin N), term (alpha ∆ W)) =
        ∑ alpha : Finset (Fin N), term alpha := by
    simpa only [fixedDualToggleEquiv_apply] using
      (fixedDualToggleEquiv W).sum_comp term
  calc
    (∑ alpha : Finset (Fin N),
        oppositeLiteralFixedDualTerm coordinate a b cutoff W weight alpha) =
        ∑ alpha : Finset (Fin N), term (alpha ∆ W) := by
          exact hreindex.symm
    _ = ∑ alpha : Finset (Fin N),
          -oppositeLiteralFixedDualTerm
            coordinate b a cutoff W weight alpha := by
          apply Finset.sum_congr rfl
          intro alpha _
          exact oppositeLiteralFixedDualTerm_symmDiff_skew_of_mem
            coordinate a b ha hb cutoff W weight alpha hcoordinateW
    _ = -(∑ alpha : Finset (Fin N),
          oppositeLiteralFixedDualTerm
            coordinate b a cutoff W weight alpha) := by
          rw [Finset.sum_neg_distrib]

/-- With one common residual factor, every selected on-coordinate term,
including every cutoff-boundary term, cancels in the complete fixed-dual
cross form. -/
theorem oppositeLiteralFixedDualCrossForm_self_eq_zero_of_mem
    {N : Nat} (coordinate : Fin N)
    (a : (Fin N -> Bool) -> Rat)
    (ha : DependsOnlyOn (Finset.univ.erase coordinate) a)
    (cutoff : Nat) (W : Finset (Fin N))
    (weight : Finset (Fin N) -> Rat)
    (hcoordinateW : coordinate ∈ W) :
    oppositeLiteralFixedDualCrossForm coordinate a a cutoff W weight = 0 := by
  have hskew := oppositeLiteralFixedDualCrossForm_skew_of_mem
    coordinate a a ha ha cutoff W weight hcoordinateW
  linarith

end FiniteBooleanOppositeLiteralCrossFormSkew

end

end OneTapeMagnification
end Frontier
end Pnp4
