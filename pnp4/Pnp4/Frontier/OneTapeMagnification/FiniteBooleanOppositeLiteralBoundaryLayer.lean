import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralRankDerivative

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The off-coordinate opposite-literal cutoff boundary

For a fixed dual word which omits the queried coordinate, toggling that
coordinate adds one point to both Fourier supports.  Consequently a pair which
is not high/high before the toggle but is high/high afterwards lies on the
cutoff exactly: the smaller original support has cardinality `cutoff`.

For a nonempty structured dual word at independence degree `4m+1`, the dual
distance then forces the other support to have cardinality at least `2m+2`.
These are unconditional finite-cardinality statements.  They do not estimate
the Fourier coefficient carried by the boundary pair.
-/

noncomputable section

open scoped symmDiff

open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open FiniteBooleanBoundedIndependence
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteBooleanOppositeLiteralCorrelation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualFixedDifferenceReindex

namespace FiniteBooleanOppositeLiteralBoundaryLayer

private theorem coordinate_not_mem_fixedDualRight
    {N : Nat} (coordinate : Fin N) (W alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W) :
    coordinate ∉ alpha ∆ W := by
  simp only [Finset.mem_symmDiff]
  tauto

/-- If the off-coordinate toggle is high/high, both original supports already
have cardinality at least the cutoff. -/
theorem offCoordinate_toggledHigh_originalCards_ge
    {N : Nat} (coordinate : Fin N) (cutoff : Nat)
    (W alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (htoggled : highHighAlias cutoff W
      (toggleSupport coordinate alpha)) :
    cutoff ≤ alpha.card ∧ cutoff ≤ (alpha ∆ W).card := by
  have hcoordinateRight : coordinate ∉ alpha ∆ W :=
    coordinate_not_mem_fixedDualRight coordinate W alpha
      hcoordinateAlpha hcoordinateW
  unfold highHighAlias at htoggled
  rw [toggleSupport_symmDiff,
    toggleSupport_eq_insert_of_not_mem coordinate alpha hcoordinateAlpha,
    toggleSupport_eq_insert_of_not_mem coordinate (alpha ∆ W)
      hcoordinateRight] at htoggled
  simp only [Finset.card_insert_of_notMem hcoordinateAlpha,
    Finset.card_insert_of_notMem hcoordinateRight] at htoggled
  omega

/-- Exact boundary dichotomy: an off-coordinate pair which enters the
high/high tail under the toggle has at least one original endpoint exactly at
the cutoff. -/
theorem offCoordinate_newlyHigh_boundary
    {N : Nat} (coordinate : Fin N) (cutoff : Nat)
    (W alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (horiginal : ¬ highHighAlias cutoff W alpha)
    (htoggled : highHighAlias cutoff W
      (toggleSupport coordinate alpha)) :
    alpha.card = cutoff ∨ (alpha ∆ W).card = cutoff := by
  have hge := offCoordinate_toggledHigh_originalCards_ge
    coordinate cutoff W alpha hcoordinateAlpha hcoordinateW htoggled
  unfold highHighAlias at horiginal
  omega

/-- Equivalent minimum-cardinality form of the exact cutoff boundary. -/
theorem offCoordinate_newlyHigh_min_card_eq
    {N : Nat} (coordinate : Fin N) (cutoff : Nat)
    (W alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (horiginal : ¬ highHighAlias cutoff W alpha)
    (htoggled : highHighAlias cutoff W
      (toggleSupport coordinate alpha)) :
    min alpha.card (alpha ∆ W).card = cutoff := by
  have hge := offCoordinate_toggledHigh_originalCards_ge
    coordinate cutoff W alpha hcoordinateAlpha hcoordinateW htoggled
  rcases offCoordinate_newlyHigh_boundary coordinate cutoff W alpha
      hcoordinateAlpha hcoordinateW horiginal htoggled with
    halpha | hright
  · rw [halpha]
    exact Nat.min_eq_left hge.2
  · rw [hright]
    exact Nat.min_eq_right hge.1

/-- If the fixed difference has cardinality at least `2 * cutoff + 2`, the
endpoint not pinned to the cutoff has cardinality at least `cutoff + 2`.
This is the sharp consequence of the triangle bound
`card W ≤ card alpha + card (alpha ∆ W)`. -/
theorem offCoordinate_newlyHigh_boundary_split_of_dualDistance
    {N : Nat} (coordinate : Fin N) (cutoff : Nat)
    (W alpha : Finset (Fin N))
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (horiginal : ¬ highHighAlias cutoff W alpha)
    (htoggled : highHighAlias cutoff W
      (toggleSupport coordinate alpha))
    (hWcard : 2 * cutoff + 2 ≤ W.card) :
    (alpha.card = cutoff ∧ cutoff + 2 ≤ (alpha ∆ W).card) ∨
      ((alpha ∆ W).card = cutoff ∧ cutoff + 2 ≤ alpha.card) := by
  have hsum : W.card ≤ alpha.card + (alpha ∆ W).card := by
    simpa only [symmDiff_symmDiff_cancel_left] using
      (card_symmDiff_le_add alpha (alpha ∆ W))
  rcases offCoordinate_newlyHigh_boundary coordinate cutoff W alpha
      hcoordinateAlpha hcoordinateW horiginal htoggled with
    halpha | hright
  · left
    refine ⟨halpha, ?_⟩
    omega
  · right
    refine ⟨hright, ?_⟩
    omega

/-- A nonempty structured dual word has distance at least `4m+2`; hence every
new off-coordinate boundary pair at cutoff `2m` consists of one degree-`2m`
endpoint and an opposite endpoint of degree at least `2m+2`. -/
theorem structuredDual_offCoordinate_newlyHigh_boundary_split
    (n m : Nat) (hn : 0 < n)
    (coordinate : Fin (2 ^ n))
    (W alpha : Finset (Fin (2 ^ n)))
    (hW : W ∈ nonemptyStructuredDualSupports n m hn)
    (hcoordinateAlpha : coordinate ∉ alpha)
    (hcoordinateW : coordinate ∉ W)
    (horiginal : ¬ highHighAlias (2 * m) W alpha)
    (htoggled : highHighAlias (2 * m) W
      (toggleSupport coordinate alpha)) :
    (alpha.card = 2 * m ∧ 2 * m + 2 ≤ (alpha ∆ W).card) ∨
      ((alpha ∆ W).card = 2 * m ∧ 2 * m + 2 ≤ alpha.card) := by
  have hWdata := (mem_nonemptyStructuredDualSupports n m hn W).mp hW
  have hne : alpha ≠ alpha ∆ W := by
    intro heq
    have h := congrArg (fun support => alpha ∆ support) heq
    have hempty : (∅ : Finset (Fin (2 ^ n))) = W := by
      simpa only [symmDiff_self, symmDiff_symmDiff_cancel_left] using h
    exact hWdata.1.ne_empty hempty.symm
  have hdual : IsStructuredDualSupport n (structuredIndependence m) hn
      (alpha ∆ (alpha ∆ W)) := by
    simpa only [symmDiff_symmDiff_cancel_left] using hWdata.2
  have hfar : structuredIndependence m < W.card := by
    simpa only [symmDiff_symmDiff_cancel_left] using
      (structuredIndependence_lt_symmDiff_card_of_distinct_dual
        n m hn alpha (alpha ∆ W) hne hdual)
  have hWcard : 2 * (2 * m) + 2 ≤ W.card := by
    simp only [structuredIndependence] at hfar
    omega
  exact offCoordinate_newlyHigh_boundary_split_of_dualDistance
    coordinate (2 * m) W alpha hcoordinateAlpha hcoordinateW
      horiginal htoggled hWcard

end FiniteBooleanOppositeLiteralBoundaryLayer

end

end OneTapeMagnification
end Frontier
end Pnp4
