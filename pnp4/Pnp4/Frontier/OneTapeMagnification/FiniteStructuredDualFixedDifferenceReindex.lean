import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualRankThresholdBridge

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Reindexing structured dual aliases by their fixed difference

The ordered Fourier-support pair `(left, right)` is equivalently described by
its symmetric difference `W = left ∆ right` and its left endpoint.  This file
performs that finite reindexing for the exact structured rank-weighted form.
It is entirely generic in the two coefficient functions.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanBoundedIndependenceFarTail
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge

namespace FiniteStructuredDualFixedDifferenceReindex

/-- The involutive shear which replaces an ordered pair by its symmetric
difference and left endpoint. -/
def fixedDifferencePairEquiv (α : Type*) [DecidableEq α] :
    (Finset α × Finset α) ≃ (Finset α × Finset α) :=
  (Equiv.prodShear (Equiv.refl (Finset α))
      (fun left =>
        (symmDiff_right_involutive left).toPerm
          (fun right : Finset α => left ∆ right))).trans
    (Equiv.prodComm (Finset α) (Finset α))

@[simp]
theorem fixedDifferencePairEquiv_apply
    {α : Type*} [DecidableEq α]
    (left right : Finset α) :
    fixedDifferencePairEquiv α (left, right) = (left ∆ right, left) :=
  rfl

@[simp]
theorem fixedDifferencePairEquiv_symm_apply
    {α : Type*} [DecidableEq α]
    (dual left : Finset α) :
    (fixedDifferencePairEquiv α).symm (dual, left) =
      (left, left ∆ dual) :=
  rfl

/-- All nonempty supports in the exact structured dual code. -/
def nonemptyStructuredDualSupports
    (n m : Nat) (hn : 0 < n) : Finset (Finset (Fin (2 ^ n))) := by
  classical
  exact Finset.univ.filter (fun dual =>
    dual.Nonempty ∧
      IsStructuredDualSupport n (structuredIndependence m) hn dual)

@[simp]
theorem mem_nonemptyStructuredDualSupports
    (n m : Nat) (hn : 0 < n)
    (dual : Finset (Fin (2 ^ n))) :
    dual ∈ nonemptyStructuredDualSupports n m hn ↔
      dual.Nonempty ∧
        IsStructuredDualSupport n (structuredIndependence m) hn dual := by
  classical
  simp [nonemptyStructuredDualSupports]

/-- Fixed-difference coordinates for the high/high distinct structured-dual
pair set.  The first coordinate is `W`; the second is the left support. -/
def structuredDualFixedDifferencePairs
    (n m cutoff : Nat) (hn : 0 < n) :
    Finset (Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) := by
  classical
  exact
    ((nonemptyStructuredDualSupports n m hn).product Finset.univ).filter
      (fun pair => highHighAlias cutoff pair.1 pair.2)

@[simp]
theorem mem_structuredDualFixedDifferencePairs
    (n m cutoff : Nat) (hn : 0 < n)
    (pair : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) :
    pair ∈ structuredDualFixedDifferencePairs n m cutoff hn ↔
      pair.1.Nonempty ∧
        IsStructuredDualSupport n (structuredIndependence m) hn pair.1 ∧
          highHighAlias cutoff pair.1 pair.2 := by
  classical
  simp [structuredDualFixedDifferencePairs, and_assoc]

/-- The shear restricts to a bijection between the existing ordered
structured-dual alias pairs and fixed-difference coordinates. -/
theorem fixedDifferencePairEquiv_mem_iff
    (n m cutoff : Nat) (hn : 0 < n)
    (pair : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) :
    fixedDifferencePairEquiv (Fin (2 ^ n)) pair ∈
        structuredDualFixedDifferencePairs n m cutoff hn ↔
      pair ∈ structuredDualAliasPairs n m cutoff hn := by
  classical
  rcases pair with ⟨left, right⟩
  rw [mem_structuredDualFixedDifferencePairs,
    mem_structuredDualAliasPairs_iff]
  simp only [fixedDifferencePairEquiv_apply]
  constructor
  · rintro ⟨hdifference, hdual, hhigh⟩
    refine ⟨mem_highDegreeSupports.mpr hhigh.1,
      mem_highDegreeSupports.mpr ?_,
      Finset.symmDiff_nonempty.mp hdifference, hdual⟩
    simpa only [symmDiff_symmDiff_cancel_left] using hhigh.2
  · rintro ⟨hleft, hright, hne, hdual⟩
    refine ⟨Finset.symmDiff_nonempty.mpr hne, hdual,
      mem_highDegreeSupports.mp hleft, ?_⟩
    simpa only [symmDiff_symmDiff_cancel_left] using
      (mem_highDegreeSupports.mp hright)

/-- Image form of the restricted fixed-difference bijection. -/
theorem structuredDualAliasPairs_map_fixedDifferencePairEquiv
    (n m cutoff : Nat) (hn : 0 < n) :
    (structuredDualAliasPairs n m cutoff hn).map
        (fixedDifferencePairEquiv (Fin (2 ^ n))).toEmbedding =
      structuredDualFixedDifferencePairs n m cutoff hn := by
  classical
  ext pair
  constructor
  · intro hpair
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_map.mp hpair
    exact (fixedDifferencePairEquiv_mem_iff
      n m cutoff hn source).2 hsource
  · intro hpair
    let source := (fixedDifferencePairEquiv (Fin (2 ^ n))).symm pair
    have hsource : source ∈ structuredDualAliasPairs n m cutoff hn := by
      apply (fixedDifferencePairEquiv_mem_iff n m cutoff hn source).1
      simpa [source] using hpair
    refine Finset.mem_map.mpr ⟨source, hsource, ?_⟩
    exact (fixedDifferencePairEquiv (Fin (2 ^ n))).apply_symm_apply pair

/-- Exact rank-weighted distinct-alias form, reindexed as an outer sum over
nonempty structured-dual differences and an inner fixed-difference
high/high convolution. -/
theorem structuredDualRankDistinctCrossForm_eq_sum_fixedDualRankWeightedHighHigh
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (leftFunction rightFunction : (Fin (2 ^ n) → Bool) → Rat) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction =
      ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
        weightedSelectedSum (highHighAlias cutoff dual)
          (fun left =>
            dyadicRankWeight
              (supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail (left ∪ (left ∆ dual))))
          (fun left =>
            coefficient leftFunction left *
              coefficient rightFunction (left ∆ dual)) := by
  classical
  rw [structuredDualRankDistinctCrossForm_eq_pairWeightedSum]
  let sourceTerm := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    dyadicRankWeight
        (structuredDualAliasPairRank n m tailBits hn htail pair) *
      structuredDualAliasPairCoefficient leftFunction rightFunction pair
  let targetTerm := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    dyadicRankWeight
        (supportPrefixConstraintRank n (structuredIndependence m)
          tailBits hn htail (pair.2 ∪ (pair.2 ∆ pair.1))) *
      (coefficient leftFunction pair.2 *
        coefficient rightFunction (pair.2 ∆ pair.1))
  calc
    (∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
        sourceTerm pair) =
        ∑ pair ∈
            (structuredDualAliasPairs n m cutoff hn).map
              (fixedDifferencePairEquiv (Fin (2 ^ n))).toEmbedding,
          targetTerm pair := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro pair _hpair
      rcases pair with ⟨left, right⟩
      simp [sourceTerm, targetTerm, structuredDualAliasPairRank,
        structuredDualAliasPairCoefficient]
    _ = ∑ pair ∈ structuredDualFixedDifferencePairs n m cutoff hn,
          targetTerm pair := by
      rw [structuredDualAliasPairs_map_fixedDifferencePairEquiv]
    _ = ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
          weightedSelectedSum (highHighAlias cutoff dual)
            (fun left =>
              dyadicRankWeight
                (supportPrefixConstraintRank n (structuredIndependence m)
                  tailBits hn htail (left ∪ (left ∆ dual))))
            (fun left =>
              coefficient leftFunction left *
                coefficient rightFunction (left ∆ dual)) := by
      unfold structuredDualFixedDifferencePairs weightedSelectedSum
      rw [Finset.sum_filter]
      calc
        (∑ pair ∈
            (nonemptyStructuredDualSupports n m hn).product Finset.univ,
              if highHighAlias cutoff pair.1 pair.2 then
                targetTerm pair else 0) =
            ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
              ∑ left ∈ Finset.univ,
                if highHighAlias cutoff dual left then
                  targetTerm (dual, left) else 0 := by
          exact Finset.sum_product
            (nonemptyStructuredDualSupports n m hn) Finset.univ
              (fun pair =>
                if highHighAlias cutoff pair.1 pair.2 then
                  targetTerm pair else 0)
        _ = _ := by rfl

/-- The cumulative actual-rank form admits the same fixed-difference
reindexing.  At each nonempty structured-dual `W`, it is exactly the
unweighted high/high convolution restricted to union rank at most `level`. -/
theorem structuredDualRankAtMostCrossForm_eq_sum_fixedDualRankAtMostHighHigh
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (leftFunction rightFunction : (Fin (2 ^ n) → Bool) → Rat)
    (level : Nat) :
    structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction level =
      ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
        selectedSum
          (fun left =>
            highHighAlias cutoff dual left ∧
              supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail (left ∪ (left ∆ dual)) ≤ level)
          (fun left =>
            coefficient leftFunction left *
              coefficient rightFunction (left ∆ dual)) := by
  classical
  unfold structuredDualRankAtMostCrossForm finiteRankAtMostSum
  let sourceTerm := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    if structuredDualAliasPairRank n m tailBits hn htail pair ≤ level then
      structuredDualAliasPairCoefficient leftFunction rightFunction pair
    else 0
  let targetTerm := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    if supportPrefixConstraintRank n (structuredIndependence m)
        tailBits hn htail (pair.2 ∪ (pair.2 ∆ pair.1)) ≤ level then
      coefficient leftFunction pair.2 *
        coefficient rightFunction (pair.2 ∆ pair.1)
    else 0
  calc
    (∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
        sourceTerm pair) =
        ∑ pair ∈
            (structuredDualAliasPairs n m cutoff hn).map
              (fixedDifferencePairEquiv (Fin (2 ^ n))).toEmbedding,
          targetTerm pair := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro pair _hpair
      rcases pair with ⟨left, right⟩
      simp [sourceTerm, targetTerm, structuredDualAliasPairRank,
        structuredDualAliasPairCoefficient]
    _ = ∑ pair ∈ structuredDualFixedDifferencePairs n m cutoff hn,
          targetTerm pair := by
      rw [structuredDualAliasPairs_map_fixedDifferencePairEquiv]
    _ = ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
          selectedSum
            (fun left =>
              highHighAlias cutoff dual left ∧
                supportPrefixConstraintRank n (structuredIndependence m)
                  tailBits hn htail (left ∪ (left ∆ dual)) ≤ level)
            (fun left =>
              coefficient leftFunction left *
                coefficient rightFunction (left ∆ dual)) := by
      unfold structuredDualFixedDifferencePairs selectedSum
      rw [Finset.sum_filter]
      calc
        (∑ pair ∈
            (nonemptyStructuredDualSupports n m hn).product Finset.univ,
              if highHighAlias cutoff pair.1 pair.2 then
                targetTerm pair else 0) =
            ∑ dual ∈ nonemptyStructuredDualSupports n m hn,
              ∑ left ∈ Finset.univ,
                if highHighAlias cutoff dual left then
                  targetTerm (dual, left) else 0 := by
          exact Finset.sum_product
            (nonemptyStructuredDualSupports n m hn) Finset.univ
              (fun pair =>
                if highHighAlias cutoff pair.1 pair.2 then
                  targetTerm pair else 0)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro dual _hdual
          apply Finset.sum_congr rfl
          intro left _hleft
          by_cases hhigh : highHighAlias cutoff dual left
          · by_cases hrank :
                supportPrefixConstraintRank n (structuredIndependence m)
                  tailBits hn htail (left ∪ (left ∆ dual)) ≤ level
            · simp [targetTerm, hhigh, hrank]
            · simp [targetTerm, hhigh, hrank]
          · simp [targetTerm, hhigh]

end FiniteStructuredDualFixedDifferenceReindex

end

end OneTapeMagnification
end Frontier
end Pnp4
