import Pnp4.Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One-coordinate increments of the structured mask rank

Adding one truth-table coordinate contributes at most `tailBits` new binary
prefix constraints.  Consequently the corresponding inverse-rank mask weight
drops by at most its old value times `1 - 2^(-tailBits)`.

These are unconditional linear-algebraic properties of the existing
structured prefix-constraint map.  No selector or correlation premise is used.
-/

noncomputable section

open DPTWStructuredMaskRank
open FiniteRankWeightAbelVariation

namespace DPTWStructuredMaskRankInsertion

/-- Adding one support coordinate cannot decrease prefix-constraint rank. -/
theorem supportPrefixConstraintRank_le_insert
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) (coordinate : Fin (2 ^ n)) :
    supportPrefixConstraintRank n k tailBits hn htail support <=
      supportPrefixConstraintRank n k tailBits hn htail
        (insert coordinate support) := by
  exact supportPrefixConstraintRank_mono n k tailBits hn htail
    (Finset.subset_insert coordinate support)

set_option synthInstance.maxHeartbeats 100000 in
/-- Adding one support coordinate contributes at most `tailBits` independent
binary prefix constraints. -/
theorem supportPrefixConstraintRank_insert_le_add_tailBits
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) (coordinate : Fin (2 ^ n)) :
    supportPrefixConstraintRank n k tailBits hn htail
        (insert coordinate support) <=
      supportPrefixConstraintRank n k tailBits hn htail support + tailBits := by
  let large : Finset (Fin (2 ^ n)) := insert coordinate support
  let smallMap := supportPrefixConstraintMap n k tailBits hn htail support
  let largeMap := supportPrefixConstraintMap n k tailBits hn htail large
  have hsubset : support ⊆ large := by
    exact Finset.subset_insert coordinate support
  let restrictMap := prefixConstraintRestrictionMap tailBits hsubset
  let insertedIndex : large :=
    ⟨coordinate, Finset.mem_insert_self coordinate support⟩
  have hcomp : restrictMap.comp largeMap = smallMap := by
    exact prefixConstraintRestrictionMap_comp
      n k tailBits hn htail hsubset
  let splitRange : LinearMap.range largeMap →ₗ[ZMod 2]
      LinearMap.range smallMap × (Fin tailBits → ZMod 2) :=
    { toFun := fun value =>
        (⟨restrictMap value.1, by
            rcases value.2 with ⟨polynomial, hpolynomial⟩
            refine ⟨polynomial, ?_⟩
            have happly := congrArg (fun map => map polynomial) hcomp
            change restrictMap (largeMap polynomial) =
              smallMap polynomial at happly
            rw [hpolynomial] at happly
            exact happly.symm⟩,
          value.1 insertedIndex)
      map_add' := by
        intro left right
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
      map_smul' := by
        intro scalar value
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl }
  have hsplitInjective : Function.Injective splitRange := by
    intro left right hequal
    apply Subtype.ext
    funext largeIndex selected
    by_cases heq : largeIndex.1 = coordinate
    · have hlargeIndex : largeIndex = insertedIndex := Subtype.ext heq
      subst largeIndex
      exact congrArg (fun value => value.2 selected) hequal
    · have hsmall : largeIndex.1 ∈ support := by
        have hmem : largeIndex.1 ∈ insert coordinate support := by
          have hlarge := largeIndex.property
          change largeIndex.1 ∈ insert coordinate support at hlarge
          exact hlarge
        exact (Finset.mem_insert.mp hmem).resolve_left heq
      let smallIndex : support := ⟨largeIndex.1, hsmall⟩
      have hfirst :=
        congrArg (fun value => value.1.1 smallIndex selected) hequal
      simp [splitRange, restrictMap, prefixConstraintRestrictionMap,
        smallIndex] at hfirst
      exact hfirst
  have hfinrank :=
    LinearMap.finrank_le_finrank_of_injective hsplitInjective
  change supportPrefixConstraintRank n k tailBits hn htail large <=
    Module.finrank (ZMod 2)
      (LinearMap.range smallMap × (Fin tailBits → ZMod 2)) at hfinrank
  rw [Module.finrank_prod, Module.finrank_pi_fintype] at hfinrank
  simpa [supportPrefixConstraintRank, large, smallMap, largeMap] using hfinrank

/-- The complete one-coordinate rank-increment interval. -/
theorem supportPrefixConstraintRank_insert_bounds
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) (coordinate : Fin (2 ^ n)) :
    supportPrefixConstraintRank n k tailBits hn htail support <=
        supportPrefixConstraintRank n k tailBits hn htail
          (insert coordinate support) ∧
      supportPrefixConstraintRank n k tailBits hn htail
          (insert coordinate support) <=
        supportPrefixConstraintRank n k tailBits hn htail support + tailBits := by
  exact ⟨supportPrefixConstraintRank_le_insert
      n k tailBits hn htail support coordinate,
    supportPrefixConstraintRank_insert_le_add_tailBits
      n k tailBits hn htail support coordinate⟩

private theorem dyadicRankWeight_antitone
    {lower upper : Nat} (h : lower <= upper) :
    dyadicRankWeight upper <= dyadicRankWeight lower := by
  unfold dyadicRankWeight
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ (by norm_num : (0 : Rat) <= 2) h

private theorem dyadicRankWeight_add (left right : Nat) :
    dyadicRankWeight (left + right) =
      dyadicRankWeight left * dyadicRankWeight right := by
  unfold dyadicRankWeight
  rw [pow_add]
  field_simp

/-- Adding one coordinate decreases the dyadic survival weight by a
nonnegative amount, and the drop is at most the probability that at least one
of its `tailBits` constraints is live. -/
theorem dyadicRankWeight_sub_insert_bounds
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) (coordinate : Fin (2 ^ n)) :
    let oldRank := supportPrefixConstraintRank
      n k tailBits hn htail support
    let newRank := supportPrefixConstraintRank
      n k tailBits hn htail (insert coordinate support)
    0 <= dyadicRankWeight oldRank - dyadicRankWeight newRank ∧
      dyadicRankWeight oldRank - dyadicRankWeight newRank <=
        (1 - 1 / (2 : Rat) ^ tailBits) * dyadicRankWeight oldRank := by
  dsimp only
  let oldRank := supportPrefixConstraintRank
    n k tailBits hn htail support
  let newRank := supportPrefixConstraintRank
    n k tailBits hn htail (insert coordinate support)
  have hlower : oldRank <= newRank :=
    supportPrefixConstraintRank_le_insert
      n k tailBits hn htail support coordinate
  have hupper : newRank <= oldRank + tailBits :=
    supportPrefixConstraintRank_insert_le_add_tailBits
      n k tailBits hn htail support coordinate
  constructor
  · exact sub_nonneg.mpr (dyadicRankWeight_antitone hlower)
  · have hweightLower :
        dyadicRankWeight (oldRank + tailBits) <=
          dyadicRankWeight newRank :=
      dyadicRankWeight_antitone hupper
    rw [dyadicRankWeight_add] at hweightLower
    change dyadicRankWeight oldRank - dyadicRankWeight newRank <=
      (1 - dyadicRankWeight tailBits) * dyadicRankWeight oldRank
    nlinarith [dyadicRankWeight_nonneg oldRank]

end DPTWStructuredMaskRankInsertion
end

end OneTapeMagnification
end Frontier
end Pnp4
