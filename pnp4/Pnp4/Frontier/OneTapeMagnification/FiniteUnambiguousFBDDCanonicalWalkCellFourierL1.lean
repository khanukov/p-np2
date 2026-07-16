import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanStructuredDualFourierL1
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralCrossFormSkew
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDCanonicalWalkCellEnergyPacking

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fourier-L1 control of canonical-walk suffix cells

A fixed canonical-walk cell is a (possibly empty) Boolean subcube.  The
slightly delicate point is that a bare query edge need not determine its
label when the false and true successors coincide.  We therefore do not
identify the cell with the cylinder fixing every label of the bare walk.
Instead, a nonempty cell is split into the compatibility cylinder of a fixed
prefix walk and the fixed-labelled cylinder of the remaining suffix.

Fourier `L1` is submultiplicative under pointwise products.  Fixed-walk
compatibility is itself a product of unary edge cylinders, so it has Fourier
`L1` at most one.  The suffix cylinder has Fourier `L1` exactly one by
`FiniteBooleanStructuredDualFourierL1`.  This gives the requested cell bound
and, by the structured-dual `L1` endpoint, a dual-word-free bound for one
actual pair of realized canonical cells.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteBooleanOppositeLiteralCrossFormSkew
open FiniteBooleanStructuredDualFourierL1
open FiniteRankWeightAbelVariation
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredMaskRank
open DPTWStructuredUnbiasedDualCode
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge

namespace FiniteUnambiguousFBDD

/-! ## Generic coordinate cylinders -/

/-- The rational indicator that an input agrees with a reference assignment
on a fixed set of coordinates. -/
def ratCoordinateCylinderIndicator {N : Nat}
    (support : Finset (Fin N)) (reference input : Fin N -> Bool) : Rat :=
  if restrictAssignment support input =
      restrictAssignment support reference then 1 else 0

theorem ratCoordinateCylinderIndicator_dependsOnlyOn {N : Nat}
    (support : Finset (Fin N)) (reference : Fin N -> Bool) :
    DependsOnlyOn support
      (ratCoordinateCylinderIndicator support reference) := by
  intro left right hagrees
  unfold ratCoordinateCylinderIndicator
  have hrestrict : restrictAssignment support left =
      restrictAssignment support right := by
    funext coordinate
    exact hagrees coordinate coordinate.property
  rw [hrestrict]

theorem coefficient_ratCoordinateCylinderIndicator_eq_character_div
    {N : Nat} (support : Finset (Fin N)) (reference : Fin N -> Bool)
    (frequency : Finset (Fin N)) (hfrequency : frequency ⊆ support) :
    coefficient (ratCoordinateCylinderIndicator support reference) frequency =
      character frequency reference / (2 : Rat) ^ support.card := by
  classical
  let complement := Finset.univ \ support
  have hdisjoint : Disjoint support complement := by
    simp [complement, Finset.disjoint_left]
  have hcover : support ∪ complement = Finset.univ := by
    simp [complement]
  let localSupport := localizeSupport support frequency
  have hlift : liftLocalSupport support localSupport = frequency := by
    dsimp only [localSupport]
    rw [liftLocalSupport_localizeSupport]
    exact Finset.inter_eq_left.mpr hfrequency
  have hlocal := coefficient_eq_localCoefficient_left_of_partition
    (ratCoordinateCylinderIndicator_dependsOnlyOn support reference)
    hdisjoint hcover localSupport
  rw [hlift] at hlocal
  rw [hlocal]
  unfold localCoefficient
  let referenceLocal := restrictAssignment support reference
  have hcylinder (input : LocalAssignment support) :
      ratCoordinateCylinderIndicator support reference
          (extendAssignment support input) =
        if input = referenceLocal then 1 else 0 := by
    unfold ratCoordinateCylinderIndicator
    rw [restrictAssignment_extendAssignment]
  have hsum :
      (∑ input : LocalAssignment support,
        ratCoordinateCylinderIndicator support reference
            (extendAssignment support input) *
          localCharacter localSupport input) =
        localCharacter localSupport referenceLocal := by
    calc
      _ = ratCoordinateCylinderIndicator support reference
            (extendAssignment support referenceLocal) *
          localCharacter localSupport referenceLocal := by
            apply Fintype.sum_eq_single referenceLocal
            intro input hne
            rw [hcylinder]
            simp [hne]
      _ = _ := by
        rw [hcylinder]
        simp
  rw [hsum]
  have hcharacter := character_liftLocalSupport localSupport reference
  rw [hlift] at hcharacter
  rw [hcharacter]

theorem abs_coefficient_ratCoordinateCylinderIndicator_eq_inv_pow
    {N : Nat} (support : Finset (Fin N)) (reference : Fin N -> Bool)
    (frequency : Finset (Fin N)) (hfrequency : frequency ⊆ support) :
    abs (coefficient (ratCoordinateCylinderIndicator support reference)
      frequency) = 1 / (2 : Rat) ^ support.card := by
  rw [coefficient_ratCoordinateCylinderIndicator_eq_character_div
    support reference frequency hfrequency, abs_div, abs_character_eq_one]
  rw [abs_of_nonneg (by positivity :
    (0 : Rat) ≤ (2 : Rat) ^ support.card)]

/-- Every nonempty coordinate cylinder has Fourier `L1` exactly one. -/
theorem fourierL1_ratCoordinateCylinderIndicator_eq_one
    {N : Nat} (support : Finset (Fin N)) (reference : Fin N -> Bool) :
    fourierL1 (ratCoordinateCylinderIndicator support reference) = 1 := by
  classical
  have hcoefficient (frequency : Finset (Fin N)) :
      abs (coefficient
          (ratCoordinateCylinderIndicator support reference) frequency) =
        if frequency ⊆ support then
          1 / (2 : Rat) ^ support.card
        else 0 := by
    by_cases hfrequency : frequency ⊆ support
    · rw [if_pos hfrequency]
      exact abs_coefficient_ratCoordinateCylinderIndicator_eq_inv_pow
        support reference frequency hfrequency
    · rw [if_neg hfrequency]
      have hzero : coefficient
          (ratCoordinateCylinderIndicator support reference) frequency = 0 :=
        coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
          (ratCoordinateCylinderIndicator_dependsOnlyOn support reference)
          hfrequency
      rw [hzero, abs_zero]
  unfold fourierL1
  simp_rw [hcoefficient]
  calc
    (∑ frequency : Finset (Fin N),
        if frequency ⊆ support then
          1 / (2 : Rat) ^ support.card
        else 0) =
      ∑ frequency ∈ support.powerset,
        1 / (2 : Rat) ^ support.card := by
          rw [← Finset.sum_filter]
          congr 1
          ext frequency
          simp
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_powerset]
      simp only [nsmul_eq_mul]
      have hpow : (0 : Rat) < (2 : Rat) ^ support.card := by positivity
      field_simp

/-! ## Fourier-L1 submultiplicativity -/

/-- The Walsh `L1` norm is submultiplicative for pointwise products. -/
theorem fourierL1_mul_le {N : Nat}
    (left right : (Fin N -> Bool) -> Rat) :
    fourierL1 (fun input => left input * right input) ≤
      fourierL1 left * fourierL1 right := by
  classical
  unfold fourierL1
  simp_rw [coefficient_mul_eq_symmDiff_convolution]
  calc
    (∑ difference : Finset (Fin N),
        abs (∑ frequency : Finset (Fin N),
          coefficient left frequency *
            coefficient right (frequency ∆ difference))) ≤
      ∑ difference : Finset (Fin N),
        ∑ frequency : Finset (Fin N),
          abs (coefficient left frequency *
            coefficient right (frequency ∆ difference)) := by
          apply Finset.sum_le_sum
          intro difference _
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ frequency : Finset (Fin N),
        ∑ difference : Finset (Fin N),
          abs (coefficient left frequency *
            coefficient right (frequency ∆ difference)) := by
          rw [Finset.sum_comm]
    _ = ∑ frequency : Finset (Fin N),
        abs (coefficient left frequency) *
          ∑ rightFrequency : Finset (Fin N),
            abs (coefficient right rightFrequency) := by
          apply Finset.sum_congr rfl
          intro frequency _
          have htoggle :
              (∑ difference : Finset (Fin N),
                  abs (coefficient right (frequency ∆ difference))) =
                ∑ rightFrequency : Finset (Fin N),
                  abs (coefficient right rightFrequency) := by
            simpa only [fixedDualToggleEquiv_apply, symmDiff_comm] using
              (fixedDualToggleEquiv frequency).sum_comp
                (fun rightFrequency : Finset (Fin N) =>
                  abs (coefficient right rightFrequency))
          simp_rw [abs_mul]
          rw [← Finset.mul_sum, htoggle]
    _ = (∑ frequency : Finset (Fin N),
          abs (coefficient left frequency)) *
        ∑ rightFrequency : Finset (Fin N),
          abs (coefficient right rightFrequency) := by
          rw [Finset.sum_mul]

/-! ## Fixed-walk compatibility cylinders -/

/-- Rational indicator that one fixed graph edge is compatible with the
current input. -/
noncomputable def ratCompatibleEdgeIndicator {N : Nat}
    (B : FiniteUnambiguousFBDD N)
    (source target : B.Vertex) (input : Fin N -> Bool) : Rat :=
  by
    classical
    exact if B.CompatibleEdge input source target then 1 else 0

/-- Every actual graph edge imposes either no input condition or one unary
literal, hence its Fourier `L1` norm is one. -/
theorem fourierL1_ratCompatibleEdgeIndicator_eq_one
    {N : Nat} (B : FiniteUnambiguousFBDD N)
    {source target : B.Vertex} (edge : B.Edge source target) :
    fourierL1 (B.ratCompatibleEdgeIndicator source target) = 1 := by
  classical
  cases hnode : B.node source with
  | query queryIndex ifFalse ifTrue =>
      have hedge : target = ifFalse ∨ target = ifTrue := by
        simpa [FiniteUnambiguousFBDD.Edge,
          FiniteUFBDDNode.HasChild, hnode] using edge
      by_cases hsame : ifFalse = ifTrue
      · have htarget : target = ifFalse := by
          rcases hedge with h | h
          · exact h
          · exact h.trans hsame.symm
        have hfunction : B.ratCompatibleEdgeIndicator source target =
            ratCoordinateCylinderIndicator (∅ : Finset (Fin N))
              (fun _ => false) := by
          funext input
          unfold ratCompatibleEdgeIndicator ratCoordinateCylinderIndicator
          have hempty : restrictAssignment (∅ : Finset (Fin N)) input =
              restrictAssignment ∅ (fun _ => false) :=
            Subsingleton.elim _ _
          rw [if_pos hempty]
          cases hinput : input queryIndex <;>
            simp [CompatibleEdge, hnode, htarget, hsame, hinput]
        rw [hfunction,
          fourierL1_ratCoordinateCylinderIndicator_eq_one]
      · rcases hedge with htarget | htarget
        · have hfunction : B.ratCompatibleEdgeIndicator source target =
              ratCoordinateCylinderIndicator {queryIndex}
                (fun _ => false) := by
            funext input
            unfold ratCompatibleEdgeIndicator
              ratCoordinateCylinderIndicator
            subst target
            cases hinput : input queryIndex <;>
              simp [CompatibleEdge, hnode, hsame, hinput,
                restrictAssignment, funext_iff]
          rw [hfunction,
            fourierL1_ratCoordinateCylinderIndicator_eq_one]
        · have hfunction : B.ratCompatibleEdgeIndicator source target =
              ratCoordinateCylinderIndicator {queryIndex}
                (fun _ => true) := by
            funext input
            unfold ratCompatibleEdgeIndicator
              ratCoordinateCylinderIndicator
            subst target
            cases hinput : input queryIndex <;>
              simp [CompatibleEdge, hnode, Ne.symm hsame, hinput,
                restrictAssignment, funext_iff]
          rw [hfunction,
            fourierL1_ratCoordinateCylinderIndicator_eq_one]
  | choice children =>
      have hedge : target ∈ children := by
        simpa [FiniteUnambiguousFBDD.Edge,
          FiniteUFBDDNode.HasChild, hnode] using edge
      have hfunction : B.ratCompatibleEdgeIndicator source target =
          ratCoordinateCylinderIndicator (∅ : Finset (Fin N))
            (fun _ => false) := by
        funext input
        unfold ratCompatibleEdgeIndicator ratCoordinateCylinderIndicator
        have hempty : restrictAssignment (∅ : Finset (Fin N)) input =
            restrictAssignment ∅ (fun _ => false) :=
          Subsingleton.elim _ _
        rw [if_pos hempty]
        simp [CompatibleEdge, hnode, hedge]
      rw [hfunction, fourierL1_ratCoordinateCylinderIndicator_eq_one]
  | sink =>
      simp [FiniteUnambiguousFBDD.Edge,
        FiniteUFBDDNode.HasChild, hnode] at edge

/-- Rational indicator of compatibility with one fixed bare walk. -/
noncomputable def Walk.ratCompatibilityIndicator {N : Nat}
    {B : FiniteUnambiguousFBDD N} {source target : B.Vertex}
    (walk : B.Walk source target) (input : Fin N -> Bool) : Rat :=
  by
    classical
    exact if walk.Compatible input then 1 else 0

/-- Compatibility with a fixed walk is a product of unary edge cylinders,
so its Fourier `L1` norm is at most one.  No read-once premise is needed:
submultiplicativity also covers repeated or contradictory literals. -/
theorem Walk.fourierL1_ratCompatibilityIndicator_le_one
    {N : Nat} {B : FiniteUnambiguousFBDD N}
    {source target : B.Vertex} (walk : B.Walk source target) :
    fourierL1 walk.ratCompatibilityIndicator ≤ 1 := by
  induction walk with
  | nil vertex =>
      have hfunction :
          (Walk.nil vertex).ratCompatibilityIndicator =
            ratCoordinateCylinderIndicator (∅ : Finset (Fin N))
              (fun _ => false) := by
        funext input
        unfold Walk.ratCompatibilityIndicator
          ratCoordinateCylinderIndicator
        have hempty : restrictAssignment (∅ : Finset (Fin N)) input =
            restrictAssignment ∅ (fun _ => false) :=
          Subsingleton.elim _ _
        rw [if_pos hempty]
        simp [Walk.Compatible]
      rw [hfunction, fourierL1_ratCoordinateCylinderIndicator_eq_one]
  | @cons source middle target edge tail ih =>
      have hfunction :
          (Walk.cons edge tail).ratCompatibilityIndicator =
            fun input =>
              B.ratCompatibleEdgeIndicator source middle input *
                tail.ratCompatibilityIndicator input := by
        funext input
        unfold Walk.ratCompatibilityIndicator ratCompatibleEdgeIndicator
        by_cases hhead : B.CompatibleEdge input source middle <;>
          by_cases htail : tail.Compatible input <;>
          simp [Walk.Compatible, hhead, htail]
      rw [hfunction]
      calc
        fourierL1 (fun input =>
            B.ratCompatibleEdgeIndicator source middle input *
              tail.ratCompatibilityIndicator input) ≤
          fourierL1 (B.ratCompatibleEdgeIndicator source middle) *
            fourierL1 tail.ratCompatibilityIndicator :=
              fourierL1_mul_le _ _
        _ ≤ 1 := by
          rw [fourierL1_ratCompatibleEdgeIndicator_eq_one B edge]
          simpa using ih

/-! ## Canonical-walk cell cylinders -/

private theorem Walk.inputLabelledFullTrace_length_eq
    {N : Nat} {B : FiniteUnambiguousFBDD N}
    {source target : B.Vertex} (walk : B.Walk source target)
    (left right : Fin N -> Bool) :
    (walk.inputLabelledFullTrace left).length =
      (walk.inputLabelledFullTrace right).length := by
  induction walk with
  | nil vertex => rfl
  | cons edge tail ih =>
      simp [Walk.inputLabelledFullTrace, ih]

/-- Once a nonempty cell supplies a reference input, the cell is exactly the
product of a fixed-prefix compatibility cylinder and one fixed-labelled
suffix cylinder. -/
theorem canonicalWalkSuffixConeCellIndicator_eq_prefixCompatibility_mul_suffixCylinder
    {N : Nat} (B : FiniteUnambiguousFBDD N)
    (hUnambiguous : B.IsUnambiguous)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept)
    (reference : Fin N -> Bool)
    (hreference : B.IsCanonicalWalkSuffixConeCellInput key walk reference) :
    ∃ vertex : B.Vertex,
      ∃ prefixWalk : B.Walk B.start vertex,
        ∃ suffixWalk : B.Walk vertex B.accept,
          walk = prefixWalk.append suffixWalk ∧
            B.canonicalWalkSuffixConeCellIndicator key walk =
              fun input =>
                prefixWalk.ratCompatibilityIndicator input *
                  ratFixedLabelledSuffixCylinderIndicator
                    suffixWalk reference input := by
  classical
  rcases Walk.exists_split_of_isSuffix_inputLabelledFullTrace
      walk reference key hreference.2 with
    ⟨vertex, prefixWalk, suffixWalk, hsplit, hreferenceTrace⟩
  refine ⟨vertex, prefixWalk, suffixWalk, hsplit, ?_⟩
  funext input
  rw [B.canonicalWalkSuffixConeCellIndicator_eq_compatibleSuffixIndicator
    hUnambiguous]
  unfold canonicalWalkSuffixConeCellMembershipIndicator
    Walk.ratCompatibilityIndicator
    ratFixedLabelledSuffixCylinderIndicator
  have hreferenceAppend :
      (prefixWalk.append suffixWalk).Compatible reference := by
    simpa [← hsplit] using hreference.1
  have hreferenceParts :
      prefixWalk.Compatible reference ∧ suffixWalk.Compatible reference :=
    (Walk.compatible_append reference prefixWalk suffixWalk).1
      hreferenceAppend
  have hsuffixAtInput :
      suffixWalk.inputLabelledFullTrace input <:+
        walk.inputLabelledFullTrace input := by
    rw [hsplit, Walk.inputLabelledFullTrace_append]
    exact ⟨prefixWalk.inputLabelledFullTrace input, rfl⟩
  have hcellIff :
      B.IsCanonicalWalkSuffixConeCellInput key walk input ↔
        prefixWalk.Compatible input ∧
          suffixWalk.inputLabelledFullTrace input =
            suffixWalk.inputLabelledFullTrace reference := by
    constructor
    · intro hcell
      have hparts : prefixWalk.Compatible input ∧
          suffixWalk.Compatible input := by
        apply (Walk.compatible_append input prefixWalk suffixWalk).1
        simpa [← hsplit] using hcell.1
      refine ⟨hparts.1, ?_⟩
      have hlength : key.length =
          (suffixWalk.inputLabelledFullTrace input).length := by
        calc
          key.length =
              (suffixWalk.inputLabelledFullTrace reference).length := by
                rw [hreferenceTrace]
          _ = (suffixWalk.inputLabelledFullTrace input).length :=
            suffixWalk.inputLabelledFullTrace_length_eq reference input
      have hkeyDrop := (List.suffix_iff_eq_drop.mp hcell.2)
      have hsuffixDrop := (List.suffix_iff_eq_drop.mp hsuffixAtInput)
      rw [hlength] at hkeyDrop
      exact (hsuffixDrop.trans hkeyDrop.symm).trans hreferenceTrace.symm
    · rintro ⟨hprefix, htrace⟩
      have hagrees : ∀ queryIndex,
          queryIndex ∈ suffixWalk.queryVars ->
            input queryIndex = reference queryIndex :=
        suffixWalk.eq_on_queryVars_of_inputLabelledQueryTrace_eq
          input reference
          (suffixWalk.inputLabelledQueryTrace_eq_of_inputLabelledFullTrace_eq
            input reference htrace)
      have hsuffixCompatible : suffixWalk.Compatible input :=
        (suffixWalk.compatible_iff_of_eq_on_queryVars hagrees).2
          hreferenceParts.2
      constructor
      · have happend :=
          (Walk.compatible_append input prefixWalk suffixWalk).2
            ⟨hprefix, hsuffixCompatible⟩
        simpa [← hsplit] using happend
      · refine ⟨prefixWalk.inputLabelledFullTrace input, ?_⟩
        rw [hsplit, Walk.inputLabelledFullTrace_append,
          htrace, hreferenceTrace]
  rw [hcellIff]
  by_cases hprefix : prefixWalk.Compatible input <;>
    by_cases htrace : suffixWalk.inputLabelledFullTrace input =
      suffixWalk.inputLabelledFullTrace reference <;>
      simp [hprefix, htrace]

private theorem fourierL1_zero {N : Nat} :
    fourierL1 (fun _ : Fin N -> Bool => (0 : Rat)) = 0 := by
  unfold fourierL1 coefficient
  simp

/-- Every realized canonical-walk suffix cell has Fourier `L1` at most one.
The cell may be empty for the selected suffix key; the nonempty case is the
product cylinder above. -/
theorem fourierL1_canonicalWalkSuffixConeCellIndicator_le_one_of_realized
    {N : Nat} (B : FiniteUnambiguousFBDD N)
    (hUnambiguous : B.IsUnambiguous)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept)
    (_hrealized : walk ∈ B.realizedCanonicalAcceptingWalks) :
    fourierL1 (B.canonicalWalkSuffixConeCellIndicator key walk) ≤ 1 := by
  classical
  by_cases hcell : ∃ reference : Fin N -> Bool,
      B.IsCanonicalWalkSuffixConeCellInput key walk reference
  · obtain ⟨reference, hreference⟩ := hcell
    obtain ⟨vertex, prefixWalk, suffixWalk, _hsplit, hfunction⟩ :=
      B.canonicalWalkSuffixConeCellIndicator_eq_prefixCompatibility_mul_suffixCylinder
        hUnambiguous key walk reference hreference
    rw [hfunction]
    calc
      fourierL1 (fun input =>
          prefixWalk.ratCompatibilityIndicator input *
            ratFixedLabelledSuffixCylinderIndicator
              suffixWalk reference input) ≤
        fourierL1 prefixWalk.ratCompatibilityIndicator *
          fourierL1 (fun input =>
            ratFixedLabelledSuffixCylinderIndicator
              suffixWalk reference input) := fourierL1_mul_le _ _
      _ ≤ 1 := by
        rw [fourierL1_ratFixedLabelledSuffixCylinderIndicator_eq_one]
        simpa using prefixWalk.fourierL1_ratCompatibilityIndicator_le_one
  · have hzero : B.canonicalWalkSuffixConeCellIndicator key walk =
        fun _ : Fin N -> Bool => (0 : Rat) := by
      funext input
      rw [B.canonicalWalkSuffixConeCellIndicator_eq_compatibleSuffixIndicator
        hUnambiguous]
      unfold canonicalWalkSuffixConeCellMembershipIndicator
      rw [if_neg]
      exact fun hinput => hcell ⟨input, hinput⟩
    rw [hzero, fourierL1_zero]
    norm_num

/-- Actual canonical-cell-pair endpoint.  One pair of realized cells pays
the full structured rank scale once, with no sum over dual words or Fourier
supports. -/
theorem abs_structuredDualRankDistinctCrossForm_canonicalWalkCells_le
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (hUnambiguous : B.IsUnambiguous)
    (leftKey rightKey : List (InputLabelledFullStep B))
    (leftWalk rightWalk : B.Walk B.start B.accept)
    (hleftRealized : leftWalk ∈ B.realizedCanonicalAcceptingWalks)
    (hrightRealized : rightWalk ∈ B.realizedCanonicalAcceptingWalks) :
    abs (structuredDualRankDistinctCrossForm
        n m tailBits cutoff hn htail
        (B.canonicalWalkSuffixConeCellIndicator leftKey leftWalk)
        (B.canonicalWalkSuffixConeCellIndicator rightKey rightWalk)) ≤
      dyadicRankWeight (structuredIndependence m * tailBits) := by
  apply abs_structuredDualRankDistinctCrossForm_le_baseWeight_of_fourierL1
  · exact B.fourierL1_canonicalWalkSuffixConeCellIndicator_le_one_of_realized
      hUnambiguous leftKey leftWalk hleftRealized
  · exact B.fourierL1_canonicalWalkSuffixConeCellIndicator_le_one_of_realized
      hUnambiguous rightKey rightWalk hrightRealized

end FiniteUnambiguousFBDD
end

end OneTapeMagnification
end Frontier
end Pnp4
