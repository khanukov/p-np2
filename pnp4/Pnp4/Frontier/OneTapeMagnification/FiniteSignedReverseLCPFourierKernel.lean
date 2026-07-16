import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPTelescope
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fourier form of the signed reverse-LCP telescope

The signed mass in a canonical suffix cone is exactly the masked average of
the strict high-degree Fourier tail of the cone's accepted-point indicator.
This rewrites each local reverse-LCP square drop as a difference of structured
high-tail energies, without taking absolute values or losing the cancellation
between sibling cones.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanOneRoundFoolingBound
open FiniteLayeredQueryProgramFamily
open FiniteBooleanBoundedIndependenceFarTail
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode

namespace FiniteUnambiguousFBDD

namespace Walk

/-- Full input-labelled traces respect dependent walk concatenation. -/
theorem inputLabelledFullTrace_append {n : Nat}
    {B : FiniteUnambiguousFBDD n}
    {source middle target : B.Vertex}
    (prefixWalk : B.Walk source middle) (suffixWalk : B.Walk middle target)
    (input : Fin n -> Bool) :
    (prefixWalk.append suffixWalk).inputLabelledFullTrace input =
      prefixWalk.inputLabelledFullTrace input ++
        suffixWalk.inputLabelledFullTrace input := by
  induction prefixWalk with
  | nil vertex => rfl
  | cons edge tail ih =>
      simp [Walk.append, inputLabelledFullTrace, ih]

/-- Agreement on the variables queried by a fixed walk forces equality of
its full input-labelled edge trace. -/
theorem inputLabelledFullTrace_eq_of_eq_on_queryVars {n : Nat}
    {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (left right : Fin n -> Bool)
    (hagrees : ∀ queryIndex, queryIndex ∈ walk.queryVars ->
      left queryIndex = right queryIndex) :
    walk.inputLabelledFullTrace left =
      walk.inputLabelledFullTrace right := by
  induction walk with
  | nil vertex => rfl
  | @cons source middle target edge tail ih =>
      have htail : ∀ queryIndex, queryIndex ∈ tail.queryVars ->
          left queryIndex = right queryIndex := by
        intro queryIndex hquery
        apply hagrees queryIndex
        have htailEvent : ∃ sourceVertex,
            (sourceVertex, queryIndex) ∈ tail.queryEvents := by
          simpa [Walk.queryVars, Walk.queryTrace] using hquery
        have hwholeEvent :
            (∃ queryEvent,
                (B.node source).queryEvent? source =
                  some (queryEvent, queryIndex)) ∨
              ∃ sourceVertex,
                (sourceVertex, queryIndex) ∈ tail.queryEvents :=
          Or.inr htailEvent
        simpa [Walk.queryVars, Walk.queryTrace, Walk.queryEvents] using
          hwholeEvent
      have hi := ih htail
      cases hnode : B.node source with
      | query queryIndex ifFalse ifTrue =>
          have hhead : left queryIndex = right queryIndex := by
            apply hagrees queryIndex
            simp [Walk.queryVars, Walk.queryTrace, Walk.queryEvents, hnode,
              FiniteUFBDDNode.queryEvent?]
          simp [inputLabelledFullTrace, inputLabelledFullStep, hnode,
            hhead, hi]
      | choice children =>
          simp [inputLabelledFullTrace, inputLabelledFullStep, hnode, hi]
      | sink =>
          have hedgeFalse : False := by
            simp [FiniteUnambiguousFBDD.Edge,
              FiniteUFBDDNode.HasChild, hnode] at edge
          exact hedgeFalse.elim

end Walk

/-- The rational indicator of the accepted inputs whose canonical full trace
has `key` as a suffix. -/
noncomputable def canonicalResidualSuffixConeIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B)) (input : Fin n -> Bool) : Rat :=
  ∑ accepted : B.AcceptedModel,
    if key <:+ B.canonicalInputLabelledFullTrace accepted then
      B.ratAcceptedPointIndicator accepted input
    else 0

/-- Semantic membership in one canonical full-trace suffix cone. -/
def IsCanonicalResidualSuffixConeInput {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B)) (input : Fin n -> Bool) : Prop :=
  ∃ accepted : B.AcceptedModel,
    accepted.1 = input ∧
      key <:+ B.canonicalInputLabelledFullTrace accepted

/-- Rational cylinder indicator fixing the complete input-labelled trace of
one chosen suffix walk to that of a reference input. -/
noncomputable def ratFixedLabelledSuffixCylinderIndicator {n : Nat}
    {B : FiniteUnambiguousFBDD n} {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (reference input : Fin n -> Bool) :
    Rat := by
  classical
  exact if suffixWalk.inputLabelledFullTrace input =
      suffixWalk.inputLabelledFullTrace reference then 1 else 0

/-- The `{0,1}` indicator of semantic suffix-cone membership. -/
noncomputable def canonicalResidualSuffixConeMembershipIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B)) (input : Fin n -> Bool) : Rat := by
  classical
  exact if B.IsCanonicalResidualSuffixConeInput key input then 1 else 0

/-- The explicit accepted-point sum is the `{0,1}` indicator of semantic
suffix-cone membership. -/
theorem canonicalResidualSuffixConeIndicator_eq_membershipIndicator
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B)) (input : Fin n -> Bool) :
    B.canonicalResidualSuffixConeIndicator key input =
      B.canonicalResidualSuffixConeMembershipIndicator key input := by
  classical
  unfold canonicalResidualSuffixConeIndicator
    canonicalResidualSuffixConeMembershipIndicator
  by_cases hcone : B.IsCanonicalResidualSuffixConeInput key input
  · rcases hcone with ⟨accepted, hinput, hkey⟩
    rw [if_pos ⟨accepted, hinput, hkey⟩]
    calc
      (∑ other : B.AcceptedModel,
          if key <:+ B.canonicalInputLabelledFullTrace other then
            B.ratAcceptedPointIndicator other input
          else 0) =
        (if key <:+ B.canonicalInputLabelledFullTrace accepted then
          B.ratAcceptedPointIndicator accepted input
        else 0) := by
          apply Fintype.sum_eq_single accepted
          intro other hotherNe
          by_cases hotherKey :
              key <:+ B.canonicalInputLabelledFullTrace other
          · have hinputNe : input ≠ other.1 := by
              intro heq
              apply hotherNe
              apply Subtype.ext
              exact (hinput.trans heq).symm
            simp [hotherKey, ratAcceptedPointIndicator, hinputNe]
          · simp [hotherKey]
      _ = 1 := by simp [hkey, ratAcceptedPointIndicator, hinput]
  · rw [if_neg hcone]
    apply Finset.sum_eq_zero
    intro accepted _
    by_cases hkey : key <:+ B.canonicalInputLabelledFullTrace accepted
    · have hinputNe : input ≠ accepted.1 := by
        intro heq
        apply hcone
        exact ⟨accepted, heq.symm, hkey⟩
      simp [hkey, ratAcceptedPointIndicator, hinputNe]
    · simp [hkey]

/-- A suffix cone realized by a fixed canonical suffix is exactly the product
of compatible prefix reachability and the corresponding labelled suffix
cylinder.  Unambiguity is used only in the reverse implication, to identify
the accepting splice with the selected canonical walk. -/
theorem isCanonicalResidualSuffixConeInput_iff_prefix_and_fixedSuffix
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous) (reference : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk)
    (input : Fin n -> Bool) :
    B.IsCanonicalResidualSuffixConeInput
        (suffixWalk.inputLabelledFullTrace reference.1) input ↔
      B.HasCompatiblePrefix input vertex ∧
        suffixWalk.inputLabelledFullTrace input =
          suffixWalk.inputLabelledFullTrace reference.1 := by
  constructor
  · rintro ⟨accepted, hinput, hkey⟩
    subst input
    rcases Walk.exists_split_of_isSuffix_inputLabelledFullTrace
        (B.canonicalAcceptingWalk accepted) accepted.1
        (suffixWalk.inputLabelledFullTrace reference.1)
        (by simpa [canonicalInputLabelledFullTrace] using hkey) with
      ⟨cutVertex, prefixWalk, realizedSuffix,
        hsplit, hrealizedTrace⟩
    have hsuffixSigma :
        (⟨cutVertex, realizedSuffix⟩ : Walk.AnyWalkTo B B.accept) =
          ⟨vertex, suffixWalk⟩ :=
      Walk.anyWalkTo_eq_of_inputLabelledFullTrace_eq B.accept
        accepted.1 reference.1
        ⟨cutVertex, realizedSuffix⟩ ⟨vertex, suffixWalk⟩ hrealizedTrace
    cases hsuffixSigma
    constructor
    · exact B.hasCompatiblePrefix_of_hasCanonicalAcceptingSuffix
        accepted suffixWalk ⟨prefixWalk, hsplit⟩
    · exact hrealizedTrace
  · rintro ⟨hprefix, htrace⟩
    rcases hprefix with ⟨prefixWalk, hprefixCompatible⟩
    have hreferenceCompatible : suffixWalk.Compatible reference.1 :=
      B.compatible_of_hasCanonicalAcceptingSuffix
        reference suffixWalk hreferenceSuffix
    have hagrees : ∀ queryIndex,
        queryIndex ∈ suffixWalk.queryVars ->
          input queryIndex = reference.1 queryIndex :=
      suffixWalk.eq_on_queryVars_of_inputLabelledQueryTrace_eq
        input reference.1
        (suffixWalk.inputLabelledQueryTrace_eq_of_inputLabelledFullTrace_eq
          input reference.1 htrace)
    have hsuffixCompatible : suffixWalk.Compatible input :=
      (suffixWalk.compatible_iff_of_eq_on_queryVars hagrees).2
        hreferenceCompatible
    have happendCompatible :
        (prefixWalk.append suffixWalk).Compatible input :=
      (Walk.compatible_append input prefixWalk suffixWalk).2
        ⟨hprefixCompatible, hsuffixCompatible⟩
    let accepted : B.AcceptedModel :=
      ⟨input, Nonempty.intro
        { walk := prefixWalk.append suffixWalk
          compatible := happendCompatible }⟩
    have hcanonical :
        B.canonicalAcceptingWalk accepted =
          prefixWalk.append suffixWalk :=
      B.canonicalAcceptingWalk_eq_of_compatible
        hUnambiguous accepted (prefixWalk.append suffixWalk) happendCompatible
    refine ⟨accepted, rfl, ?_⟩
    refine ⟨prefixWalk.inputLabelledFullTrace input, ?_⟩
    simp only [canonicalInputLabelledFullTrace, hcanonical,
      Walk.inputLabelledFullTrace_append]
    exact (congrArg
      (fun trace => prefixWalk.inputLabelledFullTrace input ++ trace) htrace).symm

/-- Exact pointwise product factorization of a realized canonical suffix-cone
indicator. -/
theorem canonicalResidualSuffixConeIndicator_eq_prefix_mul_suffixCylinder
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous) (reference : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk)
    (input : Fin n -> Bool) :
    B.canonicalResidualSuffixConeIndicator
        (suffixWalk.inputLabelledFullTrace reference.1) input =
      B.ratCompatiblePrefixIndicator input vertex *
        ratFixedLabelledSuffixCylinderIndicator
          suffixWalk reference.1 input := by
  rw [B.canonicalResidualSuffixConeIndicator_eq_membershipIndicator]
  unfold canonicalResidualSuffixConeMembershipIndicator
    ratCompatiblePrefixIndicator ratFixedLabelledSuffixCylinderIndicator
  rw [B.isCanonicalResidualSuffixConeInput_iff_prefix_and_fixedSuffix
    hUnambiguous reference suffixWalk hreferenceSuffix input]
  by_cases hprefix : B.HasCompatiblePrefix input vertex <;>
    by_cases hsuffix : suffixWalk.inputLabelledFullTrace input =
      suffixWalk.inputLabelledFullTrace reference.1 <;>
      simp [compatiblePrefixIndicator, hprefix, hsuffix]

/-- The prefix factor is local to the advertised pre-variables. -/
theorem ratCompatiblePrefixIndicator_eq_of_eq_on_preVars
    {n : Nat} (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    {left right : Fin n -> Bool}
    (hagrees : ∀ queryIndex, queryIndex ∈ B.preVars vertex ->
      left queryIndex = right queryIndex) :
    B.ratCompatiblePrefixIndicator left vertex =
      B.ratCompatiblePrefixIndicator right vertex := by
  classical
  exact B.ratCompatiblePrefixIndicator_dependsOnlyOn_preVars vertex hagrees

/-- The fixed labelled-suffix cylinder is local to the variables queried by
that suffix walk. -/
theorem ratFixedLabelledSuffixCylinderIndicator_eq_of_eq_on_queryVars
    {n : Nat} {B : FiniteUnambiguousFBDD n} {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (reference : Fin n -> Bool)
    {left right : Fin n -> Bool}
    (hagrees : ∀ queryIndex, queryIndex ∈ suffixWalk.queryVars ->
      left queryIndex = right queryIndex) :
    ratFixedLabelledSuffixCylinderIndicator suffixWalk reference left =
      ratFixedLabelledSuffixCylinderIndicator suffixWalk reference right := by
  classical
  unfold ratFixedLabelledSuffixCylinderIndicator
  rw [suffixWalk.inputLabelledFullTrace_eq_of_eq_on_queryVars
    left right hagrees]

/-- The fixed labelled-suffix cylinder has exactly the advertised dependency
set. -/
theorem ratFixedLabelledSuffixCylinderIndicator_dependsOnlyOn_queryVars
    {n : Nat} {B : FiniteUnambiguousFBDD n} {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (reference : Fin n -> Bool) :
    FiniteBooleanFourier.DependsOnlyOn suffixWalk.queryVars
      (fun input =>
        ratFixedLabelledSuffixCylinderIndicator
          suffixWalk reference input) := by
  intro left right hagrees
  exact ratFixedLabelledSuffixCylinderIndicator_eq_of_eq_on_queryVars
    suffixWalk reference hagrees

/-- The labelled-trace cylinder is literally the coordinate cylinder fixing
the values on the variables queried by the suffix walk. -/
theorem ratFixedLabelledSuffixCylinderIndicator_eq_if_restrictAssignment
    {n : Nat} {B : FiniteUnambiguousFBDD n} {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (reference input : Fin n -> Bool) :
    ratFixedLabelledSuffixCylinderIndicator suffixWalk reference input =
      if restrictAssignment suffixWalk.queryVars input =
          restrictAssignment suffixWalk.queryVars reference then 1 else 0 := by
  classical
  unfold ratFixedLabelledSuffixCylinderIndicator
  apply if_congr
  constructor
  · intro htrace
    funext queryIndex
    exact suffixWalk.eq_on_queryVars_of_inputLabelledQueryTrace_eq
      input reference
      (suffixWalk.inputLabelledQueryTrace_eq_of_inputLabelledFullTrace_eq
        input reference htrace)
      queryIndex queryIndex.property
  · intro hrestrict
    apply suffixWalk.inputLabelledFullTrace_eq_of_eq_on_queryVars
    intro queryIndex hqueryIndex
    exact congrFun hrestrict ⟨queryIndex, hqueryIndex⟩
  · rfl
  · rfl

/-- Exact Walsh coefficient of one fixed labelled suffix cylinder.  Inside
the suffix dependency set it is the reference character divided by the
number of suffix assignments. -/
theorem coefficient_ratFixedLabelledSuffixCylinderIndicator_eq_character_div
    {n : Nat} {B : FiniteUnambiguousFBDD n} {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (reference : Fin n -> Bool)
    (support : Finset (Fin n))
    (hsupport : support ⊆ suffixWalk.queryVars) :
    coefficient
        (fun input => ratFixedLabelledSuffixCylinderIndicator
          suffixWalk reference input) support =
      character support reference / (2 : Rat) ^ suffixWalk.queryVars.card := by
  classical
  let queryVars := suffixWalk.queryVars
  let complement := Finset.univ \ queryVars
  have hdisjoint : Disjoint queryVars complement := by
    simp [queryVars, complement, Finset.disjoint_left]
  have hcover : queryVars ∪ complement = Finset.univ := by
    simp [queryVars, complement]
  let localSupport := localizeSupport queryVars support
  have hlift : liftLocalSupport queryVars localSupport = support := by
    dsimp only [localSupport]
    rw [liftLocalSupport_localizeSupport]
    exact Finset.inter_eq_left.mpr hsupport
  have hlocal := coefficient_eq_localCoefficient_left_of_partition
    (ratFixedLabelledSuffixCylinderIndicator_dependsOnlyOn_queryVars
      suffixWalk reference)
    hdisjoint hcover localSupport
  rw [hlift] at hlocal
  rw [hlocal]
  unfold localCoefficient
  let referenceLocal := restrictAssignment queryVars reference
  have hcylinder (input : LocalAssignment queryVars) :
      ratFixedLabelledSuffixCylinderIndicator suffixWalk reference
          (extendAssignment queryVars input) =
        if input = referenceLocal then 1 else 0 := by
    rw [ratFixedLabelledSuffixCylinderIndicator_eq_if_restrictAssignment]
    change
      (if restrictAssignment queryVars (extendAssignment queryVars input) =
          restrictAssignment queryVars reference then 1 else 0) =
        if input = referenceLocal then 1 else 0
    rw [restrictAssignment_extendAssignment]
  have hsum :
      (∑ input : LocalAssignment queryVars,
        ratFixedLabelledSuffixCylinderIndicator suffixWalk reference
            (extendAssignment queryVars input) *
          localCharacter localSupport input) =
        localCharacter localSupport referenceLocal := by
    calc
      _ = ratFixedLabelledSuffixCylinderIndicator suffixWalk reference
            (extendAssignment queryVars referenceLocal) *
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

/-- Every in-support Fourier coefficient of the fixed suffix cylinder has
the same magnitude, namely `2 ^ (-|suffix variables|)`. -/
theorem abs_coefficient_ratFixedLabelledSuffixCylinderIndicator_eq_inv_pow
    {n : Nat} {B : FiniteUnambiguousFBDD n} {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (reference : Fin n -> Bool)
    (support : Finset (Fin n))
    (hsupport : support ⊆ suffixWalk.queryVars) :
    |coefficient
        (fun input => ratFixedLabelledSuffixCylinderIndicator
          suffixWalk reference input) support| =
      1 / (2 : Rat) ^ suffixWalk.queryVars.card := by
  rw [coefficient_ratFixedLabelledSuffixCylinderIndicator_eq_character_div
    suffixWalk reference support hsupport, abs_div, abs_character_eq_one]
  rw [abs_of_nonneg (by positivity :
    (0 : Rat) ≤ (2 : Rat) ^ suffixWalk.queryVars.card)]

/-- Under syntactic read-once, the two factors in the suffix-cone product
have disjoint dependency sets. -/
theorem preVars_disjoint_fixedSuffixQueryVars
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) :
    Disjoint (B.preVars vertex) suffixWalk.queryVars := by
  exact (B.preVars_disjoint_postVars hreadOnce vertex).mono_right
    suffixWalk.queryVars_subset_postVars

/-- Completeness of the canonical accepting trace makes the prefix and the
fixed suffix cover every coordinate.  Consequently every Fourier support
meets the support premise of the product-factorization theorem below. -/
theorem support_subset_preVars_union_suffixQueryVars_of_completeCanonicalSuffix
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk)
    (hcomplete :
      (B.canonicalAcceptingWalk reference).queryVars = Finset.univ)
    (support : Finset (Fin n)) :
    support ⊆ B.preVars vertex ∪ suffixWalk.queryVars := by
  rcases hreferenceSuffix with ⟨prefixWalk, hcanonical⟩
  intro queryIndex _hqueryIndex
  have hwhole :
      queryIndex ∈ (B.canonicalAcceptingWalk reference).queryVars := by
    rw [hcomplete]
    exact Finset.mem_univ queryIndex
  rw [hcanonical, Walk.queryVars_append] at hwhole
  rcases Finset.mem_union.mp hwhole with hprefix | hsuffix
  · exact Finset.mem_union.mpr
      (Or.inl (prefixWalk.queryVars_subset_preVars hprefix))
  · exact Finset.mem_union.mpr (Or.inr hsuffix)

/-- Fourier coefficient factorization of a realized canonical suffix cone.
The coefficient splits into a prefix coefficient and a fixed-cylinder
coefficient whenever its support lies in their disjoint dependency union. -/
theorem coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_suffix
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hUnambiguous : B.IsUnambiguous) (reference : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk)
    (support : Finset (Fin n))
    (hsupport : support ⊆ B.preVars vertex ∪ suffixWalk.queryVars) :
    coefficient
        (B.canonicalResidualSuffixConeIndicator
          (suffixWalk.inputLabelledFullTrace reference.1)) support =
      coefficient (fun input =>
          B.ratCompatiblePrefixIndicator input vertex)
          (support ∩ B.preVars vertex) *
        coefficient (fun input =>
          ratFixedLabelledSuffixCylinderIndicator
            suffixWalk reference.1 input)
          (support ∩ suffixWalk.queryVars) := by
  have hfunction :
      B.canonicalResidualSuffixConeIndicator
          (suffixWalk.inputLabelledFullTrace reference.1) =
        fun input => B.ratCompatiblePrefixIndicator input vertex *
          ratFixedLabelledSuffixCylinderIndicator
            suffixWalk reference.1 input := by
    funext input
    exact B.canonicalResidualSuffixConeIndicator_eq_prefix_mul_suffixCylinder
      hUnambiguous reference suffixWalk hreferenceSuffix input
  rw [hfunction]
  exact FiniteBooleanFourier.coefficient_mul_eq_mul_coefficient_of_disjoint
    (B.ratCompatiblePrefixIndicator_dependsOnlyOn_preVars vertex)
    (ratFixedLabelledSuffixCylinderIndicator_dependsOnlyOn_queryVars
      suffixWalk reference.1)
    (B.preVars_disjoint_fixedSuffixQueryVars hreadOnce suffixWalk)
    hsupport

/-- Complete-trace form of the cone coefficient factorization.  Unlike the
generic theorem, it has no residual support-filter premise. -/
theorem coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_suffix_of_complete
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hUnambiguous : B.IsUnambiguous) (reference : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk)
    (hcomplete :
      (B.canonicalAcceptingWalk reference).queryVars = Finset.univ)
    (support : Finset (Fin n)) :
    coefficient
        (B.canonicalResidualSuffixConeIndicator
          (suffixWalk.inputLabelledFullTrace reference.1)) support =
      coefficient (fun input =>
          B.ratCompatiblePrefixIndicator input vertex)
          (support ∩ B.preVars vertex) *
        coefficient (fun input =>
          ratFixedLabelledSuffixCylinderIndicator
            suffixWalk reference.1 input)
          (support ∩ suffixWalk.queryVars) := by
  exact B.coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_suffix
    hreadOnce hUnambiguous reference suffixWalk hreferenceSuffix support
    (B.support_subset_preVars_union_suffixQueryVars_of_completeCanonicalSuffix
      reference suffixWalk hreferenceSuffix hcomplete support)

/-- Fully explicit complete-trace coefficient formula.  The suffix factor is
the flat point-cylinder coefficient: one character sign divided by
`2 ^ |suffix variables|`.  All nontrivial Fourier information is therefore
concentrated in the reachable-prefix coefficient. -/
theorem coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_character_div_of_complete
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hUnambiguous : B.IsUnambiguous) (reference : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk)
    (hcomplete :
      (B.canonicalAcceptingWalk reference).queryVars = Finset.univ)
    (support : Finset (Fin n)) :
    coefficient
        (B.canonicalResidualSuffixConeIndicator
          (suffixWalk.inputLabelledFullTrace reference.1)) support =
      coefficient (fun input =>
          B.ratCompatiblePrefixIndicator input vertex)
          (support ∩ B.preVars vertex) *
        (character (support ∩ suffixWalk.queryVars) reference.1 /
          (2 : Rat) ^ suffixWalk.queryVars.card) := by
  rw [B.coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_suffix_of_complete
    hreadOnce hUnambiguous reference suffixWalk hreferenceSuffix hcomplete support]
  rw [coefficient_ratFixedLabelledSuffixCylinderIndicator_eq_character_div]
  exact Finset.inter_subset_right

/-- Quantitative cone factorization: a complete realized suffix damps every
ambient coefficient by exactly `2 ^ (-|suffix variables|)`, leaving only the
magnitude of the reachable-prefix coefficient. -/
theorem abs_coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_div_pow_of_complete
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hUnambiguous : B.IsUnambiguous) (reference : B.AcceptedModel)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hreferenceSuffix :
      B.HasCanonicalAcceptingSuffix reference suffixWalk)
    (hcomplete :
      (B.canonicalAcceptingWalk reference).queryVars = Finset.univ)
    (support : Finset (Fin n)) :
    |coefficient
        (B.canonicalResidualSuffixConeIndicator
          (suffixWalk.inputLabelledFullTrace reference.1)) support| =
      |coefficient (fun input =>
          B.ratCompatiblePrefixIndicator input vertex)
          (support ∩ B.preVars vertex)| /
        (2 : Rat) ^ suffixWalk.queryVars.card := by
  rw [B.coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_character_div_of_complete
    hreadOnce hUnambiguous reference suffixWalk hreferenceSuffix hcomplete support]
  rw [abs_mul, abs_div, abs_character_eq_one]
  rw [abs_of_nonneg (by positivity :
    (0 : Rat) ≤ (2 : Rat) ^ suffixWalk.queryVars.card)]
  ring

/-- One atomic signed residual deviation is exactly its masked conditional
high-degree Fourier tail. -/
theorem acceptedPointResidualDeviation_eq_highTailAverage
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (accepted : B.AcceptedModel) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    B.acceptedPointResidualDeviation accepted cutoff base mask =
      finiteAverage (fun uniform : Fin n -> Bool =>
        ratHighDegreeFourierTail (B.ratAcceptedPointIndicator accepted)
          cutoff (maskedInput base mask uniform)) := by
  rw [FiniteBooleanResidualMass.highTailAverage_eq_maskedAverage_sub_lowDegreePredictor]
  unfold FiniteBooleanResidualMass.maskedAverage
    FiniteBooleanResidualMass.maskedLowDegreePredictor
    acceptedPointResidualDeviation acceptedPointLowDegreePredictor
  rw [B.acceptedPointCompatibleMass_eq_acceptedPointMaskedMass]
  rfl

/-- The signed mass of a canonical suffix cone is the masked conditional
high-degree tail of the cone indicator. -/
theorem canonicalResidualDeviationSuffixConeMass_eq_highTailAverage
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) :
    B.canonicalResidualDeviationSuffixConeMass cutoff base mask key =
      finiteAverage (fun uniform : Fin n -> Bool =>
        ratHighDegreeFourierTail
          (B.canonicalResidualSuffixConeIndicator key) cutoff
          (maskedInput base mask uniform)) := by
  classical
  unfold canonicalResidualDeviationSuffixConeMass
    FiniteSignedReverseLCPTelescope.suffixConeMass
  calc
    (∑ accepted : B.AcceptedModel,
        if key <:+ B.canonicalInputLabelledFullTrace accepted then
          B.acceptedPointResidualDeviation accepted cutoff base mask
        else 0) =
      ∑ accepted : B.AcceptedModel,
        if key <:+ B.canonicalInputLabelledFullTrace accepted then
          finiteAverage (fun uniform : Fin n -> Bool =>
            ratHighDegreeFourierTail (B.ratAcceptedPointIndicator accepted)
              cutoff (maskedInput base mask uniform))
        else 0 := by
          apply Finset.sum_congr rfl
          intro accepted _
          split
          · rw [B.acceptedPointResidualDeviation_eq_highTailAverage]
          · rfl
    _ = finiteAverage (fun uniform : Fin n -> Bool =>
        ∑ accepted : B.AcceptedModel,
          if key <:+ B.canonicalInputLabelledFullTrace accepted then
            ratHighDegreeFourierTail (B.ratAcceptedPointIndicator accepted)
              cutoff (maskedInput base mask uniform)
          else 0) := by
            rw [finiteAverage_fintype_sum]
            apply Finset.sum_congr rfl
            intro accepted _
            split
            · rfl
            · unfold finiteAverage
              simp
    _ = finiteAverage (fun uniform : Fin n -> Bool =>
        ratHighDegreeFourierTail
          (B.canonicalResidualSuffixConeIndicator key) cutoff
          (maskedInput base mask uniform)) := by
            apply finiteAverage_congr
            intro uniform
            unfold canonicalResidualSuffixConeIndicator
            rw [ratHighDegreeFourierTail_fintype_sum]
            apply Finset.sum_congr rfl
            intro accepted _
            split
            · rfl
            · simp [ratHighDegreeFourierTail,
                FiniteBooleanFourier.coefficient]

/-! ## Exact structured-code energy of one suffix cone -/

/-- The exact structured high-tail energy attached to one canonical suffix
cone: its diagonal mask-survival energy plus its signed dual-code aliases. -/
noncomputable def structuredCanonicalResidualSuffixConeEnergy
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (key : List (InputLabelledFullStep B)) : Rat :=
  let f := B.canonicalResidualSuffixConeIndicator key
  (∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
      (coefficient f support) ^ 2 *
        finiteAverage
          (fun t : FiniteBitTape (structuredIndependence m * n) =>
            maskAllZeroIndicator support
              ((structuredDyadicPrimitive n m tailBits hn htail).generate t))) +
    structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail f

/-- The seed-averaged square of one signed suffix-cone mass is exactly its
structured diagonal-plus-dual Fourier energy. -/
theorem canonicalResidualDeviationSuffixConeMass_secondMoment_eq_structuredEnergy
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (key : List (InputLabelledFullStep B)) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (B.canonicalResidualDeviationSuffixConeMass (2 * m)
        ((structuredUnbiasedPrimitive n m hn).generate seed.1)
        ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
        key) ^ 2) =
      structuredCanonicalResidualSuffixConeEnergy
        n m tailBits hn htail B key := by
  unfold structuredCanonicalResidualSuffixConeEnergy
  dsimp only
  calc
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (B.canonicalResidualDeviationSuffixConeMass (2 * m)
        ((structuredUnbiasedPrimitive n m hn).generate seed.1)
        ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
        key) ^ 2) =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          ratHighDegreeFourierTail
            (B.canonicalResidualSuffixConeIndicator key) (2 * m)
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              uniform))) ^ 2) := by
                apply finiteAverage_congr
                intro seed
                rw [B.canonicalResidualDeviationSuffixConeMass_eq_highTailAverage]
    _ = _ := structured_highTail_restriction_secondMoment_eq_diagonal_add_dual
      n m tailBits hn htail
        (B.canonicalResidualSuffixConeIndicator key)

/-- Averaging one local reverse-LCP charge preserves the signed square drop,
now expressed entirely as a difference of structured Fourier/code energies.
In particular, no nonnegativity of an individual node charge is assumed. -/
theorem canonicalExactLCPSignedPairCharge_average_eq_structuredEnergyDrop
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (key : List (InputLabelledFullStep B)) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      B.canonicalExactLCPSignedPairCharge (2 * m)
        ((structuredUnbiasedPrimitive n m hn).generate seed.1)
        ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
        key) =
      structuredCanonicalResidualSuffixConeEnergy
          n m tailBits hn htail B key -
        ∑ step ∈ B.canonicalImmediateReverseLCPSteps key,
          structuredCanonicalResidualSuffixConeEnergy
            n m tailBits hn htail B (step :: key) := by
  calc
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      B.canonicalExactLCPSignedPairCharge (2 * m)
        ((structuredUnbiasedPrimitive n m hn).generate seed.1)
        ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
        key) =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        B.canonicalResidualDeviationSuffixConeMass (2 * m)
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
            key ^ 2 -
          ∑ step ∈ B.canonicalImmediateReverseLCPSteps key,
            B.canonicalResidualDeviationSuffixConeMass (2 * m)
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              (step :: key) ^ 2) := by
                apply finiteAverage_congr
                intro seed
                exact B.canonicalExactLCPSignedPairCharge_eq_suffixSquareDrop
                  (2 * m)
                  ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    seed.2)
                  key
    _ = finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          key ^ 2) -
        ∑ step ∈ B.canonicalImmediateReverseLCPSteps key,
          finiteAverage (fun seed :
              FiniteBitTape (structuredIndependence m * n) ×
                FiniteBitTape (structuredIndependence m * n) =>
            B.canonicalResidualDeviationSuffixConeMass (2 * m)
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              (step :: key) ^ 2) := by
                rw [finiteAverage_sub, finiteAverage_finset_sum]
    _ = _ := by
      rw [B.canonicalResidualDeviationSuffixConeMass_secondMoment_eq_structuredEnergy]
      apply congrArg (fun childEnergy =>
        structuredCanonicalResidualSuffixConeEnergy
          n m tailBits hn htail B key - childEnergy)
      apply Finset.sum_congr rfl
      intro step _
      rw [B.canonicalResidualDeviationSuffixConeMass_secondMoment_eq_structuredEnergy]

end FiniteUnambiguousFBDD

namespace MandatoryCanonicalSelectorFourierKernel

open FiniteUnambiguousFBDD
open FiniteAffineRestrictionHybrid

/-- In every affine-prefixed mandatory selector, positivity of the canonical
block size discharges unambiguity, read-once, and complete-trace support.
Thus every realized suffix cone has the premise-free explicit coefficient
formula needed by the selector-correlation analysis. -/
theorem prefixedMandatoryCanonicalSelector_coneCoefficient_eq_prefix_mul_character_div
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (coordinateCount T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound coordinateCount)) :
    let B := (mandatoryCanonicalUFBDD machine coordinateCount T b)
      |>.affinePaddedRestrictByRounds rounds
    ∀ (reference : B.AcceptedModel) (vertex : B.Vertex)
      (suffixWalk : B.Walk vertex B.accept),
      B.HasCanonicalAcceptingSuffix reference suffixWalk ->
      ∀ support : Finset (Fin coordinateCount),
      coefficient
          (B.canonicalResidualSuffixConeIndicator
            (suffixWalk.inputLabelledFullTrace reference.1)) support =
        coefficient (fun input =>
            B.ratCompatiblePrefixIndicator input vertex)
            (support ∩ B.preVars vertex) *
          (character (support ∩ suffixWalk.queryVars) reference.1 /
            (2 : Rat) ^ suffixWalk.queryVars.card) := by
  dsimp only
  intro reference vertex suffixWalk hreferenceSuffix support
  let B := (mandatoryCanonicalUFBDD machine coordinateCount T b)
    |>.affinePaddedRestrictByRounds rounds
  apply B.coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_character_div_of_complete
    (mandatoryCanonicalUFBDD machine coordinateCount T b
      |>.affinePaddedRestrictByRounds_isSyntacticallyReadOnce rounds
        (mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
          machine coordinateCount T b))
    (mandatoryCanonicalUFBDD machine coordinateCount T b
      |>.affinePaddedRestrictByRounds_isUnambiguous rounds
        (mandatoryCanonicalUFBDD_isUnambiguous
          machine coordinateCount T b hb))
    reference suffixWalk hreferenceSuffix
  exact mandatoryCanonicalUFBDD_affinePaddedRestrictByRounds_walk_queryVars_eq_univ
    machine coordinateCount T b rounds (B.canonicalAcceptingWalk reference)

end MandatoryCanonicalSelectorFourierKernel

end

end OneTapeMagnification
end Frontier
end Pnp4
