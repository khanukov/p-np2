import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDSuffixLaplacian

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact high-degree regrouping for finite uFBDDs

This module proves the finite algebraic bridge from the corrected, static-
filtered Claim-15 coefficient identity to the `H_v * G_v` high-degree
decomposition.  It contains no restriction argument, error estimate, or
lower-bound claim.
-/

open scoped BigOperators

namespace FiniteBooleanCutReindex

variable {Index Value : Type*} [DecidableEq Index] [AddCommMonoid Value]

/-- Supports admitted by the static cut condition at a fixed query
coordinate. -/
def cutSupports (pre post : Finset Index) (queryIndex : Index) (k : Nat) :
    Finset (Finset Index) :=
  (pre ∪ post).powerset.filter fun alpha =>
    (alpha ∩ pre).card = k ∧ queryIndex ∈ alpha

/-- Suffix supports selected by a fixed query coordinate. -/
def suffixSupports (post : Finset Index) (queryIndex : Index) :
    Finset (Finset Index) :=
  post.powerset.filter fun beta => queryIndex ∈ beta

/-- Every subset of a union splits into its two intersections. -/
lemma eq_inter_union_inter {pre post alpha : Finset Index}
    (hsubset : alpha ⊆ pre ∪ post) :
    alpha = (alpha ∩ pre) ∪ (alpha ∩ post) := by
  ext queryIndex
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · intro hqueryIndex
    rcases Finset.mem_union.mp (hsubset hqueryIndex) with hpre | hpost
    · exact Or.inl ⟨hqueryIndex, hpre⟩
    · exact Or.inr ⟨hqueryIndex, hpost⟩
  · rintro (⟨hqueryIndex, _⟩ | ⟨hqueryIndex, _⟩) <;>
      exact hqueryIndex

/-- The left intersection recovers the left member of a union of subsets of
disjoint ambient supports. -/
lemma union_inter_left_eq {pre post left right : Finset Index}
    (hleft : left ⊆ pre) (hright : right ⊆ post)
    (hdisjoint : Disjoint pre post) :
    (left ∪ right) ∩ pre = left := by
  ext queryIndex
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hleft' | hright', hpre⟩
    · exact hleft'
    · exact False.elim
        ((Finset.disjoint_left.mp hdisjoint) hpre (hright hright'))
  · intro hleft'
    exact ⟨Or.inl hleft', hleft hleft'⟩

/-- The right intersection recovers the right member of a union of subsets of
disjoint ambient supports. -/
lemma union_inter_right_eq {pre post left right : Finset Index}
    (hleft : left ⊆ pre) (hright : right ⊆ post)
    (hdisjoint : Disjoint pre post) :
    (left ∪ right) ∩ post = right := by
  ext queryIndex
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hleft' | hright', hpost⟩
    · exact False.elim
        ((Finset.disjoint_left.mp hdisjoint) (hleft hleft') hpost)
    · exact hright'
  · intro hright'
    exact ⟨Or.inr hright', hright hright'⟩

/-- Static cut supports are in bijection with a degree-`k` prefix support and
a nonempty selected suffix support. -/
theorem sum_cutSupports_eq_sum_product
    (pre post : Finset Index) (queryIndex : Index) (k : Nat)
    (hdisjoint : Disjoint pre post) (hqueryPre : queryIndex ∉ pre)
    (weight : Finset Index × Finset Index → Value) :
    ∑ alpha ∈ cutSupports pre post queryIndex k,
        weight (alpha ∩ pre, alpha ∩ post) =
      ∑ pair ∈ (pre.powersetCard k).product
          (suffixSupports post queryIndex),
        weight pair := by
  classical
  apply Finset.sum_bij
      (fun alpha _ => (alpha ∩ pre, alpha ∩ post))
  · intro alpha halpha
    apply Finset.mem_product.mpr
    rw [cutSupports, Finset.mem_filter, Finset.mem_powerset] at halpha
    rcases halpha with ⟨halphaSupport, halphaCard, hqueryAlpha⟩
    have hqueryPost : queryIndex ∈ post := by
      rcases Finset.mem_union.mp (halphaSupport hqueryAlpha) with
        hqueryPre' | hqueryPost
      · exact False.elim (hqueryPre hqueryPre')
      · exact hqueryPost
    constructor
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.inter_subset_right, halphaCard⟩
    · rw [suffixSupports, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_inter.mpr ⟨hqueryAlpha, hqueryPost⟩⟩
  · intro alpha halpha alpha' halpha' heq
    rw [cutSupports, Finset.mem_filter, Finset.mem_powerset] at halpha halpha'
    have hsplit := eq_inter_union_inter halpha.1
    have hsplit' := eq_inter_union_inter halpha'.1
    have hpre := congrArg Prod.fst heq
    have hpost := congrArg Prod.snd heq
    simp only at hpre hpost
    rw [hsplit, hsplit', hpre, hpost]
  · intro pair hpair
    rcases Finset.mem_product.mp hpair with ⟨hleft, hright⟩
    rw [Finset.mem_powersetCard] at hleft
    rw [suffixSupports, Finset.mem_filter, Finset.mem_powerset] at hright
    refine ⟨pair.1 ∪ pair.2, ?_, ?_⟩
    · rw [cutSupports, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro queryIndex' hqueryIndex'
        rcases Finset.mem_union.mp hqueryIndex' with hleft' | hright'
        · exact Finset.mem_union_left _ (hleft.1 hleft')
        · exact Finset.mem_union_right _ (hright.1 hright')
      constructor
      · rw [union_inter_left_eq hleft.1 hright.1 hdisjoint, hleft.2]
      · exact Finset.mem_union_right _ hright.2
    · apply Prod.ext
      · exact union_inter_left_eq hleft.1 hright.1 hdisjoint
      · exact union_inter_right_eq hleft.1 hright.1 hdisjoint
  · intro alpha halpha
    rfl

end FiniteBooleanCutReindex

namespace FiniteUnambiguousFBDD

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanCutReindex

/-! ## Structural support facts -/

/-- A query at `vertex` is not among the variables queried strictly before
`vertex`. -/
theorem queryIndex_not_mem_preVars_of_node_eq_query
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (vertex : B.Vertex) (queryIndex : Fin n)
    (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query queryIndex ifFalse ifTrue) :
    queryIndex ∉ B.preVars vertex := by
  intro hpre
  rw [B.mem_preVars_iff] at hpre
  rcases hpre with ⟨leftWalk, hmem⟩
  have hedge : B.Edge vertex ifFalse := by
    simp [Edge, hnode, FiniteUFBDDNode.HasChild]
  let rightWalk : B.Walk vertex ifFalse :=
    .cons hedge (.nil ifFalse)
  have hnodup := hreadOnce ifFalse (leftWalk.append rightWalk)
  have htrace : rightWalk.queryTrace = [queryIndex] := by
    simp [rightWalk, Walk.queryTrace, Walk.queryEvents, hnode,
      FiniteUFBDDNode.queryEvent?]
  rw [Walk.queryTrace_append, htrace] at hnodup
  exact (List.nodup_append.mp hnodup).2.2 queryIndex hmem queryIndex
    (by simp) rfl

/-- The prefix homogeneous slice may be restricted to degree-`k` subsets of
the advertised prefix variables. -/
theorem ratCompatiblePrefixHomogeneousSlice_eq_sum_powersetCard
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) (input : Fin n → Bool) :
    B.ratCompatiblePrefixHomogeneousSlice vertex k input =
      ∑ alpha ∈ (B.preVars vertex).powersetCard k,
        coefficient
            (fun source => B.ratCompatiblePrefixIndicator source vertex)
            alpha *
          character alpha input := by
  classical
  have hdegree : degreeSupports n k =
      (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext alpha
    simp [degreeSupports]
  unfold ratCompatiblePrefixHomogeneousSlice homogeneousPolynomial
  rw [hdegree]
  symm
  apply Finset.sum_subset
  · exact Finset.powersetCard_mono (Finset.subset_univ _)
  · intro alpha halpha hnot
    have hnsubset : ¬ alpha ⊆ B.preVars vertex := by
      intro hsubset
      apply hnot
      exact Finset.mem_powersetCard.mpr
        ⟨hsubset, (Finset.mem_powersetCard.mp halpha).2⟩
    rw [coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
      (B.ratCompatiblePrefixIndicator_dependsOnlyOn_preVars vertex)
      hnsubset]
    simp

/-- At a query vertex, membership in the path-independent static cut is
exactly membership in the corresponding finite support set. -/
theorem isFilteredAlphaCutVertex_iff_mem_cutSupports_of_node_eq_query
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) (queryIndex : Fin n)
    (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query queryIndex ifFalse ifTrue)
    (alpha : Finset (Fin n)) (k : Nat) :
    B.IsFilteredAlphaCutVertex alpha k vertex ↔
      alpha ∈ cutSupports (B.preVars vertex) (B.postVars vertex)
        queryIndex k := by
  classical
  simp only [IsFilteredAlphaCutVertex, cutSupports, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨⟨otherIndex, otherFalse, otherTrue, hotherNode, hmem⟩,
      hcard, hsubset⟩
    rw [hnode] at hotherNode
    cases hotherNode
    exact ⟨hsubset, hcard, hmem⟩
  · rintro ⟨hsubset, hcard, hmem⟩
    exact ⟨⟨queryIndex, ifFalse, ifTrue, hnode, hmem⟩,
      hcard, hsubset⟩

/-- Rational static-indicator form of the finite cut-support
characterization. -/
theorem ratFilteredAlphaCutStaticIndicator_eq_indicator_cutSupports
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) (queryIndex : Fin n)
    (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query queryIndex ifFalse ifTrue)
    (alpha : Finset (Fin n)) (k : Nat) :
    B.ratFilteredAlphaCutStaticIndicator alpha k vertex =
      if alpha ∈ cutSupports (B.preVars vertex) (B.postVars vertex)
          queryIndex k then 1 else 0 := by
  classical
  rw [ratFilteredAlphaCutStaticIndicator,
    filteredAlphaCutStaticIndicator]
  rw [B.isFilteredAlphaCutVertex_iff_mem_cutSupports_of_node_eq_query
    vertex queryIndex ifFalse ifTrue hnode]
  split <;> simp_all

/-- Query-vertex form of the suffix Fourier filter as an ordinary filtered
finite sum. -/
theorem suffixFourierFilter_eq_sum_suffixSupports_of_node_eq_query
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) (queryIndex : Fin n)
    (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query queryIndex ifFalse ifTrue)
    (input : Fin n → Bool) :
    B.suffixFourierFilter vertex input =
      ∑ beta ∈ suffixSupports (B.postVars vertex) queryIndex,
        coefficient
            (fun source =>
              B.ratCompatibleAcceptingSuffixIndicator source vertex)
            beta *
          character beta input := by
  classical
  unfold suffixFourierFilter suffixSupports
  rw [hnode]
  simp only
  rw [Finset.sum_filter]

/-- Every static cut support is genuinely above degree `k`: its suffix part
contains the current query. -/
theorem card_lt_of_mem_cutSupports
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (vertex : B.Vertex) (queryIndex : Fin n)
    (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query queryIndex ifFalse ifTrue)
    {alpha : Finset (Fin n)}
    (halpha : alpha ∈ cutSupports (B.preVars vertex)
      (B.postVars vertex) queryIndex k) :
    k < alpha.card := by
  classical
  rw [cutSupports, Finset.mem_filter, Finset.mem_powerset] at halpha
  rcases halpha with ⟨hsubset, hcard, hqueryAlpha⟩
  have hqueryPre := B.queryIndex_not_mem_preVars_of_node_eq_query
    hreadOnce vertex queryIndex ifFalse ifTrue hnode
  have hqueryPost : queryIndex ∈ B.postVars vertex := by
    rcases Finset.mem_union.mp (hsubset hqueryAlpha) with hpre | hpost
    · exact False.elim (hqueryPre hpre)
    · exact hpost
  have hsplit := eq_inter_union_inter hsubset
  have hdisjointInter : Disjoint
      (alpha ∩ B.preVars vertex) (alpha ∩ B.postVars vertex) := by
    exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
      (B.preVars_disjoint_postVars hreadOnce vertex)
  have hpostPositive : 0 < (alpha ∩ B.postVars vertex).card := by
    exact Finset.card_pos.mpr
      ⟨queryIndex, Finset.mem_inter.mpr ⟨hqueryAlpha, hqueryPost⟩⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisjointInter, hcard]
  omega

/-! ## Fixed-vertex regrouping -/

/-- At one query vertex, the static-filtered high-degree Claim-15 summands
regroup exactly into the prefix homogeneous slice times the suffix Fourier
filter. -/
theorem highDegree_staticFactor_sum_eq_prefixSlice_mul_suffixFourierFilter_of_node_eq_query
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (vertex : B.Vertex) (queryIndex : Fin n)
    (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query queryIndex ifFalse ifTrue)
    (input : Fin n → Bool) :
    (∑ alpha : Finset (Fin n),
      if k < alpha.card then
        B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
          (coefficient
              (fun source =>
                B.ratCompatiblePrefixIndicator source vertex)
              (alpha ∩ B.preVars vertex) *
            coefficient
              (fun source =>
                B.ratCompatibleAcceptingSuffixIndicator source vertex)
              (alpha ∩ B.postVars vertex)) *
          character alpha input
      else 0) =
      B.ratCompatiblePrefixHomogeneousSlice vertex k input *
        B.suffixFourierFilter vertex input := by
  classical
  let cut := cutSupports (B.preVars vertex) (B.postVars vertex)
    queryIndex k
  let prefixCoefficient := fun alpha : Finset (Fin n) =>
    coefficient
      (fun source => B.ratCompatiblePrefixIndicator source vertex) alpha
  let suffixCoefficient := fun alpha : Finset (Fin n) =>
    coefficient
      (fun source =>
        B.ratCompatibleAcceptingSuffixIndicator source vertex) alpha
  let raw := fun alpha : Finset (Fin n) =>
    prefixCoefficient (alpha ∩ B.preVars vertex) *
      suffixCoefficient (alpha ∩ B.postVars vertex) *
        character alpha input
  have hpoint (alpha : Finset (Fin n)) :
      (if k < alpha.card then
        B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
          (prefixCoefficient (alpha ∩ B.preVars vertex) *
            suffixCoefficient (alpha ∩ B.postVars vertex)) *
          character alpha input
      else 0) = if alpha ∈ cut then raw alpha else 0 := by
    rw [B.ratFilteredAlphaCutStaticIndicator_eq_indicator_cutSupports
      vertex queryIndex ifFalse ifTrue hnode]
    by_cases hcut : alpha ∈ cut
    · have hhigh : k < alpha.card := by
        exact B.card_lt_of_mem_cutSupports hreadOnce vertex queryIndex
          ifFalse ifTrue hnode (by simpa [cut] using hcut)
      simp [cut] at hcut
      simp [cut, hcut, hhigh, raw]
    · simp [cut] at hcut
      by_cases hhigh : k < alpha.card <;>
        simp [cut, hcut, hhigh, raw]
  change
    (∑ alpha : Finset (Fin n),
      if k < alpha.card then
        B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
          (prefixCoefficient (alpha ∩ B.preVars vertex) *
            suffixCoefficient (alpha ∩ B.postVars vertex)) *
          character alpha input
      else 0) = _
  simp_rw [hpoint]
  have hfilter :
      (∑ alpha : Finset (Fin n),
        if alpha ∈ cut then raw alpha else 0) =
        ∑ alpha ∈ cut, raw alpha := by
    symm
    simp
  rw [hfilter]
  let weight := fun pair : Finset (Fin n) × Finset (Fin n) =>
    (prefixCoefficient pair.1 * character pair.1 input) *
      (suffixCoefficient pair.2 * character pair.2 input)
  calc
    (∑ alpha ∈ cut, raw alpha) =
        ∑ alpha ∈ cut,
          weight (alpha ∩ B.preVars vertex,
            alpha ∩ B.postVars vertex) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      have hsupport :
          alpha ⊆ B.preVars vertex ∪ B.postVars vertex := by
        simpa [cut, cutSupports] using
          (Finset.mem_filter.mp halpha).1
      have hsplit := eq_inter_union_inter hsupport
      have hdisjoint : Disjoint
          (alpha ∩ B.preVars vertex)
          (alpha ∩ B.postVars vertex) := by
        exact Disjoint.mono Finset.inter_subset_right
          Finset.inter_subset_right
          (B.preVars_disjoint_postVars hreadOnce vertex)
      have hleftIntersection :
          ((alpha ∩ B.preVars vertex) ∪
              (alpha ∩ B.postVars vertex)) ∩ B.preVars vertex =
            alpha ∩ B.preVars vertex := by
        exact union_inter_left_eq Finset.inter_subset_right
          Finset.inter_subset_right
          (B.preVars_disjoint_postVars hreadOnce vertex)
      have hrightIntersection :
          ((alpha ∩ B.preVars vertex) ∪
              (alpha ∩ B.postVars vertex)) ∩ B.postVars vertex =
            alpha ∩ B.postVars vertex := by
        exact union_inter_right_eq Finset.inter_subset_right
          Finset.inter_subset_right
          (B.preVars_disjoint_postVars hreadOnce vertex)
      unfold raw weight
      rw [hsplit, hleftIntersection, hrightIntersection,
        character_union_of_disjoint hdisjoint]
      ring
    _ = ∑ pair ∈
          ((B.preVars vertex).powersetCard k).product
            (suffixSupports (B.postVars vertex) queryIndex),
          weight pair := by
      simpa [cut] using
        (sum_cutSupports_eq_sum_product
          (B.preVars vertex) (B.postVars vertex) queryIndex k
          (B.preVars_disjoint_postVars hreadOnce vertex)
          (B.queryIndex_not_mem_preVars_of_node_eq_query hreadOnce
            vertex queryIndex ifFalse ifTrue hnode) weight)
    _ = (∑ alpha ∈ (B.preVars vertex).powersetCard k,
          prefixCoefficient alpha * character alpha input) *
        (∑ beta ∈ suffixSupports (B.postVars vertex) queryIndex,
          suffixCoefficient beta * character beta input) := by
      rw [Finset.sum_mul_sum]
      simpa [weight] using
        (Finset.sum_product ((B.preVars vertex).powersetCard k)
          (suffixSupports (B.postVars vertex) queryIndex) weight)
    _ = B.ratCompatiblePrefixHomogeneousSlice vertex k input *
        B.suffixFourierFilter vertex input := by
      rw [B.ratCompatiblePrefixHomogeneousSlice_eq_sum_powersetCard,
        B.suffixFourierFilter_eq_sum_suffixSupports_of_node_eq_query
          vertex queryIndex ifFalse ifTrue hnode]

/-- Canonical fixed-vertex form of the high-degree regrouping.  Silent choice
vertices and sinks contribute zero on both sides. -/
theorem highDegree_staticFactor_sum_eq_prefixSlice_mul_suffixFourierFilter
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (vertex : B.Vertex) (input : Fin n → Bool) :
    (∑ alpha : Finset (Fin n),
      if k < alpha.card then
        B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
          (coefficient
              (fun source =>
                B.ratCompatiblePrefixIndicator source vertex)
              (alpha ∩ B.preVars vertex) *
            coefficient
              (fun source =>
                B.ratCompatibleAcceptingSuffixIndicator source vertex)
              (alpha ∩ B.postVars vertex)) *
          character alpha input
      else 0) =
      B.ratCompatiblePrefixHomogeneousSlice vertex k input *
        B.suffixFourierFilter vertex input := by
  cases hnode : B.node vertex with
  | query queryIndex ifFalse ifTrue =>
      exact
        B.highDegree_staticFactor_sum_eq_prefixSlice_mul_suffixFourierFilter_of_node_eq_query
          hreadOnce vertex queryIndex ifFalse ifTrue hnode input
  | choice children =>
      classical
      simp [ratFilteredAlphaCutStaticIndicator,
        filteredAlphaCutStaticIndicator, IsFilteredAlphaCutVertex,
        suffixFourierFilter, hnode]
  | sink =>
      classical
      simp [ratFilteredAlphaCutStaticIndicator,
        filteredAlphaCutStaticIndicator, IsFilteredAlphaCutVertex,
        suffixFourierFilter, hnode]

/-! ## Global high-degree regrouping -/

/-- Exact rational high-degree Fourier tail of a Boolean-cube function. -/
noncomputable def ratHighDegreeFourierTail {n : Nat}
    (f : (Fin n → Bool) → ℚ) (k : Nat)
    (input : Fin n → Bool) : ℚ :=
  ∑ alpha : Finset (Fin n),
    if k < alpha.card then
      coefficient f alpha * character alpha input
    else 0

/-- The corrected Claim-15 coefficient factorization, summed over all
high-degree supports and regrouped by vertex.  The accepting-path hypothesis
is the exact full-read premise needed to instantiate Claim 15 simultaneously
for every Fourier support. -/
theorem ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixFourierFilter
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (input : Fin n → Bool) :
    ratHighDegreeFourierTail B.ratAcceptanceIndicator k input =
      ∑ vertex : B.Vertex,
        B.ratCompatiblePrefixHomogeneousSlice vertex k input *
          B.suffixFourierFilter vertex input := by
  classical
  unfold ratHighDegreeFourierTail
  calc
    (∑ alpha : Finset (Fin n),
      if k < alpha.card then
        coefficient B.ratAcceptanceIndicator alpha * character alpha input
      else 0) =
        ∑ alpha : Finset (Fin n),
          ∑ vertex : B.Vertex,
            if k < alpha.card then
              B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
                (coefficient
                    (fun source =>
                      B.ratCompatiblePrefixIndicator source vertex)
                    (alpha ∩ B.preVars vertex) *
                  coefficient
                    (fun source =>
                      B.ratCompatibleAcceptingSuffixIndicator source vertex)
                    (alpha ∩ B.postVars vertex)) *
                character alpha input
            else 0 := by
      apply Finset.sum_congr rfl
      intro alpha _
      by_cases hhigh : k < alpha.card
      · rw [if_pos hhigh]
        rw [B.coefficient_ratAcceptanceIndicator_eq_sum_static_mul_prefix_mul_suffix
          hreadOnce hunambiguous alpha k]
        · rw [Finset.sum_mul]
          simp [hhigh]
        · intro currentInput path
          rw [hreadsAll currentInput path]
          exact Finset.subset_univ alpha
        · exact hhigh
      · simp [hhigh]
    _ = ∑ vertex : B.Vertex,
          ∑ alpha : Finset (Fin n),
            if k < alpha.card then
              B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
                (coefficient
                    (fun source =>
                      B.ratCompatiblePrefixIndicator source vertex)
                    (alpha ∩ B.preVars vertex) *
                  coefficient
                    (fun source =>
                      B.ratCompatibleAcceptingSuffixIndicator source vertex)
                    (alpha ∩ B.postVars vertex)) *
                character alpha input
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ vertex : B.Vertex,
          B.ratCompatiblePrefixHomogeneousSlice vertex k input *
            B.suffixFourierFilter vertex input := by
      apply Finset.sum_congr rfl
      intro vertex _
      exact
        B.highDegree_staticFactor_sum_eq_prefixSlice_mul_suffixFourierFilter
          hreadOnce vertex input

/-- Laplacian form of the global exact high-degree regrouping. -/
theorem ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (input : Fin n → Bool) :
    ratHighDegreeFourierTail B.ratAcceptanceIndicator k input =
      ∑ vertex : B.Vertex,
        B.ratCompatiblePrefixHomogeneousSlice vertex k input *
          B.suffixLaplacian vertex input := by
  rw [B.ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixFourierFilter
    hreadOnce hunambiguous hreadsAll input]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [B.suffixLaplacian_eq_fourierFilter]

end FiniteUnambiguousFBDD

/-! ## Mandatory canonical specialization -/

/-- Exact high-degree Fourier regrouping for the mandatory canonical uFBDD.
The positive block-size assumption is used only to discharge unambiguity. -/
theorem mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixFourierFilter
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b k : Nat) (hb : 0 < b) (input : Fin n → Bool) :
    FiniteUnambiguousFBDD.ratHighDegreeFourierTail
        (mandatoryCanonicalUFBDD machine n T b).ratAcceptanceIndicator k input =
      ∑ vertex : (mandatoryCanonicalUFBDD machine n T b).Vertex,
        (mandatoryCanonicalUFBDD machine n T b).ratCompatiblePrefixHomogeneousSlice
            vertex k input *
          (mandatoryCanonicalUFBDD machine n T b).suffixFourierFilter
            vertex input := by
  apply
    FiniteUnambiguousFBDD.ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixFourierFilter
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce machine n T b
  · exact mandatoryCanonicalUFBDD_isUnambiguous machine n T b hb
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n T b currentInput path

/-- Laplacian form of the exact high-degree regrouping for the mandatory
canonical uFBDD. -/
theorem mandatoryCanonicalUFBDD_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b k : Nat) (hb : 0 < b) (input : Fin n → Bool) :
    FiniteUnambiguousFBDD.ratHighDegreeFourierTail
        (mandatoryCanonicalUFBDD machine n T b).ratAcceptanceIndicator k input =
      ∑ vertex : (mandatoryCanonicalUFBDD machine n T b).Vertex,
        (mandatoryCanonicalUFBDD machine n T b).ratCompatiblePrefixHomogeneousSlice
            vertex k input *
          (mandatoryCanonicalUFBDD machine n T b).suffixLaplacian vertex input := by
  apply
    FiniteUnambiguousFBDD.ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce machine n T b
  · exact mandatoryCanonicalUFBDD_isUnambiguous machine n T b hb
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n T b currentInput path

end OneTapeMagnification
end Frontier
end Pnp4
