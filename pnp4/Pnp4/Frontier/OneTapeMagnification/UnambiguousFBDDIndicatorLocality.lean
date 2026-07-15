import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDIndicatorCut

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

namespace FiniteUnambiguousFBDD

/-!
# Locality and factorization of finite uFBDD cut indicators

This file records the direct precursor to a Fourier decomposition.  Walk
compatibility only inspects variables queried by that walk.  Consequently a
compatible prefix is a function of `preVars`, a compatible accepting suffix
is a function of `postVars`, and the filtered cut indicator factors pointwise
into prefix, suffix, and input-independent structural indicators.

No Fourier expansion or lower bound is asserted here.
-/

namespace Walk

/-- Compatibility of a fixed walk is unchanged when two inputs agree on every
variable in its query trace. -/
theorem compatible_iff_of_eq_on_queryTrace
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input input' : Fin n → Bool} {source target : B.Vertex}
    (walk : B.Walk source target)
    (hagrees : ∀ queryIndex ∈ walk.queryTrace,
      input queryIndex = input' queryIndex) :
    walk.Compatible input ↔ walk.Compatible input' := by
  induction walk with
  | nil vertex =>
      simp [Compatible]
  | @cons source middle target edge tail ih =>
      have htailAgrees : ∀ queryIndex ∈ tail.queryTrace,
          input queryIndex = input' queryIndex := by
        intro queryIndex hqueryIndex
        apply hagrees queryIndex
        simp only [queryTrace] at hqueryIndex ⊢
        simp only [queryEvents, List.map_append, List.mem_append]
        exact Or.inr hqueryIndex
      have htail := ih htailAgrees
      cases hnode : B.node source with
      | query queryIndex ifFalse ifTrue =>
          have hhead : input queryIndex = input' queryIndex := by
            apply hagrees queryIndex
            simp [queryTrace, queryEvents, hnode,
              FiniteUFBDDNode.queryEvent?]
          simp [Compatible, CompatibleEdge, hnode, hhead, htail]
      | choice children =>
          simp [Compatible, CompatibleEdge, hnode, htail]
      | sink =>
          have hedgeFalse : False := by
            simp [Edge, FiniteUFBDDNode.HasChild, hnode] at edge
          exact hedgeFalse.elim

/-- Set-valued form of `compatible_iff_of_eq_on_queryTrace`. -/
theorem compatible_iff_of_eq_on_queryVars
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input input' : Fin n → Bool} {source target : B.Vertex}
    (walk : B.Walk source target)
    (hagrees : ∀ queryIndex ∈ walk.queryVars,
      input queryIndex = input' queryIndex) :
    walk.Compatible input ↔ walk.Compatible input' := by
  apply walk.compatible_iff_of_eq_on_queryTrace
  intro queryIndex hqueryIndex
  apply hagrees queryIndex
  simpa [queryVars] using hqueryIndex

end Walk

/-- Prefix reachability through compatible edges depends only on the variables
that can syntactically occur before the endpoint. -/
theorem hasCompatiblePrefix_iff_of_eq_on_preVars
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    {input input' : Fin n → Bool} (vertex : B.Vertex)
    (hagrees : ∀ queryIndex ∈ B.preVars vertex,
      input queryIndex = input' queryIndex) :
    B.HasCompatiblePrefix input vertex ↔
      B.HasCompatiblePrefix input' vertex := by
  constructor
  · rintro ⟨walk, hcompatible⟩
    refine ⟨walk, (walk.compatible_iff_of_eq_on_queryVars ?_).mp hcompatible⟩
    intro queryIndex hqueryIndex
    exact hagrees queryIndex (walk.queryVars_subset_preVars hqueryIndex)
  · rintro ⟨walk, hcompatible⟩
    refine ⟨walk, (walk.compatible_iff_of_eq_on_queryVars ?_).mpr hcompatible⟩
    intro queryIndex hqueryIndex
    exact hagrees queryIndex (walk.queryVars_subset_preVars hqueryIndex)

/-- Compatible accepting continuation from a vertex depends only on variables
that can syntactically occur between that vertex and acceptance. -/
theorem hasCompatibleAcceptingSuffix_iff_of_eq_on_postVars
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    {input input' : Fin n → Bool} (vertex : B.Vertex)
    (hagrees : ∀ queryIndex ∈ B.postVars vertex,
      input queryIndex = input' queryIndex) :
    B.HasCompatibleAcceptingSuffix input vertex ↔
      B.HasCompatibleAcceptingSuffix input' vertex := by
  constructor
  · rintro ⟨walk, hcompatible⟩
    refine ⟨walk, (walk.compatible_iff_of_eq_on_queryVars ?_).mp hcompatible⟩
    intro queryIndex hqueryIndex
    exact hagrees queryIndex (walk.queryVars_subset_postVars hqueryIndex)
  · rintro ⟨walk, hcompatible⟩
    refine ⟨walk, (walk.compatible_iff_of_eq_on_queryVars ?_).mpr hcompatible⟩
    intro queryIndex hqueryIndex
    exact hagrees queryIndex (walk.queryVars_subset_postVars hqueryIndex)

/-- The natural-number indicator of compatible prefix reachability. -/
noncomputable def compatiblePrefixIndicator
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n → Bool) (vertex : B.Vertex) : Nat := by
  classical
  exact if B.HasCompatiblePrefix input vertex then 1 else 0

/-- The natural-number indicator of compatible accepting continuation. -/
noncomputable def compatibleAcceptingSuffixIndicator
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n → Bool) (vertex : B.Vertex) : Nat := by
  classical
  exact if B.HasCompatibleAcceptingSuffix input vertex then 1 else 0

/-- The input-independent indicator of the structural filtered-cut condition. -/
noncomputable def filteredAlphaCutStaticIndicator
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (alpha : Finset (Fin n)) (k : Nat) (vertex : B.Vertex) : Nat := by
  classical
  exact if B.IsFilteredAlphaCutVertex alpha k vertex then 1 else 0

/-- The prefix indicator is local to `preVars vertex`. -/
theorem compatiblePrefixIndicator_eq_of_eq_on_preVars
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    {input input' : Fin n → Bool} (vertex : B.Vertex)
    (hagrees : ∀ queryIndex ∈ B.preVars vertex,
      input queryIndex = input' queryIndex) :
    B.compatiblePrefixIndicator input vertex =
      B.compatiblePrefixIndicator input' vertex := by
  classical
  rw [compatiblePrefixIndicator, compatiblePrefixIndicator,
    B.hasCompatiblePrefix_iff_of_eq_on_preVars vertex hagrees]

/-- The accepting-suffix indicator is local to `postVars vertex`. -/
theorem compatibleAcceptingSuffixIndicator_eq_of_eq_on_postVars
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    {input input' : Fin n → Bool} (vertex : B.Vertex)
    (hagrees : ∀ queryIndex ∈ B.postVars vertex,
      input queryIndex = input' queryIndex) :
    B.compatibleAcceptingSuffixIndicator input vertex =
      B.compatibleAcceptingSuffixIndicator input' vertex := by
  classical
  rw [compatibleAcceptingSuffixIndicator,
    compatibleAcceptingSuffixIndicator,
    B.hasCompatibleAcceptingSuffix_iff_of_eq_on_postVars vertex hagrees]

/-- Exact pointwise factorization of the semantic filtered-cut indicator. -/
theorem filteredAlphaCutIndicator_eq_prefix_mul_suffix_mul_static
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n → Bool) (alpha : Finset (Fin n))
    (k : Nat) (vertex : B.Vertex) :
    B.filteredAlphaCutIndicator input alpha k vertex =
      B.compatiblePrefixIndicator input vertex *
        B.compatibleAcceptingSuffixIndicator input vertex *
          B.filteredAlphaCutStaticIndicator alpha k vertex := by
  classical
  simp only [filteredAlphaCutIndicator, compatiblePrefixIndicator,
    compatibleAcceptingSuffixIndicator, filteredAlphaCutStaticIndicator,
    HasFilteredAlphaCut]
  by_cases hprefix : B.HasCompatiblePrefix input vertex <;>
    by_cases hsuffix : B.HasCompatibleAcceptingSuffix input vertex <;>
      by_cases hstatic : B.IsFilteredAlphaCutVertex alpha k vertex <;>
        simp [hprefix, hsuffix, hstatic]

/-- Under syntactic read-once, the two input-dependent indicator factors have
disjoint advertised dependency sets. -/
theorem indicatorDependencySets_disjoint_of_syntacticallyReadOnce
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce) (vertex : B.Vertex) :
    Disjoint (B.preVars vertex) (B.postVars vertex) :=
  B.preVars_disjoint_postVars hreadOnce vertex

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
