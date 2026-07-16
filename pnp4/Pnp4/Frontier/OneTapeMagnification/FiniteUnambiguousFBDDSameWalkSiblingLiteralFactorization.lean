import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDCanonicalWalkCellDecomposition

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Same-walk sibling literal factorization

Two distinct immediate reverse-LCP extensions can be realized by different
inputs on the same bare walk only by carrying opposite labels at one common
query step.  Indeed, forgetting input labels makes the endpoint trace of a
fixed walk independent of the input.  Equal-length suffixes therefore align
the two sibling steps at the same source and target.  A choice or sink step
would have `query? = none` for both inputs, so distinctness forces a query
step and complementary Boolean labels.

Queries whose false and true successors coincide are intentionally allowed:
they are precisely the important case in which opposite labels can occur on
one bare edge.  Silent-choice occurrences with the same target remain
identified by the underlying quotient-graph `Walk` API and cannot create two
distinct `InputLabelledFullStep`s here.

The final theorem applies this aligned-step fact to two nonempty sibling
cells indexed by one fixed canonical walk.  Their rational cell indicators
factor exactly through opposite literals, with coordinate-free frozen
factors.  This is still a per-walk-cell statement; it supplies no uniform
coordinate across different walk pairs, decomposition-size estimate,
packing bound, or correlation bound.
-/

noncomputable section

open FiniteBooleanFourier
open FiniteBooleanOppositeLiteralCorrelation
open FiniteBooleanLiteralSupportFactorization

namespace FiniteUnambiguousFBDD
namespace Walk

/-- Forgetting query labels leaves the same endpoint trace for every input
on one fixed bare walk. -/
theorem inputLabelledFullTrace_map_endpoints_eq
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (leftInput rightInput : Fin n -> Bool) :
    (walk.inputLabelledFullTrace leftInput).map
        (fun step => (step.source, step.target)) =
      (walk.inputLabelledFullTrace rightInput).map
        (fun step => (step.source, step.target)) := by
  induction walk with
  | nil vertex => rfl
  | @cons source middle target edge tail ih =>
      simp [inputLabelledFullTrace, ih]

/-- Every full step occurring in a labelled trace has the query label
prescribed by its source node and the labelling input. -/
theorem inputLabelledFullStep_query_eq_of_mem_fullTrace
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (input : Fin n -> Bool) (step : InputLabelledFullStep B)
    (hmem : step ∈ walk.inputLabelledFullTrace input) :
    InputLabelledFullStep.query? step =
      match B.node step.source with
      | .query queryIndex _ _ => some (queryIndex, input queryIndex)
      | .choice _ => none
      | .sink => none := by
  induction walk generalizing step with
  | nil vertex =>
      simp [inputLabelledFullTrace] at hmem
  | @cons source middle target edge tail ih =>
      simp only [inputLabelledFullTrace, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst step
        cases hnode : B.node source <;>
          simp [inputLabelledFullStep, hnode]
      · exact ih step htail

/-- A query-labelled full step fixes the corresponding input bit whenever
that step occurs in a labelled trace. -/
theorem input_eq_of_queryStep_mem_inputLabelledFullTrace
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (input : Fin n -> Bool) (step : InputLabelledFullStep B)
    (queryIndex : Fin n) (value : Bool)
    (hquery : InputLabelledFullStep.query? step =
      some (queryIndex, value))
    (hmem : step ∈ walk.inputLabelledFullTrace input) :
    input queryIndex = value := by
  have hshape :=
    inputLabelledFullStep_query_eq_of_mem_fullTrace walk input step hmem
  cases hnode : B.node step.source with
  | query actualIndex ifFalse ifTrue =>
      simp [hnode] at hshape
      have hpairs : (queryIndex, value) =
          (actualIndex, input actualIndex) :=
        Option.some.inj (hquery.symm.trans hshape)
      have hindex : queryIndex = actualIndex :=
        congrArg Prod.fst hpairs
      have hvalue : value = input actualIndex :=
        congrArg Prod.snd hpairs
      rw [← hindex] at hvalue
      exact hvalue.symm
  | choice children =>
      simp [hnode] at hshape
      have : some (queryIndex, value) = none := hquery.symm.trans hshape
      simp at this
  | sink =>
      simp [hnode] at hshape
      have : some (queryIndex, value) = none := hquery.symm.trans hshape
      simp at this

/-- **Aligned same-walk sibling theorem.**  Distinct equal-length sibling
extensions realized on one bare walk have the same graph endpoints and one
common query index, but complementary Boolean labels.  The query coordinate
is genuinely queried by the walk.

No compatibility, unambiguity, read-once, or full-read premise is needed for
this trace-level statement.  In particular, it remains valid when the two
query successors are the same graph vertex. -/
theorem exists_alignedOppositeQuery_of_distinct_sibling_suffixes
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (leftInput rightInput : Fin n -> Bool)
    (key : List (InputLabelledFullStep B))
    (leftStep rightStep : InputLabelledFullStep B)
    (hleft : leftStep :: key <:+
      walk.inputLabelledFullTrace leftInput)
    (hright : rightStep :: key <:+
      walk.inputLabelledFullTrace rightInput)
    (hne : leftStep ≠ rightStep) :
    ∃ vertex nextVertex queryIndex value,
      leftStep.source = vertex ∧
        rightStep.source = vertex ∧
          leftStep.target = nextVertex ∧
            rightStep.target = nextVertex ∧
              InputLabelledFullStep.query? leftStep =
                  some (queryIndex, value) ∧
                InputLabelledFullStep.query? rightStep =
                    some (queryIndex, !value) ∧
                  queryIndex ∈ walk.queryVars := by
  let endpoint := fun step : InputLabelledFullStep B =>
    (step.source, step.target)
  have hleftMap := hleft.map endpoint
  have hrightMap := hright.map endpoint
  have hmapTrace :=
    inputLabelledFullTrace_map_endpoints_eq walk leftInput rightInput
  change (walk.inputLabelledFullTrace leftInput).map endpoint =
    (walk.inputLabelledFullTrace rightInput).map endpoint at hmapTrace
  rw [hmapTrace] at hleftMap
  have hmapKeys :
      (leftStep :: key).map endpoint =
        (rightStep :: key).map endpoint := by
    rcases List.suffix_or_suffix_of_suffix hleftMap hrightMap with
      hleftRight | hrightLeft
    · exact hleftRight.eq_of_length (by simp)
    · exact (hrightLeft.eq_of_length (by simp)).symm
  simp only [List.map_cons, List.cons.injEq] at hmapKeys
  have hsource : leftStep.source = rightStep.source :=
    congrArg Prod.fst hmapKeys.1
  have htarget : leftStep.target = rightStep.target :=
    congrArg Prod.snd hmapKeys.1
  have hleftMem : leftStep ∈ walk.inputLabelledFullTrace leftInput :=
    hleft.subset (by simp)
  have hrightMem : rightStep ∈ walk.inputLabelledFullTrace rightInput :=
    hright.subset (by simp)
  have hleftQuery :=
    inputLabelledFullStep_query_eq_of_mem_fullTrace
      walk leftInput leftStep hleftMem
  have hrightQuery :=
    inputLabelledFullStep_query_eq_of_mem_fullTrace
      walk rightInput rightStep hrightMem
  rw [← hsource] at hrightQuery
  have hqueryNe : InputLabelledFullStep.query? leftStep ≠
      InputLabelledFullStep.query? rightStep := by
    intro hquery
    apply hne
    rcases leftStep with ⟨leftSource, leftTarget, leftQuery⟩
    rcases rightStep with ⟨rightSource, rightTarget, rightQuery⟩
    simp only at hsource htarget hquery ⊢
    simp [hsource, htarget, hquery]
  cases hnode : B.node leftStep.source with
  | query queryIndex ifFalse ifTrue =>
      simp [hnode] at hleftQuery hrightQuery
      have hvalue : leftInput queryIndex ≠ rightInput queryIndex := by
        intro hsame
        exact hqueryNe (by rw [hleftQuery, hrightQuery, hsame])
      have hopposite : rightInput queryIndex = !leftInput queryIndex := by
        cases hleftValue : leftInput queryIndex <;>
          cases hrightValue : rightInput queryIndex <;>
            simp_all
      have hleftEvent :
          ({ vertex := leftStep.source
             queryIndex := queryIndex
             value := leftInput queryIndex } : InputLabelledQueryEvent B) ∈
            walk.inputLabelledQueryTrace leftInput := by
        rw [← walk.inputLabelledFullTrace_filterMap_queryEvent? leftInput]
        apply (List.mem_filterMap).2
        refine ⟨leftStep, hleftMem, ?_⟩
        simp [InputLabelledFullStep.queryEvent?, hleftQuery]
      have hqueryVar : queryIndex ∈ walk.queryVars := by
        have hindexMem : queryIndex ∈
            (walk.inputLabelledQueryTrace leftInput).map
              InputLabelledQueryEvent.queryIndex := by
          apply List.mem_map.mpr
          exact ⟨{
            vertex := leftStep.source
            queryIndex := queryIndex
            value := leftInput queryIndex
          }, hleftEvent, rfl⟩
        simpa [inputLabelledQueryTrace, queryVars, queryTrace] using hindexMem
      exact ⟨leftStep.source, leftStep.target, queryIndex,
        leftInput queryIndex, rfl, hsource.symm, rfl, htarget.symm,
        hleftQuery, by simpa [hopposite] using hrightQuery, hqueryVar⟩
  | choice children =>
      simp [hnode] at hleftQuery hrightQuery
      exact (hqueryNe (hleftQuery.trans hrightQuery.symm)).elim
  | sink =>
      simp [hnode] at hleftQuery hrightQuery
      exact (hqueryNe (hleftQuery.trans hrightQuery.symm)).elim

end Walk

/-- A canonical-walk suffix cell is realized when some accepted model in the
walk fiber has the specified labelled suffix. -/
def CanonicalWalkSuffixConeCellRealized
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) : Prop :=
  ∃ accepted : B.AcceptedModel,
    B.canonicalAcceptingWalk accepted = walk ∧
      key <:+ B.canonicalInputLabelledFullTrace accepted

/-- A full-step query label forces every point mass contributing to the
corresponding canonical-walk cell to lie on the indicated coordinate slice. -/
theorem canonicalWalkSuffixConeCellIndicator_eq_zero_of_queryStep
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (walk : B.Walk B.start B.accept)
    (key : List (InputLabelledFullStep B))
    (step : InputLabelledFullStep B)
    (queryIndex : Fin n) (value : Bool)
    (hquery : InputLabelledFullStep.query? step =
      some (queryIndex, value))
    (input : Fin n -> Bool) (hvalue : input queryIndex ≠ value) :
    B.canonicalWalkSuffixConeCellIndicator (step :: key) walk input = 0 := by
  classical
  unfold canonicalWalkSuffixConeCellIndicator
  apply Finset.sum_eq_zero
  intro accepted haccepted
  by_cases hsuffix : step :: key <:+
      B.canonicalInputLabelledFullTrace accepted
  · rw [if_pos hsuffix]
    by_cases hinput : input = accepted.1
    · subst input
      have hstepMem : step ∈
          (B.canonicalAcceptingWalk accepted).inputLabelledFullTrace
            accepted.1 := by
        have hmemCanonical : step ∈
            B.canonicalInputLabelledFullTrace accepted :=
          hsuffix.subset (by simp)
        simpa [canonicalInputLabelledFullTrace] using hmemCanonical
      have hacceptedValue : accepted.1 queryIndex = value :=
        Walk.input_eq_of_queryStep_mem_inputLabelledFullTrace
          (B.canonicalAcceptingWalk accepted) accepted.1 step
          queryIndex value hquery hstepMem
      exact (hvalue hacceptedValue).elim
    · simp [ratAcceptedPointIndicator, hinput]
  · simp [hsuffix]

/-- **Same-walk sibling-cell factorization.**  If two distinct sibling cells
for one canonical bare walk are both realized, their cell indicators factor
through opposite literals at a coordinate queried by that walk.  The two
frozen factors are independent of the separating coordinate.

This theorem is local to the displayed walk and sibling pair.  It does not
choose one coordinate for cells indexed by other walks. -/
theorem exists_oppositeLiteralFactorization_sameWalkSiblingCells
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (walk : B.Walk B.start B.accept)
    (key : List (InputLabelledFullStep B))
    (leftStep rightStep : InputLabelledFullStep B)
    (hne : leftStep ≠ rightStep)
    (hleftRealized : B.CanonicalWalkSuffixConeCellRealized
      (leftStep :: key) walk)
    (hrightRealized : B.CanonicalWalkSuffixConeCellRealized
      (rightStep :: key) walk) :
    ∃ coordinate : Fin n,
      ∃ leftFactor rightFactor : (Fin n -> Bool) -> Rat,
        coordinate ∈ walk.queryVars ∧
          DependsOnlyOn (Finset.univ.erase coordinate) leftFactor ∧
            DependsOnlyOn (Finset.univ.erase coordinate) rightFactor ∧
              ((B.canonicalWalkSuffixConeCellIndicator
                    (leftStep :: key) walk =
                    falseLiteralPart coordinate leftFactor ∧
                  B.canonicalWalkSuffixConeCellIndicator
                    (rightStep :: key) walk =
                    trueLiteralPart coordinate rightFactor) ∨
                (B.canonicalWalkSuffixConeCellIndicator
                    (leftStep :: key) walk =
                    trueLiteralPart coordinate leftFactor ∧
                  B.canonicalWalkSuffixConeCellIndicator
                    (rightStep :: key) walk =
                    falseLiteralPart coordinate rightFactor)) := by
  obtain ⟨leftAccepted, hleftWalk, hleftSuffix⟩ := hleftRealized
  obtain ⟨rightAccepted, hrightWalk, hrightSuffix⟩ := hrightRealized
  have hleftSuffix' : leftStep :: key <:+
      walk.inputLabelledFullTrace leftAccepted.1 := by
    simpa [canonicalInputLabelledFullTrace, hleftWalk] using hleftSuffix
  have hrightSuffix' : rightStep :: key <:+
      walk.inputLabelledFullTrace rightAccepted.1 := by
    simpa [canonicalInputLabelledFullTrace, hrightWalk] using hrightSuffix
  obtain ⟨vertex, nextVertex, coordinate, value,
      hleftSource, hrightSource, hleftTarget, hrightTarget,
      hleftQuery, hrightQuery, hcoordinate⟩ :=
    walk.exists_alignedOppositeQuery_of_distinct_sibling_suffixes
      leftAccepted.1 rightAccepted.1 key leftStep rightStep
      hleftSuffix' hrightSuffix' hne
  cases value with
  | false =>
      have hleftVanish : ∀ input,
          input coordinate = true ->
            B.canonicalWalkSuffixConeCellIndicator
              (leftStep :: key) walk input = 0 := by
        intro input hvalue
        apply B.canonicalWalkSuffixConeCellIndicator_eq_zero_of_queryStep
          walk key leftStep coordinate false hleftQuery input
        simp [hvalue]
      have hrightVanish : ∀ input,
          input coordinate = false ->
            B.canonicalWalkSuffixConeCellIndicator
              (rightStep :: key) walk input = 0 := by
        intro input hvalue
        apply B.canonicalWalkSuffixConeCellIndicator_eq_zero_of_queryStep
          walk key rightStep coordinate true (by simpa using hrightQuery) input
        simp [hvalue]
      obtain ⟨hleftFactorization, hrightFactorization,
          hleftFactor, hrightFactor⟩ :=
        paired_literal_support_factorization coordinate
          (B.canonicalWalkSuffixConeCellIndicator
            (leftStep :: key) walk)
          (B.canonicalWalkSuffixConeCellIndicator
            (rightStep :: key) walk)
          hleftVanish hrightVanish
      exact ⟨coordinate,
        freezeCoordinate coordinate false
          (B.canonicalWalkSuffixConeCellIndicator
            (leftStep :: key) walk),
        freezeCoordinate coordinate true
          (B.canonicalWalkSuffixConeCellIndicator
            (rightStep :: key) walk),
        hcoordinate, hleftFactor, hrightFactor,
        Or.inl ⟨hleftFactorization, hrightFactorization⟩⟩
  | true =>
      have hleftVanish : ∀ input,
          input coordinate = false ->
            B.canonicalWalkSuffixConeCellIndicator
              (leftStep :: key) walk input = 0 := by
        intro input hvalue
        apply B.canonicalWalkSuffixConeCellIndicator_eq_zero_of_queryStep
          walk key leftStep coordinate true hleftQuery input
        simp [hvalue]
      have hrightVanish : ∀ input,
          input coordinate = true ->
            B.canonicalWalkSuffixConeCellIndicator
              (rightStep :: key) walk input = 0 := by
        intro input hvalue
        apply B.canonicalWalkSuffixConeCellIndicator_eq_zero_of_queryStep
          walk key rightStep coordinate false (by simpa using hrightQuery) input
        simp [hvalue]
      obtain ⟨hrightFactorization, hleftFactorization,
          hrightFactor, hleftFactor⟩ :=
        paired_literal_support_factorization coordinate
          (B.canonicalWalkSuffixConeCellIndicator
            (rightStep :: key) walk)
          (B.canonicalWalkSuffixConeCellIndicator
            (leftStep :: key) walk)
          hrightVanish hleftVanish
      exact ⟨coordinate,
        freezeCoordinate coordinate true
          (B.canonicalWalkSuffixConeCellIndicator
            (leftStep :: key) walk),
        freezeCoordinate coordinate false
          (B.canonicalWalkSuffixConeCellIndicator
            (rightStep :: key) walk),
        hcoordinate, hleftFactor, hrightFactor,
        Or.inr ⟨hleftFactorization, hrightFactorization⟩⟩

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
