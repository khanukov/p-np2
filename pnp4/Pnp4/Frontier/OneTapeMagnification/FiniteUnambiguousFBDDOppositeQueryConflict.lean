import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPFourierKernel

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Opposite-query conflicts between distinct accepting walks

Two different accepting walks of an unambiguous branching DAG cannot have
compatible inputs which agree on every query coordinate common to the two
walks.  Indeed, use the left input on the variables queried by the left walk
and the right input everywhere else.  Agreement on the intersection makes
this merged input compatible with both walks, contradicting unambiguity.

Thus every such pair has a common queried coordinate carrying opposite input
labels, possibly at different query vertices.  No read-once or full-read
hypothesis is needed.  The file also packages the finite conflict set and its
least coordinate, and gives the corresponding input-labelled-full-trace
statement.
-/

noncomputable section

namespace FiniteUnambiguousFBDD

namespace Walk

/-- Common query coordinates on which the two compatible input labels are
opposite. -/
def commonOppositeQueryCoordinates
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {leftSource leftTarget rightSource rightTarget : B.Vertex}
    (left : B.Walk leftSource leftTarget)
    (right : B.Walk rightSource rightTarget)
    (leftInput rightInput : Fin n -> Bool) : Finset (Fin n) :=
  (left.queryVars ∩ right.queryVars).filter fun coordinate =>
    leftInput coordinate ≠ rightInput coordinate

@[simp]
theorem mem_commonOppositeQueryCoordinates
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {leftSource leftTarget rightSource rightTarget : B.Vertex}
    (left : B.Walk leftSource leftTarget)
    (right : B.Walk rightSource rightTarget)
    (leftInput rightInput : Fin n -> Bool) (coordinate : Fin n) :
    coordinate ∈ left.commonOppositeQueryCoordinates right
        leftInput rightInput ↔
      coordinate ∈ left.queryVars ∧
        coordinate ∈ right.queryVars ∧
          leftInput coordinate ≠ rightInput coordinate := by
  simp [commonOppositeQueryCoordinates, and_assoc]

/-- Merge two inputs using the left input on the variables queried by the
left walk and the right input on every other coordinate. -/
def leftBiasedQueryMerge
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (left : B.Walk source target)
    (leftInput rightInput : Fin n -> Bool) : Fin n -> Bool :=
  fun coordinate =>
    if coordinate ∈ left.queryVars then leftInput coordinate
    else rightInput coordinate

@[simp]
theorem leftBiasedQueryMerge_eq_left
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (left : B.Walk source target)
    (leftInput rightInput : Fin n -> Bool) {coordinate : Fin n}
    (hcoordinate : coordinate ∈ left.queryVars) :
    left.leftBiasedQueryMerge leftInput rightInput coordinate =
      leftInput coordinate := by
  simp [leftBiasedQueryMerge, hcoordinate]

@[simp]
theorem leftBiasedQueryMerge_eq_right
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (left : B.Walk source target)
    (leftInput rightInput : Fin n -> Bool) {coordinate : Fin n}
    (hcoordinate : coordinate ∉ left.queryVars) :
    left.leftBiasedQueryMerge leftInput rightInput coordinate =
      rightInput coordinate := by
  simp [leftBiasedQueryMerge, hcoordinate]

/-- **Pairwise opposite-query witness.**  Distinct accepting walks with
their own compatible inputs have a common query coordinate on which those
inputs carry opposite Boolean labels.  The query may occur at different graph
vertices on the two walks. -/
theorem exists_commonOppositeQuery_of_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftInput rightInput : Fin n -> Bool)
    (hleft : left.Compatible leftInput)
    (hright : right.Compatible rightInput)
    (hne : left ≠ right) :
    ∃ coordinate : Fin n,
      coordinate ∈ left.queryVars ∧
        coordinate ∈ right.queryVars ∧
          leftInput coordinate ≠ rightInput coordinate := by
  by_contra hconflict
  have hagrees : ∀ coordinate : Fin n,
      coordinate ∈ left.queryVars ->
        coordinate ∈ right.queryVars ->
          leftInput coordinate = rightInput coordinate := by
    intro coordinate hleftQuery hrightQuery
    by_contra hneValue
    exact hconflict ⟨coordinate, hleftQuery, hrightQuery, hneValue⟩
  let merged := left.leftBiasedQueryMerge leftInput rightInput
  have hleftMerged : left.Compatible merged := by
    apply (left.compatible_iff_of_eq_on_queryVars (input := leftInput)
      (input' := merged) ?_).mp hleft
    intro coordinate hcoordinate
    simp [merged, hcoordinate]
  have hrightMerged : right.Compatible merged := by
    apply (right.compatible_iff_of_eq_on_queryVars (input := rightInput)
      (input' := merged) ?_).mp hright
    intro coordinate hrightQuery
    by_cases hleftQuery : coordinate ∈ left.queryVars
    · simp [merged, hleftQuery,
        hagrees coordinate hleftQuery hrightQuery]
    · simp [merged, hleftQuery]
  exact hne (hUnambiguous merged left right hleftMerged hrightMerged)

/-- Membership in `queryVars` supplies an actual input-labelled query event,
including the graph vertex at which the coordinate is queried. -/
theorem exists_inputLabelledQueryEvent_of_mem_queryVars
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (input : Fin n -> Bool) (coordinate : Fin n)
    (hcoordinate : coordinate ∈ walk.queryVars) :
    ∃ vertex : B.Vertex,
      ({ vertex := vertex
         queryIndex := coordinate
         value := input coordinate } : InputLabelledQueryEvent B) ∈
        walk.inputLabelledQueryTrace input := by
  have htrace : coordinate ∈ walk.queryEvents.map Prod.snd := by
    simpa [queryVars, queryTrace] using hcoordinate
  rcases List.mem_map.mp htrace with
    ⟨⟨vertex, queryIndex⟩, hevent, hqueryIndex⟩
  dsimp only at hqueryIndex
  subst queryIndex
  refine ⟨vertex, ?_⟩
  apply List.mem_map.mpr
  exact ⟨(vertex, coordinate), hevent, rfl⟩

/-- Event-level form of the structural bridge.  It exposes the two (possibly
different) query vertices carrying opposite labels at a common opposite-query
coordinate. -/
theorem exists_oppositeInputLabelledQueryEvents_of_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftInput rightInput : Fin n -> Bool)
    (hleft : left.Compatible leftInput)
    (hright : right.Compatible rightInput)
    (hne : left ≠ right) :
    ∃ coordinate : Fin n, ∃ leftVertex rightVertex : B.Vertex,
      ({ vertex := leftVertex
         queryIndex := coordinate
         value := leftInput coordinate } : InputLabelledQueryEvent B) ∈
          left.inputLabelledQueryTrace leftInput ∧
        ({ vertex := rightVertex
           queryIndex := coordinate
           value := rightInput coordinate } : InputLabelledQueryEvent B) ∈
          right.inputLabelledQueryTrace rightInput ∧
        leftInput coordinate ≠ rightInput coordinate := by
  obtain ⟨coordinate, hleftQuery, hrightQuery, hvalue⟩ :=
    exists_commonOppositeQuery_of_ne hUnambiguous left right
      leftInput rightInput hleft hright hne
  obtain ⟨leftVertex, hleftEvent⟩ :=
    left.exists_inputLabelledQueryEvent_of_mem_queryVars
      leftInput coordinate hleftQuery
  obtain ⟨rightVertex, hrightEvent⟩ :=
    right.exists_inputLabelledQueryEvent_of_mem_queryVars
      rightInput coordinate hrightQuery
  exact ⟨coordinate, leftVertex, rightVertex,
    hleftEvent, hrightEvent, hvalue⟩

/-- Finset form of the structural bridge. -/
theorem commonOppositeQueryCoordinates_nonempty_of_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftInput rightInput : Fin n -> Bool)
    (hleft : left.Compatible leftInput)
    (hright : right.Compatible rightInput)
    (hne : left ≠ right) :
    (left.commonOppositeQueryCoordinates right
      leftInput rightInput).Nonempty := by
  obtain ⟨coordinate, hleftQuery, hrightQuery, hvalue⟩ :=
    exists_commonOppositeQuery_of_ne hUnambiguous left right
      leftInput rightInput hleft hright hne
  exact ⟨coordinate, by simp [hleftQuery, hrightQuery, hvalue]⟩

/-- The least common opposite-query coordinate.  `Fin n`'s canonical linear
order makes this a deterministic witness once the walks and inputs are fixed. -/
def firstCommonOppositeQueryOfNe
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftInput rightInput : Fin n -> Bool)
    (hleft : left.Compatible leftInput)
    (hright : right.Compatible rightInput)
    (hne : left ≠ right) : Fin n :=
  (left.commonOppositeQueryCoordinates right leftInput rightInput).min'
    (commonOppositeQueryCoordinates_nonempty_of_ne hUnambiguous
      left right leftInput rightInput hleft hright hne)

/-- The canonical witness belongs to the exact conflict finset. -/
theorem firstCommonOppositeQueryOfNe_mem
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftInput rightInput : Fin n -> Bool)
    (hleft : left.Compatible leftInput)
    (hright : right.Compatible rightInput)
    (hne : left ≠ right) :
    firstCommonOppositeQueryOfNe hUnambiguous left right
        leftInput rightInput hleft hright hne ∈
      left.commonOppositeQueryCoordinates right leftInput rightInput := by
  exact Finset.min'_mem _ _

/-- Expanded specification of the canonical conflict coordinate. -/
theorem firstCommonOppositeQueryOfNe_spec
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftInput rightInput : Fin n -> Bool)
    (hleft : left.Compatible leftInput)
    (hright : right.Compatible rightInput)
    (hne : left ≠ right) :
    let coordinate := firstCommonOppositeQueryOfNe hUnambiguous left right
      leftInput rightInput hleft hright hne
    coordinate ∈ left.queryVars ∧
      coordinate ∈ right.queryVars ∧
        leftInput coordinate ≠ rightInput coordinate := by
  dsimp only
  exact (mem_commonOppositeQueryCoordinates left right
    leftInput rightInput _).1
      (firstCommonOppositeQueryOfNe_mem hUnambiguous left right
        leftInput rightInput hleft hright hne)

/-- If two compatible accepting computations have different complete
input-labelled traces, then some coordinate occurs on both walks with opposite
input labels.  This also covers the case of one common bare walk whose trace
differs only at a query with coincident graph successors. -/
theorem exists_commonOppositeQuery_of_inputLabelledFullTrace_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftInput rightInput : Fin n -> Bool)
    (hleft : left.Compatible leftInput)
    (hright : right.Compatible rightInput)
    (htrace : left.inputLabelledFullTrace leftInput ≠
      right.inputLabelledFullTrace rightInput) :
    ∃ coordinate : Fin n,
      coordinate ∈ left.queryVars ∧
        coordinate ∈ right.queryVars ∧
          leftInput coordinate ≠ rightInput coordinate := by
  by_cases hwalk : left = right
  · subst right
    by_contra hconflict
    have hagrees : ∀ coordinate : Fin n,
        coordinate ∈ left.queryVars ->
          leftInput coordinate = rightInput coordinate := by
      intro coordinate hquery
      by_contra hvalue
      exact hconflict ⟨coordinate, hquery, hquery, hvalue⟩
    exact htrace
      (left.inputLabelledFullTrace_eq_of_eq_on_queryVars
        leftInput rightInput hagrees)
  · exact exists_commonOppositeQuery_of_ne hUnambiguous left right
      leftInput rightInput hleft hright hwalk

end Walk

/-- Canonical accepting traces inherit the structural opposite-query bridge.
No completeness premise is required; trace inequality is the exact condition
which excludes differences confined to coordinates queried by neither
computation. -/
theorem exists_commonOppositeQuery_of_canonicalInputLabelledFullTrace_ne
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.AcceptedModel)
    (htrace : B.canonicalInputLabelledFullTrace left ≠
      B.canonicalInputLabelledFullTrace right) :
    ∃ coordinate : Fin n,
      coordinate ∈ (B.canonicalAcceptingWalk left).queryVars ∧
        coordinate ∈ (B.canonicalAcceptingWalk right).queryVars ∧
          left.1 coordinate ≠ right.1 coordinate := by
  apply Walk.exists_commonOppositeQuery_of_inputLabelledFullTrace_ne
    hUnambiguous (B.canonicalAcceptingWalk left)
      (B.canonicalAcceptingWalk right) left.1 right.1
      (B.canonicalAcceptingWalk_compatible left)
      (B.canonicalAcceptingWalk_compatible right)
  simpa only [canonicalInputLabelledFullTrace] using htrace

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
