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
labels, possibly at different query vertices.  More strongly, for two fixed
distinct accepting walks whose compatibility fibers are nonempty, one common
queried coordinate is opposite for every pair of inputs in the two fibers.
The proof uses coordinatewise rectangularity and remains valid for degenerate
queries with coincident successors.  No read-once or full-read hypothesis is
needed.

The file packages both input-pair and fixed-walk-pair conflict finsets and
their least coordinates, and gives the corresponding input-labelled-full-
trace statement.  The uniform coordinate still depends on the ordered walk
pair and does not assert a common literal separating larger cones of walks.
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

/-- A fixed walk has a rectangular compatibility fiber: if every queried
coordinate of `input` is realized by some (coordinate-dependent) compatible
input, then `input` itself is compatible with the walk.  This formulation is
deliberately weaker than saying that all compatible inputs agree on queried
coordinates, which is false when a query has coincident successors. -/
theorem compatible_of_pointwise_realizable
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (input : Fin n -> Bool)
    (hrealizable : ∀ coordinate, coordinate ∈ walk.queryVars →
      ∃ witness : Fin n → Bool,
        walk.Compatible witness ∧ witness coordinate = input coordinate) :
    walk.Compatible input := by
  induction walk with
  | nil vertex =>
      trivial
  | @cons source middle target edge tail ih =>
      have htail : tail.Compatible input := by
        apply ih
        intro coordinate hcoordinate
        have hwhole : coordinate ∈ (Walk.cons edge tail).queryVars := by
          simp [queryVars, queryTrace, queryEvents] at hcoordinate ⊢
          exact Or.inr hcoordinate
        obtain ⟨witness, hwitness, hvalue⟩ :=
          hrealizable coordinate hwhole
        exact ⟨witness, hwitness.2, hvalue⟩
      constructor
      · cases hnode : B.node source with
        | query queryIndex ifFalse ifTrue =>
            have hquery :
                queryIndex ∈ (Walk.cons edge tail).queryVars := by
              simp [queryVars, queryTrace, queryEvents, hnode,
                FiniteUFBDDNode.queryEvent?]
            obtain ⟨witness, hwitness, hvalue⟩ :=
              hrealizable queryIndex hquery
            simpa [CompatibleEdge, hnode, hvalue] using hwitness.1
        | choice children =>
            simp [Edge, FiniteUFBDDNode.HasChild, hnode] at edge
            simp [CompatibleEdge, hnode, edge]
        | sink =>
            simp [Edge, FiniteUFBDDNode.HasChild, hnode] at edge
      · exact htail

/-- A coordinate is uniformly opposite for two walks when it is queried by
both and every compatible input for the left walk has the opposite value from
every compatible input for the right walk.  The quantification is over the
whole compatibility fibers, including degenerate queries with coincident
successors.  As a bare universal predicate it is vacuous if either fiber is
empty; every existence, least-witness, and literal theorem below therefore
receives one compatible reference input for each walk. -/
def UniformlyOppositeQueryCoordinate
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {leftSource leftTarget rightSource rightTarget : B.Vertex}
    (left : B.Walk leftSource leftTarget)
    (right : B.Walk rightSource rightTarget)
    (coordinate : Fin n) : Prop :=
  coordinate ∈ left.queryVars ∧
    coordinate ∈ right.queryVars ∧
      ∀ leftInput rightInput : Fin n → Bool,
        left.Compatible leftInput → right.Compatible rightInput →
          leftInput coordinate ≠ rightInput coordinate

/-- The finite set of coordinates uniformly opposite for a fixed pair of
walks.  Unlike `commonOppositeQueryCoordinates`, it is independent of a
chosen pair of compatible inputs.  Membership is intentionally the universal
fiber predicate above and is vacuous for an empty fiber; the nonemptiness API
below assumes explicit compatible reference inputs. -/
def uniformlyOppositeQueryCoordinates
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {leftSource leftTarget rightSource rightTarget : B.Vertex}
    (left : B.Walk leftSource leftTarget)
    (right : B.Walk rightSource rightTarget) : Finset (Fin n) := by
  classical
  exact (left.queryVars ∩ right.queryVars).filter fun coordinate =>
    ∀ leftInput rightInput : Fin n → Bool,
      left.Compatible leftInput → right.Compatible rightInput →
        leftInput coordinate ≠ rightInput coordinate

@[simp]
theorem mem_uniformlyOppositeQueryCoordinates
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {leftSource leftTarget rightSource rightTarget : B.Vertex}
    (left : B.Walk leftSource leftTarget)
    (right : B.Walk rightSource rightTarget)
    (coordinate : Fin n) :
    coordinate ∈ left.uniformlyOppositeQueryCoordinates right ↔
      left.UniformlyOppositeQueryCoordinate right coordinate := by
  simp [uniformlyOppositeQueryCoordinates,
    UniformlyOppositeQueryCoordinate, and_assoc]

/-- **Uniform fixed-walk-pair witness.**  Distinct accepting walks with
nonempty compatibility fibers have a common queried coordinate that carries
opposite values for every pair of inputs in those two fibers.  Degenerate
queries are handled by the rectangularity lemma above rather than by the
false claim that one walk fixes every variable in its `queryVars`.

The coordinate is uniform only for this fixed ordered pair of walks; it may
change with the walk pair and does not by itself separate two larger cones of
walks. -/
theorem exists_uniformlyOppositeQueryCoordinate_of_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftReference rightReference : Fin n → Bool)
    (hleft : left.Compatible leftReference)
    (hright : right.Compatible rightReference)
    (hne : left ≠ right) :
    ∃ coordinate : Fin n,
      left.UniformlyOppositeQueryCoordinate right coordinate := by
  classical
  by_contra hnone
  let merged : Fin n → Bool := fun coordinate =>
    if hleftQuery : coordinate ∈ left.queryVars then
      if ∃ leftInput : Fin n → Bool,
          left.Compatible leftInput ∧
            leftInput coordinate = rightReference coordinate then
        rightReference coordinate
      else leftReference coordinate
    else rightReference coordinate
  have hleftMerged : left.Compatible merged := by
    apply left.compatible_of_pointwise_realizable
    intro coordinate hleftQuery
    by_cases hrealizable : ∃ leftInput : Fin n → Bool,
        left.Compatible leftInput ∧
          leftInput coordinate = rightReference coordinate
    · have hwitness := hrealizable
      obtain ⟨leftInput, hleftInput, hvalue⟩ := hwitness
      refine ⟨leftInput, hleftInput, ?_⟩
      simp [merged, hleftQuery, hrealizable, hvalue]
    · refine ⟨leftReference, hleft, ?_⟩
      simp [merged, hleftQuery, hrealizable]
  have hrightMerged : right.Compatible merged := by
    apply right.compatible_of_pointwise_realizable
    intro coordinate hrightQuery
    by_cases hleftQuery : coordinate ∈ left.queryVars
    · by_cases hrealizable : ∃ leftInput : Fin n → Bool,
          left.Compatible leftInput ∧
            leftInput coordinate = rightReference coordinate
      · refine ⟨rightReference, hright, ?_⟩
        simp [merged, hleftQuery, hrealizable]
      · have hnotOpposite :
            ¬ ∀ leftInput rightInput : Fin n → Bool,
              left.Compatible leftInput →
                right.Compatible rightInput →
                  leftInput coordinate ≠ rightInput coordinate := by
          intro hopposite
          exact hnone ⟨coordinate, hleftQuery, hrightQuery, hopposite⟩
        push_neg at hnotOpposite
        obtain ⟨leftInput, rightInput, hleftInput,
          hrightInput, hsame⟩ := hnotOpposite
        have hleftInput_ne_rightReference :
            leftInput coordinate ≠ rightReference coordinate := by
          intro hvalue
          exact hrealizable ⟨leftInput, hleftInput, hvalue⟩
        have hleftReference_ne_rightReference :
            leftReference coordinate ≠ rightReference coordinate := by
          intro hvalue
          exact hrealizable ⟨leftReference, hleft, hvalue⟩
        have hleftInput_eq_leftReference :
            leftInput coordinate = leftReference coordinate := by
          cases hleftInputValue : leftInput coordinate <;>
            cases hleftReferenceValue : leftReference coordinate <;>
              cases hrightReferenceValue : rightReference coordinate <;>
                simp_all
        refine ⟨rightInput, hrightInput, ?_⟩
        have hrightInput_eq_leftReference :
            rightInput coordinate = leftReference coordinate := by
          exact hsame.symm.trans hleftInput_eq_leftReference
        simp [merged, hleftQuery, hrealizable,
          hrightInput_eq_leftReference]
    · refine ⟨rightReference, hright, ?_⟩
      simp [merged, hleftQuery]
  exact hne (hUnambiguous merged left right hleftMerged hrightMerged)

/-- Literal form of the uniform fixed-walk-pair witness.  On one common
queried coordinate, the whole left compatibility fiber fixes one Boolean
literal and the whole right fiber fixes its negation.  This is a factorization
statement for one fixed ordered pair of walks only; the coordinate and literal
may change with the pair and need not be shared by larger walk cones. -/
theorem exists_uniformlyOppositeLiteral_of_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftReference rightReference : Fin n → Bool)
    (hleft : left.Compatible leftReference)
    (hright : right.Compatible rightReference)
    (hne : left ≠ right) :
    ∃ coordinate : Fin n, ∃ value : Bool,
      coordinate ∈ left.queryVars ∧
        coordinate ∈ right.queryVars ∧
          (∀ leftInput : Fin n → Bool,
            left.Compatible leftInput →
              leftInput coordinate = value) ∧
          (∀ rightInput : Fin n → Bool,
            right.Compatible rightInput →
              rightInput coordinate = !value) := by
  obtain ⟨coordinate, hleftQuery, hrightQuery, hopposite⟩ :=
    exists_uniformlyOppositeQueryCoordinate_of_ne hUnambiguous left right
      leftReference rightReference hleft hright hne
  refine ⟨coordinate, leftReference coordinate,
    hleftQuery, hrightQuery, ?_, ?_⟩
  · intro leftInput hleftInput
    have hleftInput_ne_rightReference :=
      hopposite leftInput rightReference hleftInput hright
    have hleftReference_ne_rightReference :=
      hopposite leftReference rightReference hleft hright
    cases hleftInputValue : leftInput coordinate <;>
      cases hleftReferenceValue : leftReference coordinate <;>
        cases hrightReferenceValue : rightReference coordinate <;>
          simp_all
  · intro rightInput hrightInput
    have hvalue := hopposite leftReference rightInput hleft hrightInput
    cases hleftReferenceValue : leftReference coordinate <;>
      cases hrightInputValue : rightInput coordinate <;>
        simp_all

/-- The uniform conflict finset for two distinct accepting walks is nonempty
as soon as each walk has one compatible input. -/
theorem uniformlyOppositeQueryCoordinates_nonempty_of_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftReference rightReference : Fin n → Bool)
    (hleft : left.Compatible leftReference)
    (hright : right.Compatible rightReference)
    (hne : left ≠ right) :
    (left.uniformlyOppositeQueryCoordinates right).Nonempty := by
  obtain ⟨coordinate, hcoordinate⟩ :=
    exists_uniformlyOppositeQueryCoordinate_of_ne hUnambiguous left right
      leftReference rightReference hleft hright hne
  exact ⟨coordinate,
    (mem_uniformlyOppositeQueryCoordinates left right coordinate).2
      hcoordinate⟩

/-- The least coordinate uniformly opposite for a fixed ordered pair of
distinct accepting walks.  The reference inputs witness only that both
compatibility fibers are nonempty; the minimized finset itself depends only
on the two walks. -/
def firstUniformlyOppositeQueryOfNe
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftReference rightReference : Fin n → Bool)
    (hleft : left.Compatible leftReference)
    (hright : right.Compatible rightReference)
    (hne : left ≠ right) : Fin n :=
  (left.uniformlyOppositeQueryCoordinates right).min'
    (uniformlyOppositeQueryCoordinates_nonempty_of_ne hUnambiguous
      left right leftReference rightReference hleft hright hne)

/-- The least fixed-walk-pair witness belongs to the uniform conflict
finset. -/
theorem firstUniformlyOppositeQueryOfNe_mem
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftReference rightReference : Fin n → Bool)
    (hleft : left.Compatible leftReference)
    (hright : right.Compatible rightReference)
    (hne : left ≠ right) :
    firstUniformlyOppositeQueryOfNe hUnambiguous left right
        leftReference rightReference hleft hright hne ∈
      left.uniformlyOppositeQueryCoordinates right := by
  exact Finset.min'_mem _ _

/-- Expanded specification of the least uniform conflict coordinate. -/
theorem firstUniformlyOppositeQueryOfNe_spec
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftReference rightReference : Fin n → Bool)
    (hleft : left.Compatible leftReference)
    (hright : right.Compatible rightReference)
    (hne : left ≠ right) :
    let coordinate := firstUniformlyOppositeQueryOfNe hUnambiguous
      left right leftReference rightReference hleft hright hne
    coordinate ∈ left.queryVars ∧
      coordinate ∈ right.queryVars ∧
        ∀ leftInput rightInput : Fin n → Bool,
          left.Compatible leftInput → right.Compatible rightInput →
            leftInput coordinate ≠ rightInput coordinate := by
  dsimp only
  exact (mem_uniformlyOppositeQueryCoordinates left right _).1
    (firstUniformlyOppositeQueryOfNe_mem hUnambiguous left right
      leftReference rightReference hleft hright hne)

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
