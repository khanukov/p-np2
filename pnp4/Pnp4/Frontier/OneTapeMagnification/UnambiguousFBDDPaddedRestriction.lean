import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDRestriction
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDHighDegreeRegrouping

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Query-preserving restrictions of finite uFBDDs

The ordinary `FiniteUnambiguousFBDD.restrictBy` replaces a fixed query by a
silent singleton choice.  That representation has the right acceptance
semantics, but its accepting paths no longer query the fixed coordinate, so a
full-read hypothesis cannot be reused after a restriction.

This file gives a semantics-equivalent padded representation.  A query fixed
to `false` is changed from `query q left right` to `query q left left`, and a
query fixed to `true` is changed to `query q right right`.  Thus the input bit
can no longer affect the transition, while the query event itself remains in
the trace.  No vertices or edges outside the selected original branch are
added.  In particular, syntactic read-once, unambiguity, and the exact
full-read property are preserved, which makes the high-degree regrouping
theorem stable under arbitrary partial assignments.
-/

namespace FiniteUFBDDNode

/-- Restrict a fixed query while retaining it as a dummy query whose two
successors coincide. -/
def paddedRestrictBy {n : Nat} {Vertex : Type}
    (assignment : BooleanPartialAssignment n) :
    FiniteUFBDDNode n Vertex -> FiniteUFBDDNode n Vertex
  | .query queryIndex ifFalse ifTrue =>
      match assignment queryIndex with
      | none => .query queryIndex ifFalse ifTrue
      | some false => .query queryIndex ifFalse ifFalse
      | some true => .query queryIndex ifTrue ifTrue
  | .choice children => .choice children
  | .sink => .sink

/-- Every edge of a padded restricted node was already an edge of the
original node. -/
theorem hasChild_of_paddedRestrictBy_hasChild
    {n : Nat} {Vertex : Type}
    (assignment : BooleanPartialAssignment n)
    (node : FiniteUFBDDNode n Vertex) (target : Vertex)
    (hchild : (node.paddedRestrictBy assignment).HasChild target) :
    node.HasChild target := by
  cases node with
  | query queryIndex ifFalse ifTrue =>
      cases hassignment : assignment queryIndex with
      | none =>
          simpa [paddedRestrictBy, HasChild, hassignment] using hchild
      | some value =>
          cases value with
          | false =>
              have htarget : target = ifFalse := by
                simpa [paddedRestrictBy, HasChild, hassignment] using hchild
              exact Or.inl htarget
          | true =>
              have htarget : target = ifTrue := by
                simpa [paddedRestrictBy, HasChild, hassignment] using hchild
              exact Or.inr htarget
  | choice children =>
      simpa [paddedRestrictBy, HasChild] using hchild
  | sink =>
      simp [paddedRestrictBy, HasChild] at hchild

end FiniteUFBDDNode

namespace FiniteUnambiguousFBDD

/-- A restriction that preserves query events by padding each fixed query
with two identical selected successors. -/
def paddedRestrictBy {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) : FiniteUnambiguousFBDD n where
  Vertex := B.Vertex
  vertexFintype := B.vertexFintype
  vertexDecidableEq := B.vertexDecidableEq
  start := B.start
  accept := B.accept
  node vertex := (B.node vertex).paddedRestrictBy assignment
  accept_sink := by
    simp [FiniteUFBDDNode.paddedRestrictBy, B.accept_sink]
  rank := B.rank
  rank_child := by
    intro source target hchild
    exact B.rank_child
      (FiniteUFBDDNode.hasChild_of_paddedRestrictBy_hasChild
        assignment (B.node source) target hchild)

@[simp]
theorem paddedRestrictBy_start {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) :
    (B.paddedRestrictBy assignment).start = B.start := rfl

@[simp]
theorem paddedRestrictBy_accept {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) :
    (B.paddedRestrictBy assignment).accept = B.accept := rfl

/-- Padded restriction preserves the vertex count exactly. -/
theorem paddedRestrictBy_vertex_card {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) :
    @Fintype.card (B.paddedRestrictBy assignment).Vertex
        (B.paddedRestrictBy assignment).vertexFintype =
      @Fintype.card B.Vertex B.vertexFintype := rfl

/-- A padded restricted compatible edge is exactly an original edge
compatible with the overridden input. -/
theorem paddedRestrictBy_compatibleEdge_iff
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool)
    (source target : B.Vertex) :
    (B.paddedRestrictBy assignment).CompatibleEdge input source target <->
      B.CompatibleEdge (assignment.override input) source target := by
  cases hnode : B.node source with
  | query queryIndex ifFalse ifTrue =>
      cases hassignment : assignment queryIndex with
      | none =>
          cases hinput : input queryIndex <;>
            simp [CompatibleEdge, paddedRestrictBy,
              FiniteUFBDDNode.paddedRestrictBy,
              BooleanPartialAssignment.override, hnode, hassignment, hinput]
      | some value =>
          cases value <;> cases hinput : input queryIndex <;>
            simp [CompatibleEdge, paddedRestrictBy,
              FiniteUFBDDNode.paddedRestrictBy,
              BooleanPartialAssignment.override, hnode, hassignment, hinput]
  | choice children =>
      simp [CompatibleEdge, paddedRestrictBy,
        FiniteUFBDDNode.paddedRestrictBy, hnode]
  | sink =>
      simp [CompatibleEdge, paddedRestrictBy,
        FiniteUFBDDNode.paddedRestrictBy, hnode]

/-- Every padded restricted graph edge is an original graph edge. -/
theorem edge_of_paddedRestrictBy_edge
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) {source target : B.Vertex}
    (edge : (B.paddedRestrictBy assignment).Edge source target) :
    B.Edge source target :=
  FiniteUFBDDNode.hasChild_of_paddedRestrictBy_hasChild
    assignment (B.node source) target edge

namespace PaddedRestrictionWalk

/-- Forget that a walk lives in the padded restricted diagram. -/
def toOriginal {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} {source target : B.Vertex} :
    (B.paddedRestrictBy assignment).Walk source target ->
      B.Walk source target
  | .nil vertex =>
      @FiniteUnambiguousFBDD.Walk.nil n B vertex
  | .cons edge tail =>
      @FiniteUnambiguousFBDD.Walk.cons n B _ _ _
        (B.edge_of_paddedRestrictBy_edge assignment edge)
        (toOriginal (B := B) (assignment := assignment) tail)

/-- Compatibility is preserved exactly under the override semantics. -/
theorem toOriginal_compatible_iff
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool)
    {source target : B.Vertex}
    (walk : (B.paddedRestrictBy assignment).Walk source target) :
    FiniteUnambiguousFBDD.Walk.Compatible
        (B := B.paddedRestrictBy assignment) input walk <->
      FiniteUnambiguousFBDD.Walk.Compatible
        (B := B) (assignment.override input)
          (toOriginal (B := B) (assignment := assignment) walk) := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      FiniteUnambiguousFBDD.Walk.Compatible
          (B := B.paddedRestrictBy assignment) input currentWalk <->
        FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (assignment.override input)
            (toOriginal (B := B) (assignment := assignment) currentWalk))
    walk ?_ ?_
  · intro vertex
    simp [toOriginal, FiniteUnambiguousFBDD.Walk.Compatible]
  · intro source middle target edge tail ih
    simp only [FiniteUnambiguousFBDD.Walk.Compatible, toOriginal]
    rw [B.paddedRestrictBy_compatibleEdge_iff
      assignment input source middle, ih]

/-- Rebuild a padded restricted walk from an original walk compatible with
the overridden input. -/
def ofOriginalCompatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool) :
    {source target : B.Vertex} ->
    (walk : B.Walk source target) ->
    FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (assignment.override input) walk ->
    (B.paddedRestrictBy assignment).Walk source target
  | _, _, .nil vertex, _ =>
      @FiniteUnambiguousFBDD.Walk.nil n
        (B.paddedRestrictBy assignment) vertex
  | _, _, .cons (source := source) (middle := middle) _edge tail,
      hcompatible =>
      @FiniteUnambiguousFBDD.Walk.cons n
        (B.paddedRestrictBy assignment) source middle _
          ((B.paddedRestrictBy assignment).edge_of_compatibleEdge input
            ((B.paddedRestrictBy_compatibleEdge_iff
              assignment input source middle).mpr hcompatible.1))
          (ofOriginalCompatible input tail hcompatible.2)

/-- The rebuilt padded walk is compatible with the unrestricted input. -/
theorem ofOriginalCompatible_compatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool)
    {source target : B.Vertex} (walk : B.Walk source target)
    (hcompatible : FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (assignment.override input) walk) :
    FiniteUnambiguousFBDD.Walk.Compatible
      (B := B.paddedRestrictBy assignment) input
        (ofOriginalCompatible input walk hcompatible) := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      forall hcurrent : FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (assignment.override input) currentWalk,
        FiniteUnambiguousFBDD.Walk.Compatible
          (B := B.paddedRestrictBy assignment) input
            (ofOriginalCompatible input currentWalk hcurrent))
    walk ?_ ?_) hcompatible
  · intro vertex hcurrent
    cases hcurrent
    rw [ofOriginalCompatible]
    trivial
  · intro source middle target edge tail ih hcurrent
    rcases hcurrent with ⟨hhead, htail⟩
    rw [ofOriginalCompatible]
    exact ⟨(B.paddedRestrictBy_compatibleEdge_iff
      assignment input source middle).mpr hhead, ih htail⟩

/-- Forgetting a rebuilt padded walk returns the original walk. -/
theorem toOriginal_ofOriginalCompatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool)
    {source target : B.Vertex} (walk : B.Walk source target)
    (hcompatible : FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (assignment.override input) walk) :
    toOriginal (B := B) (assignment := assignment)
        (ofOriginalCompatible input walk hcompatible) = walk := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      forall hcurrent : FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (assignment.override input) currentWalk,
        toOriginal (B := B) (assignment := assignment)
            (ofOriginalCompatible input currentWalk hcurrent) = currentWalk)
    walk ?_ ?_) hcompatible
  · intro vertex hcurrent
    cases hcurrent
    rw [ofOriginalCompatible]
    rfl
  · intro source middle target edge tail ih hcurrent
    rcases hcurrent with ⟨hhead, htail⟩
    rw [ofOriginalCompatible]
    change @FiniteUnambiguousFBDD.Walk.cons n B source middle target _
        (toOriginal (B := B) (assignment := assignment)
          (ofOriginalCompatible input tail htail)) =
      @FiniteUnambiguousFBDD.Walk.cons n B source middle target edge tail
    rw [ih htail]

/-- Forgetting a padded restriction preserves the full vertex sequence. -/
theorem toOriginal_vertices
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex}
    (walk : (B.paddedRestrictBy assignment).Walk source target) :
    (toOriginal (B := B) (assignment := assignment) walk).vertices =
      walk.vertices := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      (toOriginal (B := B) (assignment := assignment)
        currentWalk).vertices = currentWalk.vertices)
    walk ?_ ?_
  · intro vertex
    rfl
  · intro source middle target edge tail ih
    simp [toOriginal, FiniteUnambiguousFBDD.Walk.vertices, ih]

/-- No two padded restricted walks are identified after forgetting the
restriction. -/
theorem toOriginal_injective
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex} :
    Function.Injective
      (toOriginal (B := B) (assignment := assignment) :
        (B.paddedRestrictBy assignment).Walk source target ->
          B.Walk source target) := by
  intro left right heq
  apply FiniteUnambiguousFBDD.Walk.eq_of_vertices_eq left right
  rw [← toOriginal_vertices (B := B) (assignment := assignment) left,
    ← toOriginal_vertices (B := B) (assignment := assignment) right, heq]

/-- Unlike the silent restriction, padded restriction preserves every query
event, including events at fixed coordinates. -/
theorem toOriginal_queryEvents
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex}
    (walk : (B.paddedRestrictBy assignment).Walk source target) :
    (toOriginal (B := B) (assignment := assignment) walk).queryEvents =
      walk.queryEvents := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      (toOriginal (B := B) (assignment := assignment)
        currentWalk).queryEvents = currentWalk.queryEvents)
    walk ?_ ?_
  · intro vertex
    rfl
  · intro source middle target edge tail ih
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        cases hassignment : assignment queryIndex with
        | none =>
            simp [toOriginal, FiniteUnambiguousFBDD.Walk.queryEvents,
              paddedRestrictBy, FiniteUFBDDNode.paddedRestrictBy,
              FiniteUFBDDNode.queryEvent?, hnode, hassignment, ih]
        | some value =>
            cases value <;>
              simp [toOriginal, FiniteUnambiguousFBDD.Walk.queryEvents,
                paddedRestrictBy, FiniteUFBDDNode.paddedRestrictBy,
                FiniteUFBDDNode.queryEvent?, hnode, hassignment, ih]
    | choice children =>
        simp [toOriginal, FiniteUnambiguousFBDD.Walk.queryEvents,
          paddedRestrictBy, FiniteUFBDDNode.paddedRestrictBy,
          FiniteUFBDDNode.queryEvent?, hnode, ih]
    | sink =>
        simp [FiniteUnambiguousFBDD.Edge, paddedRestrictBy,
          FiniteUFBDDNode.paddedRestrictBy, FiniteUFBDDNode.HasChild,
          hnode] at edge

/-- Padded restriction preserves the query trace exactly. -/
theorem toOriginal_queryTrace
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex}
    (walk : (B.paddedRestrictBy assignment).Walk source target) :
    (toOriginal (B := B) (assignment := assignment) walk).queryTrace =
      walk.queryTrace := by
  simp [FiniteUnambiguousFBDD.Walk.queryTrace, toOriginal_queryEvents]

/-- Padded restriction preserves the set of queried variables exactly. -/
theorem toOriginal_queryVars
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex}
    (walk : (B.paddedRestrictBy assignment).Walk source target) :
    (toOriginal (B := B) (assignment := assignment) walk).queryVars =
      walk.queryVars := by
  simp [FiniteUnambiguousFBDD.Walk.queryVars, toOriginal_queryTrace]

end PaddedRestrictionWalk

/-- Exact acceptance semantics of padded restriction. -/
theorem paddedRestrictBy_accepts_iff
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool) :
    (B.paddedRestrictBy assignment).Accepts input <->
      B.Accepts (assignment.override input) := by
  constructor
  · rintro ⟨path⟩
    refine ⟨⟨PaddedRestrictionWalk.toOriginal
      (B := B) (assignment := assignment) path.walk, ?_⟩⟩
    exact (PaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (assignment := assignment) input path.walk).mp
        path.compatible
  · rintro ⟨path⟩
    let restrictedWalk := PaddedRestrictionWalk.ofOriginalCompatible
      (B := B) (assignment := assignment) input path.walk path.compatible
    refine ⟨⟨restrictedWalk, ?_⟩⟩
    exact PaddedRestrictionWalk.ofOriginalCompatible_compatible
      (B := B) (assignment := assignment) input path.walk path.compatible

/-- Padded and silent restrictions have identical acceptance semantics. -/
theorem paddedRestrictBy_accepts_iff_restrictBy_accepts
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool) :
    (B.paddedRestrictBy assignment).Accepts input <->
      (B.restrictBy assignment).Accepts input := by
  rw [B.paddedRestrictBy_accepts_iff,
    B.restrictBy_accepts_iff]

/-- The padded diagram computes the original acceptance indicator after the
partial assignment is applied. -/
theorem paddedRestrictBy_ratAcceptanceIndicator_eq_override
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool) :
    (B.paddedRestrictBy assignment).ratAcceptanceIndicator input =
      B.ratAcceptanceIndicator (assignment.override input) := by
  classical
  unfold ratAcceptanceIndicator
  rw [B.paddedRestrictBy_accepts_iff assignment input]

/-- Consequently the rational acceptance indicator is exactly the ordinary
restricted function, not merely an approximation to it. -/
theorem paddedRestrictBy_ratAcceptanceIndicator_eq_restrictBy
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool) :
    (B.paddedRestrictBy assignment).ratAcceptanceIndicator input =
      (B.restrictBy assignment).ratAcceptanceIndicator input := by
  classical
  unfold ratAcceptanceIndicator
  rw [B.paddedRestrictBy_accepts_iff_restrictBy_accepts assignment input]

/-- Padded restriction preserves syntactic read-once because it deletes
edges but no query events. -/
theorem paddedRestrictBy_isSyntacticallyReadOnce
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n)
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    (B.paddedRestrictBy assignment).IsSyntacticallyReadOnce := by
  intro target walk
  rw [← PaddedRestrictionWalk.toOriginal_queryTrace
    (B := B) (assignment := assignment) walk]
  exact hreadOnce target
    (PaddedRestrictionWalk.toOriginal
      (B := B) (assignment := assignment) walk)

/-- Padded restriction preserves unambiguity. -/
theorem paddedRestrictBy_isUnambiguous
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n)
    (hunambiguous : B.IsUnambiguous) :
    (B.paddedRestrictBy assignment).IsUnambiguous := by
  intro input left right hleft hright
  apply PaddedRestrictionWalk.toOriginal_injective
    (B := B) (assignment := assignment)
  exact hunambiguous (assignment.override input)
    (PaddedRestrictionWalk.toOriginal
      (B := B) (assignment := assignment) left)
    (PaddedRestrictionWalk.toOriginal
      (B := B) (assignment := assignment) right)
    ((PaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (assignment := assignment) input left).mp hleft)
    ((PaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (assignment := assignment) input right).mp hright)

/-- A full-read premise transfers exactly to every padded restriction. -/
theorem paddedRestrictBy_acceptingPath_queryVars_eq_univ
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (input : Fin n -> Bool)
    (path : (B.paddedRestrictBy assignment).AcceptingPath input) :
    path.walk.queryVars = Finset.univ := by
  let originalPath : B.AcceptingPath (assignment.override input) := {
    walk := PaddedRestrictionWalk.toOriginal
      (B := B) (assignment := assignment) path.walk
    compatible := (PaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (assignment := assignment) input path.walk).mp
        path.compatible
  }
  rw [← PaddedRestrictionWalk.toOriginal_queryVars
    (B := B) (assignment := assignment) path.walk]
  exact hreadsAll (assignment.override input) originalPath

/-- The exact high-degree Laplacian regrouping therefore survives every
partial assignment when the restriction is represented with padding. -/
theorem paddedRestrictBy_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
    {n k : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (input : Fin n -> Bool) :
    ratHighDegreeFourierTail
        (B.paddedRestrictBy assignment).ratAcceptanceIndicator k input =
      ∑ vertex : (B.paddedRestrictBy assignment).Vertex,
        (B.paddedRestrictBy assignment).ratCompatiblePrefixHomogeneousSlice
            vertex k input *
          (B.paddedRestrictBy assignment).suffixLaplacian vertex input := by
  apply
    (B.paddedRestrictBy assignment).ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
  · exact B.paddedRestrictBy_isSyntacticallyReadOnce assignment hreadOnce
  · exact B.paddedRestrictBy_isUnambiguous assignment hunambiguous
  · exact B.paddedRestrictBy_acceptingPath_queryVars_eq_univ
      assignment hreadsAll

end FiniteUnambiguousFBDD

/-! ## Mandatory canonical specialization -/

/-- Every padded restriction of the mandatory canonical diagram retains the
exact high-degree Laplacian regrouping. -/
theorem mandatoryCanonicalUFBDD_paddedRestrictBy_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b k : Nat) (hb : 0 < b)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool) :
    FiniteUnambiguousFBDD.ratHighDegreeFourierTail
        ((mandatoryCanonicalUFBDD machine n T b).paddedRestrictBy assignment).ratAcceptanceIndicator
        k input =
      ∑ vertex :
          ((mandatoryCanonicalUFBDD machine n T b).paddedRestrictBy
            assignment).Vertex,
        ((mandatoryCanonicalUFBDD machine n T b).paddedRestrictBy assignment).ratCompatiblePrefixHomogeneousSlice
            vertex k input *
          ((mandatoryCanonicalUFBDD machine n T b).paddedRestrictBy
            assignment).suffixLaplacian vertex input := by
  apply
    (mandatoryCanonicalUFBDD machine n T b).paddedRestrictBy_ratHighDegreeFourierTail_eq_sum_prefixSlice_mul_suffixLaplacian
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce machine n T b
  · exact mandatoryCanonicalUFBDD_isUnambiguous machine n T b hb
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n T b currentInput path

end OneTapeMagnification
end Frontier
end Pnp4
