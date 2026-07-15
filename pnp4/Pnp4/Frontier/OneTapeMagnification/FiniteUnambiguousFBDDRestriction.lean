import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDD

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Closure of finite uFBDDs under partial assignments

A fixed query is replaced by a silent singleton choice leading to the branch
selected by the partial assignment.  Unfixed queries and all existing choice
vertices are left unchanged.  The construction uses exactly the original
vertex type and rank, so it neither copies nor adds vertices.
-/

/-- A partial Boolean assignment; `none` leaves a coordinate free. -/
abbrev BooleanPartialAssignment (n : Nat) := Fin n -> Option Bool

/-- Override a total input by the coordinates fixed by a partial assignment. -/
def BooleanPartialAssignment.override {n : Nat}
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool) :
    Fin n -> Bool := fun queryIndex =>
  match assignment queryIndex with
  | none => input queryIndex
  | some value => value

/-- Coordinates left free by a partial assignment. -/
def BooleanPartialAssignment.freeVariables {n : Nat}
    (assignment : BooleanPartialAssignment n) : Finset (Fin n) :=
  Finset.univ.filter fun queryIndex => assignment queryIndex = none

@[simp]
theorem BooleanPartialAssignment.mem_freeVariables_iff {n : Nat}
    (assignment : BooleanPartialAssignment n) (queryIndex : Fin n) :
    queryIndex ∈ assignment.freeVariables <->
      assignment queryIndex = none := by
  simp [BooleanPartialAssignment.freeVariables]

namespace FiniteUFBDDNode

/-- Restrict a node by replacing a fixed query with its selected successor as
a silent singleton choice. -/
def restrictBy {n : Nat} {Vertex : Type}
    (assignment : BooleanPartialAssignment n) :
    FiniteUFBDDNode n Vertex -> FiniteUFBDDNode n Vertex
  | .query queryIndex ifFalse ifTrue =>
      match assignment queryIndex with
      | none => .query queryIndex ifFalse ifTrue
      | some false => .choice [ifFalse]
      | some true => .choice [ifTrue]
  | .choice children => .choice children
  | .sink => .sink

/-- Every edge surviving restriction was already an edge of the original
node. -/
theorem hasChild_of_restrictBy_hasChild {n : Nat} {Vertex : Type}
    (assignment : BooleanPartialAssignment n)
    (node : FiniteUFBDDNode n Vertex) (target : Vertex)
    (hchild : (node.restrictBy assignment).HasChild target) :
    node.HasChild target := by
  cases node with
  | query queryIndex ifFalse ifTrue =>
      cases hassignment : assignment queryIndex with
      | none =>
          simpa [restrictBy, HasChild, hassignment] using hchild
      | some value =>
          cases value with
          | false =>
              simp [restrictBy, HasChild, hassignment] at hchild
              exact Or.inl hchild
          | true =>
              simp [restrictBy, HasChild, hassignment] at hchild
              exact Or.inr hchild
  | choice children =>
      simpa [restrictBy, HasChild] using hchild
  | sink =>
      simp [restrictBy, HasChild] at hchild

end FiniteUFBDDNode

namespace FiniteUnambiguousFBDD

/-- Restrict an FBDD without changing its vertex set or rank. -/
def restrictBy {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) : FiniteUnambiguousFBDD n where
  Vertex := B.Vertex
  vertexFintype := B.vertexFintype
  vertexDecidableEq := B.vertexDecidableEq
  start := B.start
  accept := B.accept
  node vertex := (B.node vertex).restrictBy assignment
  accept_sink := by
    simp [FiniteUFBDDNode.restrictBy, B.accept_sink]
  rank := B.rank
  rank_child := by
    intro source target hchild
    exact B.rank_child
      (FiniteUFBDDNode.hasChild_of_restrictBy_hasChild
        assignment (B.node source) target hchild)

@[simp]
theorem restrictBy_start {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) :
    (B.restrictBy assignment).start = B.start := rfl

@[simp]
theorem restrictBy_accept {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) :
    (B.restrictBy assignment).accept = B.accept := rfl

/-- Restriction preserves the vertex count exactly. -/
theorem restrictBy_vertex_card {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) :
    @Fintype.card (B.restrictBy assignment).Vertex
        (B.restrictBy assignment).vertexFintype =
      @Fintype.card B.Vertex B.vertexFintype := rfl

/-- A restricted compatible edge is exactly an original edge compatible with
the overridden total input. -/
theorem restrictBy_compatibleEdge_iff
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool)
    (source target : B.Vertex) :
    (B.restrictBy assignment).CompatibleEdge input source target <->
      B.CompatibleEdge (assignment.override input) source target := by
  cases hnode : B.node source with
  | query queryIndex ifFalse ifTrue =>
      cases hassignment : assignment queryIndex with
      | none =>
          cases hinput : input queryIndex <;>
            simp [CompatibleEdge, restrictBy, FiniteUFBDDNode.restrictBy,
              BooleanPartialAssignment.override, hnode, hassignment, hinput]
      | some value =>
          cases value <;>
            simp [CompatibleEdge, restrictBy, FiniteUFBDDNode.restrictBy,
              BooleanPartialAssignment.override, hnode, hassignment]
  | choice children =>
      simp [CompatibleEdge, restrictBy, FiniteUFBDDNode.restrictBy,
        hnode]
  | sink =>
      simp [CompatibleEdge, restrictBy, FiniteUFBDDNode.restrictBy,
        hnode]

/-- Every restricted graph edge is an original graph edge. -/
theorem edge_of_restrictBy_edge
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) {source target : B.Vertex}
    (edge : (B.restrictBy assignment).Edge source target) :
    B.Edge source target :=
  FiniteUFBDDNode.hasChild_of_restrictBy_hasChild
    assignment (B.node source) target edge

namespace Walk

/-- Forget that a walk lives in the restricted diagram.  Its vertex sequence
is unchanged and every surviving edge is an original edge. -/
def toOriginal {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} {source target : B.Vertex} :
    (B.restrictBy assignment).Walk source target -> B.Walk source target
  | .nil vertex =>
      @FiniteUnambiguousFBDD.Walk.nil n B vertex
  | .cons edge tail =>
      @FiniteUnambiguousFBDD.Walk.cons n B _ _ _
        (B.edge_of_restrictBy_edge assignment edge)
        (toOriginal (B := B) (assignment := assignment) tail)

/-- Compatibility of a restricted walk is exactly compatibility of the same
vertex sequence in the original diagram under the overridden input. -/
theorem toOriginal_compatible_iff
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool)
    {source target : B.Vertex}
    (walk : (B.restrictBy assignment).Walk source target) :
    FiniteUnambiguousFBDD.Walk.Compatible
        (B := B.restrictBy assignment) input walk <->
      FiniteUnambiguousFBDD.Walk.Compatible
        (B := B) (assignment.override input)
          (toOriginal (B := B) (assignment := assignment) walk) := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      FiniteUnambiguousFBDD.Walk.Compatible
          (B := B.restrictBy assignment) input currentWalk <->
        FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (assignment.override input)
            (toOriginal (B := B) (assignment := assignment) currentWalk))
    walk ?_ ?_
  · intro vertex
    simp [toOriginal, Compatible]
  · intro source middle target edge tail ih
    simp only [Compatible, toOriginal]
    rw [B.restrictBy_compatibleEdge_iff assignment input source middle, ih]

/-- Rebuild a restricted walk from an original walk compatible with the
overridden input.  Compatibility guarantees that every fixed query uses the
unique branch retained by the restriction. -/
def toRestrictedOfCompatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool) :
    {source target : B.Vertex} ->
    (walk : B.Walk source target) ->
    FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (assignment.override input) walk ->
    (B.restrictBy assignment).Walk source target
  | _, _, .nil vertex, _ =>
      @FiniteUnambiguousFBDD.Walk.nil n
        (B.restrictBy assignment) vertex
  | _, _, .cons (source := source) (middle := middle) _edge tail,
      hcompatible =>
      @FiniteUnambiguousFBDD.Walk.cons n
        (B.restrictBy assignment) source middle _
          ((B.restrictBy assignment).edge_of_compatibleEdge input
            ((B.restrictBy_compatibleEdge_iff
              assignment input source middle).mpr hcompatible.1))
          (toRestrictedOfCompatible input tail hcompatible.2)

/-- The rebuilt restricted walk is compatible with the free input. -/
theorem toRestrictedOfCompatible_compatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool)
    {source target : B.Vertex} (walk : B.Walk source target)
    (hcompatible : FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (assignment.override input) walk) :
    FiniteUnambiguousFBDD.Walk.Compatible
      (B := B.restrictBy assignment) input
        (toRestrictedOfCompatible input walk hcompatible) := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      forall hcurrent : FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (assignment.override input) currentWalk,
        FiniteUnambiguousFBDD.Walk.Compatible
          (B := B.restrictBy assignment) input
            (toRestrictedOfCompatible input currentWalk hcurrent))
    walk ?_ ?_) hcompatible
  · intro vertex _hcurrent
    cases _hcurrent
    rw [toRestrictedOfCompatible]
    change True
    trivial
  · intro source middle target edge tail ih hcurrent
    rcases hcurrent with ⟨hhead, htail⟩
    rw [toRestrictedOfCompatible]
    change (B.restrictBy assignment).CompatibleEdge input source middle ∧
      FiniteUnambiguousFBDD.Walk.Compatible
        (B := B.restrictBy assignment) input
          (toRestrictedOfCompatible input tail htail)
    exact ⟨(B.restrictBy_compatibleEdge_iff
      assignment input source middle).mpr hhead,
      ih htail⟩

/-- Forgetting after rebuilding returns the original compatible walk. -/
theorem toOriginal_toRestrictedOfCompatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n} (input : Fin n -> Bool)
    {source target : B.Vertex} (walk : B.Walk source target)
    (hcompatible : FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (assignment.override input) walk) :
    toOriginal (B := B) (assignment := assignment)
        (toRestrictedOfCompatible input walk hcompatible) = walk := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      forall hcurrent : FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (assignment.override input) currentWalk,
        toOriginal (B := B) (assignment := assignment)
            (toRestrictedOfCompatible input currentWalk hcurrent) =
          currentWalk)
    walk ?_ ?_) hcompatible
  · intro vertex _hcurrent
    cases _hcurrent
    rw [toRestrictedOfCompatible]
    rfl
  · intro source middle target edge tail ih hcurrent
    rcases hcurrent with ⟨hhead, htail⟩
    rw [toRestrictedOfCompatible]
    change @FiniteUnambiguousFBDD.Walk.cons n B source middle target _
        (toOriginal (B := B) (assignment := assignment)
          (toRestrictedOfCompatible input tail htail)) =
      @FiniteUnambiguousFBDD.Walk.cons n B source middle target edge tail
    rw [ih htail]

/-- Restriction deletes exactly the query events at fixed coordinates. -/
theorem queryTrace_eq_filter_toOriginal
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex}
    (walk : (B.restrictBy assignment).Walk source target) :
    walk.queryTrace =
      (toOriginal (B := B) (assignment := assignment) walk).queryTrace.filter
        (fun queryIndex => assignment queryIndex = none) := by
  classical
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      currentWalk.queryTrace =
        (toOriginal (B := B) (assignment := assignment)
          currentWalk).queryTrace.filter
            (fun queryIndex => assignment queryIndex = none))
    walk ?_ ?_
  · intro vertex
    rfl
  · intro source middle target edge tail ih
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        cases hassignment : assignment queryIndex with
        | none =>
            simp [queryTrace, queryEvents, toOriginal, restrictBy,
              FiniteUFBDDNode.restrictBy, FiniteUFBDDNode.queryEvent?,
              hnode, hassignment]
            simpa [queryTrace] using ih
        | some value =>
            cases value <;>
              simp [queryTrace, queryEvents, toOriginal, restrictBy,
                FiniteUFBDDNode.restrictBy, FiniteUFBDDNode.queryEvent?,
                hnode, hassignment] <;>
              simpa [queryTrace] using ih
    | choice children =>
        simp [queryTrace, queryEvents, toOriginal, restrictBy,
          FiniteUFBDDNode.restrictBy, FiniteUFBDDNode.queryEvent?, hnode]
        simpa [queryTrace] using ih
    | sink =>
        simp [Edge, restrictBy, FiniteUFBDDNode.restrictBy,
          FiniteUFBDDNode.HasChild, hnode] at edge

/-- Every nonempty walk vertex list starts at its indexed source. -/
theorem vertices_head?_eq_some
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target) :
    walk.vertices.head? = some source := by
  cases walk <;> rfl

/-- With fixed endpoints, a walk is determined by its vertex sequence. -/
theorem eq_of_vertices_eq
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex}
    (left right : B.Walk source target)
    (hvertices : left.vertices = right.vertices) :
    left = right := by
  induction left with
  | nil vertex =>
      cases right with
      | nil => rfl
      | cons edge tail =>
          cases tail <;> simp [vertices] at hvertices
  | @cons source middle target edge tail ih =>
      cases right with
      | nil vertex =>
          cases tail <;> simp [vertices] at hvertices
      | @cons _ otherMiddle _ otherEdge otherTail =>
          have htailVertices : tail.vertices = otherTail.vertices := by
            simpa [vertices] using hvertices
          have hmiddle : middle = otherMiddle := by
            have hhead := congrArg List.head? htailVertices
            rw [vertices_head?_eq_some tail,
              vertices_head?_eq_some otherTail] at hhead
            exact Option.some.inj hhead
          subst otherMiddle
          have htail : tail = otherTail := ih otherTail htailVertices
          cases htail
          rfl

/-- Forgetting restriction preserves the full vertex sequence. -/
theorem toOriginal_vertices
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex}
    (walk : (B.restrictBy assignment).Walk source target) :
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
    simp [toOriginal, vertices, ih]

/-- No two restricted walks are identified when restriction is forgotten. -/
theorem toOriginal_injective
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {assignment : BooleanPartialAssignment n}
    {source target : B.Vertex} :
    Function.Injective
      (toOriginal (B := B) (assignment := assignment) :
        (B.restrictBy assignment).Walk source target ->
          B.Walk source target) := by
  intro left right heq
  apply eq_of_vertices_eq left right
  rw [← toOriginal_vertices (B := B) (assignment := assignment) left,
    ← toOriginal_vertices (B := B) (assignment := assignment) right,
    heq]

end Walk

/-- Exact acceptance semantics of restriction. -/
theorem restrictBy_accepts_iff
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (input : Fin n -> Bool) :
    (B.restrictBy assignment).Accepts input <->
      B.Accepts (assignment.override input) := by
  constructor
  · rintro ⟨path⟩
    refine ⟨⟨Walk.toOriginal (B := B) (assignment := assignment)
      path.walk, ?_⟩⟩
    exact (Walk.toOriginal_compatible_iff
      (B := B) (assignment := assignment) input path.walk).mp
        path.compatible
  · rintro ⟨path⟩
    let restrictedWalk := Walk.toRestrictedOfCompatible
      (B := B) (assignment := assignment) input path.walk path.compatible
    refine ⟨⟨restrictedWalk, ?_⟩⟩
    exact Walk.toRestrictedOfCompatible_compatible
      (B := B) (assignment := assignment) input path.walk path.compatible

/-- Restriction can only remove prefix variables and every remaining prefix
variable is free. -/
theorem restrictBy_preVars_subset_original_inter_freeVariables
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (vertex : B.Vertex) :
    (B.restrictBy assignment).preVars vertex ⊆
      B.preVars vertex ∩ assignment.freeVariables := by
  intro queryIndex hqueryIndex
  rw [(B.restrictBy assignment).mem_preVars_iff] at hqueryIndex
  rcases hqueryIndex with ⟨walk, htrace⟩
  have htraceEq := Walk.queryTrace_eq_filter_toOriginal
    (B := B) (assignment := assignment) walk
  rw [htraceEq] at htrace
  have hfiltered := List.mem_filter.mp htrace
  rw [Finset.mem_inter]
  constructor
  · rw [B.mem_preVars_iff]
    exact ⟨Walk.toOriginal (B := B) (assignment := assignment) walk,
      hfiltered.1⟩
  · rw [BooleanPartialAssignment.mem_freeVariables_iff]
    exact of_decide_eq_true hfiltered.2

/-- Restriction can only remove accepting-suffix variables and every
remaining suffix variable is free. -/
theorem restrictBy_postVars_subset_original_inter_freeVariables
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n) (vertex : B.Vertex) :
    (B.restrictBy assignment).postVars vertex ⊆
      B.postVars vertex ∩ assignment.freeVariables := by
  intro queryIndex hqueryIndex
  rw [(B.restrictBy assignment).mem_postVars_iff] at hqueryIndex
  rcases hqueryIndex with ⟨walk, htrace⟩
  have htraceEq := Walk.queryTrace_eq_filter_toOriginal
    (B := B) (assignment := assignment) walk
  rw [htraceEq] at htrace
  have hfiltered := List.mem_filter.mp htrace
  rw [Finset.mem_inter]
  constructor
  · rw [B.mem_postVars_iff]
    exact ⟨Walk.toOriginal (B := B) (assignment := assignment) walk,
      hfiltered.1⟩
  · rw [BooleanPartialAssignment.mem_freeVariables_iff]
    exact of_decide_eq_true hfiltered.2

/-- Restriction preserves syntactic read-once: its query trace is a filtered
subsequence of the corresponding original trace. -/
theorem restrictBy_isSyntacticallyReadOnce
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n)
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    (B.restrictBy assignment).IsSyntacticallyReadOnce := by
  intro target walk
  rw [Walk.queryTrace_eq_filter_toOriginal
    (B := B) (assignment := assignment) walk]
  exact (hreadOnce target
    (Walk.toOriginal (B := B) (assignment := assignment) walk)).filter _

/-- Restriction preserves unambiguity. -/
theorem restrictBy_isUnambiguous
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (assignment : BooleanPartialAssignment n)
    (hunambiguous : B.IsUnambiguous) :
    (B.restrictBy assignment).IsUnambiguous := by
  intro input left right hleft hright
  apply Walk.toOriginal_injective
    (B := B) (assignment := assignment)
  exact hunambiguous (assignment.override input)
    (Walk.toOriginal (B := B) (assignment := assignment) left)
    (Walk.toOriginal (B := B) (assignment := assignment) right)
    ((Walk.toOriginal_compatible_iff
      (B := B) (assignment := assignment) input left).mp hleft)
    ((Walk.toOriginal_compatible_iff
      (B := B) (assignment := assignment) input right).mp hright)

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
