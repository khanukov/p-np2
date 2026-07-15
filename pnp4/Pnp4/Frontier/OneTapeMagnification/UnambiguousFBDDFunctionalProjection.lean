import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDD

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Functional existential projection for finite unambiguous FBDDs

For a diagram on a concatenated input `(x, z)`, this module forgets the
`z`-queries by turning each of them into a silent binary choice.  The
construction keeps the original vertex carrier and rank exactly.

Read-once is needed for the forward semantic direction: every projected
accepting walk must have one globally consistent assignment to the forgotten
coordinates.  If the original acceptance relation is functional in `z`, its
unambiguity then descends to the projected diagram.
-/

namespace FiniteUFBDDNode

/-- Forget the right input block.  Left queries remain queries and right
queries become silent choices between their two original children. -/
def forgetRightQueries {n m : Nat} {Vertex : Type} :
    FiniteUFBDDNode (n + m) Vertex -> FiniteUFBDDNode n Vertex
  | .query queryIndex ifFalse ifTrue =>
      Fin.addCases
        (fun leftIndex => .query leftIndex ifFalse ifTrue)
        (fun _rightIndex => .choice [ifFalse, ifTrue])
        queryIndex
  | .choice children => .choice children
  | .sink => .sink

/-- Forgetting right queries preserves the child relation exactly. -/
theorem forgetRightQueries_hasChild_iff
    {n m : Nat} {Vertex : Type}
    (node : FiniteUFBDDNode (n + m) Vertex) (target : Vertex) :
    (node.forgetRightQueries (n := n) (m := m)).HasChild target <->
      node.HasChild target := by
  cases node with
  | query queryIndex ifFalse ifTrue =>
      refine Fin.addCases ?_ ?_ queryIndex
      · intro leftIndex
        simp [forgetRightQueries, HasChild]
      · intro rightIndex
        simp [forgetRightQueries, HasChild]
  | choice children =>
      simp [forgetRightQueries, HasChild]
  | sink =>
      simp [forgetRightQueries, HasChild]

end FiniteUFBDDNode

namespace FiniteUnambiguousFBDD

/-- Existentially forget the right input block without changing vertices or
rank. -/
def forgetRightQueries {n m : Nat}
    (B : FiniteUnambiguousFBDD (n + m)) : FiniteUnambiguousFBDD n where
  Vertex := B.Vertex
  vertexFintype := B.vertexFintype
  vertexDecidableEq := B.vertexDecidableEq
  start := B.start
  accept := B.accept
  node vertex := (B.node vertex).forgetRightQueries (n := n) (m := m)
  accept_sink := by
    simp [FiniteUFBDDNode.forgetRightQueries, B.accept_sink]
  rank := B.rank
  rank_child := by
    intro source target hchild
    exact B.rank_child
      ((FiniteUFBDDNode.forgetRightQueries_hasChild_iff
        (n := n) (m := m) (B.node source) target).mp hchild)

@[simp]
theorem forgetRightQueries_start {n m : Nat}
    (B : FiniteUnambiguousFBDD (n + m)) :
    (B.forgetRightQueries (n := n) (m := m)).start = B.start := rfl

@[simp]
theorem forgetRightQueries_accept {n m : Nat}
    (B : FiniteUnambiguousFBDD (n + m)) :
    (B.forgetRightQueries (n := n) (m := m)).accept = B.accept := rfl

@[simp]
theorem forgetRightQueries_rank {n m : Nat}
    (B : FiniteUnambiguousFBDD (n + m)) (vertex : B.Vertex) :
    (B.forgetRightQueries (n := n) (m := m)).rank vertex =
      B.rank vertex := rfl

/-- Functional dependence of the right block on the left block, restricted to
accepting inputs. -/
def RightFunctional {n m : Nat}
    (B : FiniteUnambiguousFBDD (n + m)) : Prop :=
  forall (x : Fin n -> Bool) (z1 z2 : Fin m -> Bool),
    B.Accepts (Fin.addCases x z1) ->
    B.Accepts (Fin.addCases x z2) ->
    z1 = z2

/-- Partial inverse of the left embedding into a concatenated input. -/
def leftIndex? {n m : Nat} : Fin (n + m) -> Option (Fin n) :=
  Fin.addCases some (fun _rightIndex => none)

/-- The fibers of `leftIndex?` are singletons. -/
theorem leftIndex?_fiber_injective {n m : Nat} :
    forall (queryIndex queryIndex' : Fin (n + m))
      (leftIndex : Fin n),
      leftIndex ∈ leftIndex? (m := m) queryIndex ->
      leftIndex ∈ leftIndex? (m := m) queryIndex' ->
      queryIndex = queryIndex' := by
  intro queryIndex
  induction queryIndex using Fin.addCases with
  | left leftIndex1 =>
      intro queryIndex'
      induction queryIndex' using Fin.addCases with
      | left leftIndex2 =>
          intro leftIndex hmem1 hmem2
          simp [leftIndex?] at hmem1 hmem2
          subst leftIndex1
          subst leftIndex2
          rfl
      | right rightIndex2 =>
          intro leftIndex hmem1 hmem2
          simp [leftIndex?] at hmem2
  | right rightIndex1 =>
      intro queryIndex' leftIndex hmem1 hmem2
      simp [leftIndex?] at hmem1

namespace FunctionalProjectionWalk

/-- Compatibility depends only on the values of variables queried by the
walk. -/
theorem compatible_congr_of_eq_on_queryTrace
    {k : Nat} {B : FiniteUnambiguousFBDD k}
    {source target : B.Vertex} (walk : B.Walk source target)
    {input1 input2 : Fin k -> Bool}
    (heq : forall queryIndex, queryIndex ∈ walk.queryTrace ->
      input1 queryIndex = input2 queryIndex)
    (hcompatible : walk.Compatible input1) :
    walk.Compatible input2 := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      forall {input1 input2 : Fin k -> Bool},
        (forall queryIndex, queryIndex ∈ currentWalk.queryTrace ->
          input1 queryIndex = input2 queryIndex) ->
        currentWalk.Compatible input1 ->
        currentWalk.Compatible input2)
    walk ?_ ?_) heq hcompatible
  · intro vertex input1 input2 heq hcompatible
    trivial
  · intro source middle target edge tail ih input1 input2 heq hcompatible
    rcases hcompatible with ⟨hhead, htail⟩
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        have hquery : input1 queryIndex = input2 queryIndex := by
          apply heq queryIndex
          simp [FiniteUnambiguousFBDD.Walk.queryTrace,
            FiniteUnambiguousFBDD.Walk.queryEvents,
            FiniteUFBDDNode.queryEvent?, hnode]
        have htailEq : forall otherIndex,
            otherIndex ∈ tail.queryTrace ->
              input1 otherIndex = input2 otherIndex := by
          intro otherIndex hmem
          apply heq otherIndex
          rw [show
            (@FiniteUnambiguousFBDD.Walk.cons k B source middle target
              edge tail).queryTrace = queryIndex :: tail.queryTrace by
                simp [FiniteUnambiguousFBDD.Walk.queryTrace,
                  FiniteUnambiguousFBDD.Walk.queryEvents,
                  FiniteUFBDDNode.queryEvent?, hnode]]
          exact List.mem_cons_of_mem queryIndex hmem
        constructor
        · simpa [FiniteUnambiguousFBDD.CompatibleEdge, hnode, hquery]
            using hhead
        · exact ih htailEq htail
    | choice children =>
        have htailEq : forall queryIndex,
            queryIndex ∈ tail.queryTrace ->
              input1 queryIndex = input2 queryIndex := by
          intro queryIndex hmem
          apply heq queryIndex
          simpa [FiniteUnambiguousFBDD.Walk.queryTrace,
            FiniteUnambiguousFBDD.Walk.queryEvents,
            FiniteUFBDDNode.queryEvent?, hnode] using hmem
        exact ⟨by
          simpa [FiniteUnambiguousFBDD.CompatibleEdge, hnode] using hhead,
          ih htailEq htail⟩
    | sink =>
        simp [FiniteUnambiguousFBDD.Edge,
          FiniteUFBDDNode.HasChild, hnode] at edge

/-- Every syntactic walk with no repeated query admits a compatible total
input. -/
theorem exists_compatible_of_queryTrace_nodup
    {k : Nat} {B : FiniteUnambiguousFBDD k}
    {source target : B.Vertex} (walk : B.Walk source target)
    (hnodup : walk.queryTrace.Nodup) :
    ∃ input : Fin k -> Bool, walk.Compatible input := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      currentWalk.queryTrace.Nodup ->
        ∃ input : Fin k -> Bool, currentWalk.Compatible input)
    walk ?_ ?_) hnodup
  · intro vertex hnodup
    exact ⟨fun _ => false, by trivial⟩
  · intro source middle target edge tail ih hnodup
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        have hdecomp :
            queryIndex ∉ tail.queryTrace ∧ tail.queryTrace.Nodup := by
          simpa [FiniteUnambiguousFBDD.Walk.queryTrace,
            FiniteUnambiguousFBDD.Walk.queryEvents,
            FiniteUFBDDNode.queryEvent?, hnode] using hnodup
        rcases ih hdecomp.2 with ⟨input, htail⟩
        have hedge : middle = ifFalse ∨ middle = ifTrue := by
          simpa [FiniteUnambiguousFBDD.Edge,
            FiniteUFBDDNode.HasChild, hnode] using edge
        rcases hedge with hfalse | htrue
        · let updated : Fin k -> Bool :=
            Function.update input queryIndex false
          refine ⟨updated, ?_⟩
          constructor
          · simp [FiniteUnambiguousFBDD.CompatibleEdge, hnode,
              updated, hfalse]
          · apply compatible_congr_of_eq_on_queryTrace tail _ htail
            intro otherIndex hmem
            have hne : otherIndex ≠ queryIndex := by
              intro heq
              apply hdecomp.1
              simpa [heq] using hmem
            simp [updated, hne]
        · let updated : Fin k -> Bool :=
            Function.update input queryIndex true
          refine ⟨updated, ?_⟩
          constructor
          · simp [FiniteUnambiguousFBDD.CompatibleEdge, hnode,
              updated, htrue]
          · apply compatible_congr_of_eq_on_queryTrace tail _ htail
            intro otherIndex hmem
            have hne : otherIndex ≠ queryIndex := by
              intro heq
              apply hdecomp.1
              simpa [heq] using hmem
            simp [updated, hne]
    | choice children =>
        have htailNodup : tail.queryTrace.Nodup := by
          simpa [FiniteUnambiguousFBDD.Walk.queryTrace,
            FiniteUnambiguousFBDD.Walk.queryEvents,
            FiniteUFBDDNode.queryEvent?, hnode] using hnodup
        rcases ih htailNodup with ⟨input, htail⟩
        refine ⟨input, ?_⟩
        exact ⟨by
          simpa [FiniteUnambiguousFBDD.CompatibleEdge, hnode,
            FiniteUnambiguousFBDD.Edge,
            FiniteUFBDDNode.HasChild] using edge,
          htail⟩
    | sink =>
        simp [FiniteUnambiguousFBDD.Edge,
          FiniteUFBDDNode.HasChild, hnode] at edge

/-- Regard a projected walk as an original walk.  The vertex sequence is
unchanged because projection preserves every graph edge. -/
def toOriginal {n m : Nat} {B : FiniteUnambiguousFBDD (n + m)}
    {source target : B.Vertex} :
    (B.forgetRightQueries (n := n) (m := m)).Walk source target ->
      B.Walk source target
  | .nil vertex =>
      @FiniteUnambiguousFBDD.Walk.nil (n + m) B vertex
  | .cons edge tail =>
      @FiniteUnambiguousFBDD.Walk.cons (n + m) B _ _ _
        ((FiniteUFBDDNode.forgetRightQueries_hasChild_iff
          (n := n) (m := m) (B.node _) _).mp edge)
        (toOriginal (B := B) tail)

/-- Regard an original walk as a projected walk. -/
def toProjected {n m : Nat} {B : FiniteUnambiguousFBDD (n + m)}
    {source target : B.Vertex} :
    B.Walk source target ->
      (B.forgetRightQueries (n := n) (m := m)).Walk source target
  | .nil vertex =>
      @FiniteUnambiguousFBDD.Walk.nil n
        (B.forgetRightQueries (n := n) (m := m)) vertex
  | .cons edge tail =>
      @FiniteUnambiguousFBDD.Walk.cons n
        (B.forgetRightQueries (n := n) (m := m)) _ _ _
          ((FiniteUFBDDNode.forgetRightQueries_hasChild_iff
            (n := n) (m := m) (B.node _) _).mpr edge)
          (toProjected (B := B) tail)

/-- Projecting after forgetting a projected walk returns that walk. -/
theorem toProjected_toOriginal {n m : Nat}
    {B : FiniteUnambiguousFBDD (n + m)}
    {source target : B.Vertex}
    (walk : (B.forgetRightQueries (n := n) (m := m)).Walk source target) :
    toProjected (B := B) (toOriginal (B := B) walk) = walk := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      toProjected (B := B) (toOriginal (B := B) currentWalk) = currentWalk)
    walk ?_ ?_
  · intro vertex
    rfl
  · intro source middle target edge tail ih
    simp only [toOriginal, toProjected]
    rw [ih]

/-- Forgetting a projected walk is injective. -/
theorem toOriginal_injective {n m : Nat}
    {B : FiniteUnambiguousFBDD (n + m)}
    {source target : B.Vertex} :
    Function.Injective
      (toOriginal (B := B) :
        (B.forgetRightQueries (n := n) (m := m)).Walk source target ->
          B.Walk source target) := by
  intro left right heq
  have := congrArg (toProjected (B := B)) heq
  simpa [toProjected_toOriginal] using this

/-- A projected query trace is the original trace with all right-block
queries filtered out. -/
theorem queryTrace_eq_filterMap_leftIndex?
    {n m : Nat} {B : FiniteUnambiguousFBDD (n + m)}
    {source target : B.Vertex}
    (walk : (B.forgetRightQueries (n := n) (m := m)).Walk source target) :
    walk.queryTrace =
      (toOriginal (B := B) walk).queryTrace.filterMap
        (leftIndex? (n := n) (m := m)) := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      currentWalk.queryTrace =
        (toOriginal (B := B) currentWalk).queryTrace.filterMap
          (leftIndex? (n := n) (m := m)))
    walk ?_ ?_
  · intro vertex
    rfl
  · intro source middle target edge tail ih
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        induction queryIndex using Fin.addCases with
        | left leftIndex =>
            have hprojectedTrace :
                (@FiniteUnambiguousFBDD.Walk.cons n
                  (B.forgetRightQueries (n := n) (m := m))
                  source middle target edge tail).queryTrace =
                  leftIndex :: tail.queryTrace := by
              simp [FiniteUnambiguousFBDD.Walk.queryTrace,
                FiniteUnambiguousFBDD.Walk.queryEvents,
                FiniteUFBDDNode.queryEvent?,
                FiniteUnambiguousFBDD.forgetRightQueries,
                FiniteUFBDDNode.forgetRightQueries, hnode]
            have horiginalTrace :
                (toOriginal (B := B)
                  (@FiniteUnambiguousFBDD.Walk.cons n
                    (B.forgetRightQueries (n := n) (m := m))
                    source middle target edge tail)).queryTrace =
                  Fin.castAdd m leftIndex ::
                    (toOriginal (B := B) tail).queryTrace := by
              simp [FiniteUnambiguousFBDD.Walk.queryTrace,
                FiniteUnambiguousFBDD.Walk.queryEvents,
                FiniteUFBDDNode.queryEvent?, toOriginal, hnode]
            rw [hprojectedTrace, horiginalTrace]
            simp [leftIndex?, ih]
        | right rightIndex =>
            have hprojectedTrace :
                (@FiniteUnambiguousFBDD.Walk.cons n
                  (B.forgetRightQueries (n := n) (m := m))
                  source middle target edge tail).queryTrace =
                  tail.queryTrace := by
              simp [FiniteUnambiguousFBDD.Walk.queryTrace,
                FiniteUnambiguousFBDD.Walk.queryEvents,
                FiniteUFBDDNode.queryEvent?,
                FiniteUnambiguousFBDD.forgetRightQueries,
                FiniteUFBDDNode.forgetRightQueries, hnode]
            have horiginalTrace :
                (toOriginal (B := B)
                  (@FiniteUnambiguousFBDD.Walk.cons n
                    (B.forgetRightQueries (n := n) (m := m))
                    source middle target edge tail)).queryTrace =
                  Fin.natAdd n rightIndex ::
                    (toOriginal (B := B) tail).queryTrace := by
              simp [FiniteUnambiguousFBDD.Walk.queryTrace,
                FiniteUnambiguousFBDD.Walk.queryEvents,
                FiniteUFBDDNode.queryEvent?, toOriginal, hnode]
            rw [hprojectedTrace, horiginalTrace]
            simp [leftIndex?, ih]
    | choice children =>
        have hprojectedTrace :
            (@FiniteUnambiguousFBDD.Walk.cons n
              (B.forgetRightQueries (n := n) (m := m))
              source middle target edge tail).queryTrace =
              tail.queryTrace := by
          simp [FiniteUnambiguousFBDD.Walk.queryTrace,
            FiniteUnambiguousFBDD.Walk.queryEvents,
            FiniteUFBDDNode.queryEvent?,
            FiniteUnambiguousFBDD.forgetRightQueries,
            FiniteUFBDDNode.forgetRightQueries, hnode]
        have horiginalTrace :
            (toOriginal (B := B)
              (@FiniteUnambiguousFBDD.Walk.cons n
                (B.forgetRightQueries (n := n) (m := m))
                source middle target edge tail)).queryTrace =
              (toOriginal (B := B) tail).queryTrace := by
          simp [FiniteUnambiguousFBDD.Walk.queryTrace,
            FiniteUnambiguousFBDD.Walk.queryEvents,
            FiniteUFBDDNode.queryEvent?, toOriginal, hnode]
        rw [hprojectedTrace, horiginalTrace]
        exact ih
    | sink =>
        simp [FiniteUnambiguousFBDD.Edge,
          FiniteUnambiguousFBDD.forgetRightQueries,
          FiniteUFBDDNode.forgetRightQueries,
          FiniteUFBDDNode.HasChild, hnode] at edge

/-- If the original vertex sequence has no repeated query, neither does its
projected trace. -/
theorem queryTrace_nodup_of_toOriginal_queryTrace_nodup
    {n m : Nat} {B : FiniteUnambiguousFBDD (n + m)}
    {source target : B.Vertex}
    (walk : (B.forgetRightQueries (n := n) (m := m)).Walk source target)
    (hnodup : (toOriginal (B := B) walk).queryTrace.Nodup) :
    walk.queryTrace.Nodup := by
  rw [queryTrace_eq_filterMap_leftIndex? (B := B) walk]
  exact hnodup.filterMap leftIndex?_fiber_injective

/-- An original walk compatible with `(x, z)` remains compatible after the
right queries are forgotten. -/
theorem toProjected_compatible
    {n m : Nat} {B : FiniteUnambiguousFBDD (n + m)}
    (x : Fin n -> Bool) (z : Fin m -> Bool)
    {source target : B.Vertex} (walk : B.Walk source target)
    (hcompatible : walk.Compatible (Fin.addCases x z)) :
    (toProjected (B := B) walk).Compatible x := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      currentWalk.Compatible (Fin.addCases x z) ->
        (toProjected (B := B) currentWalk).Compatible x)
    walk ?_ ?_) hcompatible
  · intro vertex hcompatible
    trivial
  · intro source middle target edge tail ih hcompatible
    rcases hcompatible with ⟨hhead, htail⟩
    have htailProjected := ih htail
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        induction queryIndex using Fin.addCases with
        | left leftIndex =>
            constructor
            · simpa [FiniteUnambiguousFBDD.CompatibleEdge,
                FiniteUnambiguousFBDD.forgetRightQueries,
                FiniteUFBDDNode.forgetRightQueries, hnode]
                using hhead
            · exact htailProjected
        | right rightIndex =>
            constructor
            · cases hvalue : z rightIndex <;>
                simp [FiniteUnambiguousFBDD.CompatibleEdge,
                  FiniteUnambiguousFBDD.forgetRightQueries,
                  FiniteUFBDDNode.forgetRightQueries, hnode, hvalue]
                  at hhead ⊢
              · exact Or.inl hhead
              · exact Or.inr hhead
            · exact htailProjected
    | choice children =>
        exact ⟨by
          simpa [FiniteUnambiguousFBDD.CompatibleEdge,
            FiniteUnambiguousFBDD.forgetRightQueries,
            FiniteUFBDDNode.forgetRightQueries, hnode] using hhead,
          htailProjected⟩
    | sink =>
        simp [FiniteUnambiguousFBDD.Edge,
          FiniteUFBDDNode.HasChild, hnode] at edge

/-- Combine the visible input of a projected compatible walk with the right
slice of any original input compatible with the same vertex sequence. -/
theorem toOriginal_compatible_join_rightSlice
    {n m : Nat} {B : FiniteUnambiguousFBDD (n + m)}
    (x : Fin n -> Bool) (originalInput : Fin (n + m) -> Bool)
    {source target : B.Vertex}
    (walk : (B.forgetRightQueries (n := n) (m := m)).Walk source target)
    (hprojected : walk.Compatible x)
    (horiginal : (toOriginal (B := B) walk).Compatible originalInput) :
    (toOriginal (B := B) walk).Compatible
      (Fin.addCases x (fun rightIndex =>
        originalInput (Fin.natAdd n rightIndex))) := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      currentWalk.Compatible x ->
      (toOriginal (B := B) currentWalk).Compatible originalInput ->
      (toOriginal (B := B) currentWalk).Compatible
        (Fin.addCases x (fun rightIndex =>
          originalInput (Fin.natAdd n rightIndex))))
    walk ?_ ?_) hprojected horiginal
  · intro vertex hprojected horiginal
    trivial
  · intro source middle target edge tail ih hprojected horiginal
    rcases hprojected with ⟨hprojectedHead, hprojectedTail⟩
    rcases horiginal with ⟨horiginalHead, horiginalTail⟩
    have htail := ih hprojectedTail horiginalTail
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        induction queryIndex using Fin.addCases with
        | left leftIndex =>
            constructor
            · simpa [FiniteUnambiguousFBDD.CompatibleEdge,
                FiniteUnambiguousFBDD.forgetRightQueries,
                FiniteUFBDDNode.forgetRightQueries, hnode]
                using hprojectedHead
            · exact htail
        | right rightIndex =>
            constructor
            · simpa [FiniteUnambiguousFBDD.CompatibleEdge, hnode]
                using horiginalHead
            · exact htail
    | choice children =>
        exact ⟨by
          simpa [FiniteUnambiguousFBDD.CompatibleEdge, hnode]
            using horiginalHead,
          htail⟩
    | sink =>
        simp [FiniteUnambiguousFBDD.Edge,
          FiniteUnambiguousFBDD.forgetRightQueries,
          FiniteUFBDDNode.forgetRightQueries,
          FiniteUFBDDNode.HasChild, hnode] at edge

/-- A projected compatible walk whose original query trace is read-once can be
lifted by one assignment to all forgotten coordinates. -/
theorem exists_rightInput_compatible_toOriginal
    {n m : Nat} {B : FiniteUnambiguousFBDD (n + m)}
    (x : Fin n -> Bool) {source target : B.Vertex}
    (walk : (B.forgetRightQueries (n := n) (m := m)).Walk source target)
    (hprojected : walk.Compatible x)
    (hnodup : (toOriginal (B := B) walk).queryTrace.Nodup) :
    ∃ z : Fin m -> Bool,
      (toOriginal (B := B) walk).Compatible (Fin.addCases x z) := by
  rcases exists_compatible_of_queryTrace_nodup
      (toOriginal (B := B) walk) hnodup with
    ⟨originalInput, horiginal⟩
  refine ⟨fun rightIndex => originalInput (Fin.natAdd n rightIndex), ?_⟩
  exact toOriginal_compatible_join_rightSlice
    x originalInput walk hprojected horiginal

end FunctionalProjectionWalk

/-- Projection preserves the vertex count exactly. -/
theorem forgetRightQueries_vertex_card {n m : Nat}
    (B : FiniteUnambiguousFBDD (n + m)) :
    @Fintype.card (B.forgetRightQueries (n := n) (m := m)).Vertex
        (B.forgetRightQueries (n := n) (m := m)).vertexFintype =
      @Fintype.card B.Vertex B.vertexFintype := rfl

/-- Exact existential semantics of forgetting the right input block. -/
theorem forgetRightQueries_accepts_iff
    {n m : Nat} (B : FiniteUnambiguousFBDD (n + m))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (x : Fin n -> Bool) :
    (B.forgetRightQueries (n := n) (m := m)).Accepts x <->
      ∃ z : Fin m -> Bool, B.Accepts (Fin.addCases x z) := by
  constructor
  · rintro ⟨path⟩
    have hnodup :
        (FunctionalProjectionWalk.toOriginal (B := B) path.walk).queryTrace.Nodup :=
      hreadOnce B.accept (FunctionalProjectionWalk.toOriginal (B := B) path.walk)
    rcases FunctionalProjectionWalk.exists_rightInput_compatible_toOriginal
        (B := B) x path.walk path.compatible hnodup with
      ⟨z, hcompatible⟩
    exact ⟨z, ⟨⟨FunctionalProjectionWalk.toOriginal (B := B) path.walk,
      hcompatible⟩⟩⟩
  · rintro ⟨z, ⟨path⟩⟩
    exact ⟨⟨FunctionalProjectionWalk.toProjected (B := B) path.walk,
      FunctionalProjectionWalk.toProjected_compatible x z path.walk path.compatible⟩⟩

/-- Functional projection preserves syntactic read-once. -/
theorem forgetRightQueries_isSyntacticallyReadOnce
    {n m : Nat} (B : FiniteUnambiguousFBDD (n + m))
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    (B.forgetRightQueries (n := n) (m := m)).IsSyntacticallyReadOnce := by
  intro target walk
  apply FunctionalProjectionWalk.queryTrace_nodup_of_toOriginal_queryTrace_nodup
    (B := B) walk
  exact hreadOnce target (FunctionalProjectionWalk.toOriginal (B := B) walk)

/-- Under functionality of the forgotten witness, unambiguity descends to the
existential projection. -/
theorem forgetRightQueries_isUnambiguous_of_rightFunctional
    {n m : Nat} (B : FiniteUnambiguousFBDD (n + m))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hfunctional : B.RightFunctional) :
    (B.forgetRightQueries (n := n) (m := m)).IsUnambiguous := by
  intro x left right hleft hright
  have hleftNodup :
      (FunctionalProjectionWalk.toOriginal (B := B) left).queryTrace.Nodup :=
    hreadOnce B.accept (FunctionalProjectionWalk.toOriginal (B := B) left)
  have hrightNodup :
      (FunctionalProjectionWalk.toOriginal (B := B) right).queryTrace.Nodup :=
    hreadOnce B.accept (FunctionalProjectionWalk.toOriginal (B := B) right)
  rcases FunctionalProjectionWalk.exists_rightInput_compatible_toOriginal
      (B := B) x left hleft hleftNodup with
    ⟨z1, hleftOriginal⟩
  rcases FunctionalProjectionWalk.exists_rightInput_compatible_toOriginal
      (B := B) x right hright hrightNodup with
    ⟨z2, hrightOriginal⟩
  have hz : z1 = z2 := hfunctional x z1 z2
    ⟨⟨FunctionalProjectionWalk.toOriginal (B := B) left, hleftOriginal⟩⟩
    ⟨⟨FunctionalProjectionWalk.toOriginal (B := B) right, hrightOriginal⟩⟩
  subst z2
  apply FunctionalProjectionWalk.toOriginal_injective (B := B)
  exact hunambiguous (Fin.addCases x z1)
    (FunctionalProjectionWalk.toOriginal (B := B) left)
    (FunctionalProjectionWalk.toOriginal (B := B) right)
    hleftOriginal hrightOriginal

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
