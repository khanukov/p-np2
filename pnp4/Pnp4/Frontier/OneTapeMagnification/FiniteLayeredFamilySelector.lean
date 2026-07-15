import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDD
import Pnp4.Frontier.OneTapeMagnification.FiniteRejectingGuardedCanonicalFamily
import Pnp4.Frontier.OneTapeMagnification.MandatoryFixedOrderQueryCollapse

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A finite silent selector for a dependent layered-program family

This file turns a `FiniteLayeredQueryProgramFamily` into one finite ranked
branching DAG.  The root is a silent nondeterministic choice of a component.
Every other nonsink vertex is tagged by the chosen component, a boundary
layer, and that component's live state.  Optional query-free program layers
become singleton silent choices.

The construction below gives an exact realization of existential family
acceptance: every accepting selector path decodes to an accepting component.
No syntactic read-once claim is made: the source family API only assumes
read-once on consistent Boolean executions, whereas
`FiniteUnambiguousFBDD` quantifies over all formal graph paths.
-/

namespace FiniteLayeredQueryProgramFamily

/-- A component-local boundary slot. -/
abbrev ComponentSlot {n : Nat} (family : FiniteLayeredQueryProgramFamily n) :=
  Sigma fun index : family.Index =>
    Fin (family.layers index + 1) × (family.program index).State

/-- One silent root, every tagged component slot, and two Boolean sinks.
`false` is the rejecting sink and `true` is the accepting sink. -/
abbrev SelectorVertex {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :=
  Sum Unit (Sum family.ComponentSlot Bool)

def selectorRoot {n : Nat} {family : FiniteLayeredQueryProgramFamily n} :
    family.SelectorVertex :=
  Sum.inl ()

def selectorComponent {n : Nat}
    {family : FiniteLayeredQueryProgramFamily n}
    (index : family.Index) (boundary : Fin (family.layers index + 1))
    (state : (family.program index).State) : family.SelectorVertex :=
  Sum.inr (Sum.inl ⟨index, boundary, state⟩)

def selectorSink {n : Nat} {family : FiniteLayeredQueryProgramFamily n}
    (accepting : Bool) : family.SelectorVertex :=
  Sum.inr (Sum.inr accepting)

noncomputable def selectorVertexFintype {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    Fintype family.SelectorVertex := by
  classical
  letI : Fintype family.Index := family.indexFintype
  letI (index : family.Index) : Fintype (family.program index).State :=
    (family.program index).stateFintype
  infer_instance

/-- Component start vertices enumerated at the silent root. -/
noncomputable def selectorStartChildren {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    List family.SelectorVertex := by
  classical
  letI : Fintype family.Index := family.indexFintype
  exact Finset.univ.toList.map fun index =>
    selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
      (family.program index).start

/-- Advance one component boundary after executing a physical layer. -/
def selectorNextBoundary {n : Nat}
    {family : FiniteLayeredQueryProgramFamily n}
    {index : family.Index}
    (boundary : Fin (family.layers index + 1))
    (hphysical : boundary.val < family.layers index) :
    Fin (family.layers index + 1) :=
  ⟨boundary.val + 1, by omega⟩

/-- Graph node attached to every selector vertex. -/
noncomputable def selectorNode {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    family.SelectorVertex → FiniteUFBDDNode n family.SelectorVertex
  | Sum.inl _ => .choice family.selectorStartChildren
  | Sum.inr (Sum.inr _) => .sink
  | Sum.inr (Sum.inl ⟨index, boundary, state⟩) =>
      if hphysical : boundary.val < family.layers index then
        let layer : Fin (family.layers index) :=
          ⟨boundary.val, hphysical⟩
        let nextBoundary := selectorNextBoundary boundary hphysical
        match family.program index |>.query? layer state with
        | none =>
            .choice [selectorComponent index nextBoundary
              ((family.program index).next layer state none)]
        | some queryIndex =>
            .query queryIndex
              (selectorComponent index nextBoundary
                ((family.program index).next layer state (some false)))
              (selectorComponent index nextBoundary
                ((family.program index).next layer state (some true)))
      else
        .choice [selectorSink ((family.program index).output state)]

/-- Largest component boundary rank. -/
noncomputable def selectorMaxComponentRank {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Nat := by
  letI : Fintype family.Index := family.indexFintype
  let indices : Finset family.Index := Finset.univ
  exact Finset.sup (α := Nat) indices fun index => family.layers index + 1

/-- Sinks have rank zero, a component slot has its number of remaining
boundaries, and the silent root lies one rank above every component start. -/
noncomputable def selectorRank {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    family.SelectorVertex → Nat
  | Sum.inl _ => family.selectorMaxComponentRank + 1
  | Sum.inr (Sum.inr _) => 0
  | Sum.inr (Sum.inl ⟨index, boundary, _state⟩) =>
      family.layers index + 1 - boundary.val

theorem selectorNode_rank_child {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    {source target : family.SelectorVertex}
    (hchild : (family.selectorNode source).HasChild target) :
    family.selectorRank target < family.selectorRank source := by
  classical
  letI : Fintype family.Index := family.indexFintype
  cases source with
  | inl root =>
      simp only [selectorNode, FiniteUFBDDNode.HasChild] at hchild
      simp only [selectorStartChildren, List.mem_map] at hchild
      obtain ⟨index, _hindex, rfl⟩ := hchild
      change family.layers index + 1 < family.selectorMaxComponentRank + 1
      have hle : family.layers index + 1 ≤
          family.selectorMaxComponentRank := by
        change family.layers index + 1 ≤
          Finset.sup (α := Nat) Finset.univ
            (fun item : family.Index => family.layers item + 1)
        exact Finset.le_sup (α := Nat) (f := fun item : family.Index =>
          family.layers item + 1) (Finset.mem_univ index)
      omega
  | inr rest =>
      cases rest with
      | inr sink =>
          simp [selectorNode, FiniteUFBDDNode.HasChild] at hchild
      | inl slot =>
          rcases slot with ⟨index, boundary, state⟩
          by_cases hphysical : boundary.val < family.layers index
          · let layer : Fin (family.layers index) :=
              ⟨boundary.val, hphysical⟩
            let nextBoundary := selectorNextBoundary boundary hphysical
            cases hquery : (family.program index).query? layer state with
            | none =>
                have htarget : target = selectorComponent index nextBoundary
                    ((family.program index).next layer state none) := by
                  simpa [selectorNode, hphysical, layer, nextBoundary,
                    hquery, FiniteUFBDDNode.HasChild] using hchild
                subst target
                change family.layers index + 1 - (boundary.val + 1) <
                  family.layers index + 1 - boundary.val
                omega
            | some queryIndex =>
                have htarget :
                    target = selectorComponent index nextBoundary
                        ((family.program index).next layer state
                          (some false)) ∨
                      target = selectorComponent index nextBoundary
                        ((family.program index).next layer state
                          (some true)) := by
                  simpa [selectorNode, hphysical, layer, nextBoundary,
                    hquery, FiniteUFBDDNode.HasChild] using hchild
                rcases htarget with htarget | htarget <;> subst target <;>
                  change family.layers index + 1 - (boundary.val + 1) <
                    family.layers index + 1 - boundary.val <;> omega
          · have htarget : target =
                selectorSink ((family.program index).output state) := by
              simpa [selectorNode, hphysical,
                FiniteUFBDDNode.HasChild] using hchild
            subst target
            change 0 < family.layers index + 1 - boundary.val
            have hboundary : boundary.val ≤ family.layers index := by
              omega
            omega

/-- The single finite ranked branching graph selected from the family. -/
noncomputable def selectorFBDD {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    FiniteUnambiguousFBDD n where
  Vertex := family.SelectorVertex
  vertexFintype := family.selectorVertexFintype
  vertexDecidableEq := Classical.decEq _
  start := selectorRoot
  accept := selectorSink true
  node := family.selectorNode
  accept_sink := rfl
  rank := family.selectorRank
  rank_child := family.selectorNode_rank_child

/-- Exact vertex count: three global vertices plus the honest disjoint sum of
all component boundary-state slots. -/
theorem selectorFBDD_vertex_card {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) :
    @Fintype.card (family.selectorFBDD).Vertex
        (family.selectorFBDD).vertexFintype =
      family.layeredStateSlotCount + 3 := by
  classical
  letI : Fintype family.Index := family.indexFintype
  letI (index : family.Index) : Fintype (family.program index).State :=
    (family.program index).stateFintype
  simp [selectorFBDD, selectorVertexFintype, SelectorVertex, ComponentSlot,
    layeredStateSlotCount, LayeredQueryProgram.width,
    Fintype.card_sigma, Nat.add_comm]
  omega

/-! ## Forward existential acceptance realization -/

/-- A component execution packaged together with input compatibility. -/
structure SelectorComponentExecution {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index) (fuel physical : Nat)
    (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State) where
  result : Bool
  walk : (family.selectorFBDD).Walk
    (selectorComponent index ⟨physical, by omega⟩ state)
    (selectorSink result)
  compatible : walk.Compatible input
  result_eq : result = (family.program index).output
    (LayeredQueryProgram.executePhysicalStateFrom
      (family.program index) input fuel physical (by omega) state)

/-- The canonical input-compatible execution inside one selected component,
ending at the sink named by the component's suffix output. -/
noncomputable def selectorComponentExecution {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index) :
    (fuel physical : Nat) →
      (hphysical : physical + fuel = family.layers index) →
      (state : (family.program index).State) →
      SelectorComponentExecution family input index fuel physical
        hphysical state
  | 0, physical, hphysical, state => by
      have hnot : ¬physical < family.layers index := by omega
      have hedge : (family.selectorFBDD).Edge
          (selectorComponent index ⟨physical, by omega⟩ state)
          (selectorSink ((family.program index).output state)) := by
        change (family.selectorNode
          (selectorComponent index ⟨physical, by omega⟩ state)).HasChild
            (selectorSink ((family.program index).output state))
        simp [selectorNode, selectorComponent, selectorSink, hnot,
          FiniteUFBDDNode.HasChild]
      have hcompatible : (family.selectorFBDD).CompatibleEdge input
          (selectorComponent index ⟨physical, by omega⟩ state)
          (selectorSink ((family.program index).output state)) := by
        simp [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
          selectorNode, selectorComponent, selectorSink, hnot]
      exact
        { result := (family.program index).output state
          walk := .cons hedge (.nil _)
          compatible := ⟨hcompatible, trivial⟩
          result_eq := rfl }
  | fuel + 1, physical, hphysical, state => by
      have hlt : physical < family.layers index := by omega
      let layer : Fin (family.layers index) := ⟨physical, hlt⟩
      cases hquery : (family.program index).query? layer state with
      | none =>
          let nextState := (family.program index).next layer state none
          let tail := selectorComponentExecution family input index fuel
            (physical + 1) (by omega) nextState
          have hedge : (family.selectorFBDD).Edge
              (selectorComponent index ⟨physical, by omega⟩ state)
              (selectorComponent index ⟨physical + 1, by omega⟩ nextState) := by
            change (family.selectorNode
              (selectorComponent index ⟨physical, by omega⟩ state)).HasChild
                (selectorComponent index ⟨physical + 1, by omega⟩ nextState)
            simp [selectorNode, selectorComponent, hlt, layer,
              hquery, nextState, selectorNextBoundary,
              FiniteUFBDDNode.HasChild]
          have hcompatible : (family.selectorFBDD).CompatibleEdge input
              (selectorComponent index ⟨physical, by omega⟩ state)
              (selectorComponent index ⟨physical + 1, by omega⟩ nextState) := by
            simp [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
              selectorNode, selectorComponent, selectorSink, hlt, layer,
              hquery, nextState, selectorNextBoundary]
          exact
            { result := tail.result
              walk := .cons hedge tail.walk
              compatible := ⟨hcompatible, tail.compatible⟩
              result_eq := by
                simpa [LayeredQueryProgram.executePhysicalStateFrom, layer,
                  hquery, nextState, tail] using tail.result_eq }
      | some queryIndex =>
          cases hbit : input queryIndex with
          | false =>
              let nextState := (family.program index).next layer state
                (some false)
              let tail := selectorComponentExecution family input index fuel
                (physical + 1) (by omega) nextState
              have hedge : (family.selectorFBDD).Edge
                  (selectorComponent index ⟨physical, by omega⟩ state)
                  (selectorComponent index ⟨physical + 1, by omega⟩
                    nextState) := by
                change (family.selectorNode
                  (selectorComponent index ⟨physical, by omega⟩ state)).HasChild
                    (selectorComponent index ⟨physical + 1, by omega⟩
                      nextState)
                simp [selectorNode, selectorComponent, hlt,
                  layer, hquery, nextState, selectorNextBoundary,
                  FiniteUFBDDNode.HasChild]
              have hcompatible : (family.selectorFBDD).CompatibleEdge input
                  (selectorComponent index ⟨physical, by omega⟩ state)
                  (selectorComponent index ⟨physical + 1, by omega⟩
                    nextState) := by
                simp [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                  selectorNode, selectorComponent, selectorSink, hlt, layer,
                  hquery, hbit, nextState, selectorNextBoundary]
              exact
                { result := tail.result
                  walk := .cons hedge tail.walk
                  compatible := ⟨hcompatible, tail.compatible⟩
                  result_eq := by
                    simpa [LayeredQueryProgram.executePhysicalStateFrom,
                      layer, hquery, hbit, nextState, tail] using
                        tail.result_eq }
          | true =>
              let nextState := (family.program index).next layer state
                (some true)
              let tail := selectorComponentExecution family input index fuel
                (physical + 1) (by omega) nextState
              have hedge : (family.selectorFBDD).Edge
                  (selectorComponent index ⟨physical, by omega⟩ state)
                  (selectorComponent index ⟨physical + 1, by omega⟩
                    nextState) := by
                change (family.selectorNode
                  (selectorComponent index ⟨physical, by omega⟩ state)).HasChild
                    (selectorComponent index ⟨physical + 1, by omega⟩
                      nextState)
                simp [selectorNode, selectorComponent, hlt,
                  layer, hquery, nextState, selectorNextBoundary,
                  FiniteUFBDDNode.HasChild]
              have hcompatible : (family.selectorFBDD).CompatibleEdge input
                  (selectorComponent index ⟨physical, by omega⟩ state)
                  (selectorComponent index ⟨physical + 1, by omega⟩
                    nextState) := by
                simp [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                  selectorNode, selectorComponent, selectorSink, hlt, layer,
                  hquery, hbit, nextState, selectorNextBoundary]
              exact
                { result := tail.result
                  walk := .cons hedge tail.walk
                  compatible := ⟨hcompatible, tail.compatible⟩
                  result_eq := by
                    simpa [LayeredQueryProgram.executePhysicalStateFrom,
                      layer, hquery, hbit, nextState, tail] using
                        tail.result_eq }

noncomputable def selectorComponentExecutionWalk {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index) (fuel physical : Nat)
    (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State) :=
  (selectorComponentExecution family input index fuel physical hphysical
    state).walk

theorem selectorComponentExecutionWalk_compatible {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index) (fuel physical : Nat)
    (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State) :
    (selectorComponentExecutionWalk family input index fuel physical
      hphysical state).Compatible input :=
  (selectorComponentExecution family input index fuel physical hphysical
    state).compatible

theorem selectorComponentExecution_result_eq {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index) (fuel physical : Nat)
    (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State) :
    (selectorComponentExecution family input index fuel physical hphysical
      state).result =
      (family.program index).output
        (LayeredQueryProgram.executePhysicalStateFrom
          (family.program index) input fuel physical hphysical state) :=
  (selectorComponentExecution family input index fuel physical hphysical
    state).result_eq

theorem selectorStartChildren_mem {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (index : family.Index) :
    selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
        (family.program index).start ∈ family.selectorStartChildren := by
  classical
  letI : Fintype family.Index := family.indexFintype
  simp [selectorStartChildren]

theorem walk_compatible_cast_target {n : Nat}
    {B : FiniteUnambiguousFBDD n} (input : Fin n → Bool)
    {source target target' : B.Vertex} (h : target = target')
    (walk : B.Walk source target) :
    (h ▸ walk).Compatible input ↔ walk.Compatible input := by
  subst target'
  rfl

/-- An accepting component supplies an accepting path through the silent
selector root. -/
theorem selectorFBDD_accepts_of_component_eval_true {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index)
    (heval : (family.program index).eval input = true) :
    (family.selectorFBDD).Accepts input := by
  let execution := selectorComponentExecution family input index
    (family.layers index) 0 (by omega) (family.program index).start
  have hfinal := LayeredQueryProgram.executePhysicalStateFrom_executePrefix
    (family.program index) input (family.layers index) 0 (by omega)
  have hsuffix : (family.program index).output
      (LayeredQueryProgram.executePhysicalStateFrom
        (family.program index) input (family.layers index) 0 (by omega)
          (family.program index).start) = true := by
    unfold LayeredQueryProgram.eval LayeredQueryProgram.finalState at heval
    have hfinal' :
        LayeredQueryProgram.executePhysicalStateFrom
          (family.program index) input (family.layers index) 0 (by omega)
            (family.program index).start =
          ((family.program index).executePrefix input
            (family.layers index) le_rfl).1 := by
      simpa [LayeredQueryProgram.executePrefix] using hfinal
    rw [hfinal']
    exact heval
  have hresult : execution.result = true :=
    execution.result_eq.trans hsuffix
  have hrootEdge : (family.selectorFBDD).Edge selectorRoot
      (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
        (family.program index).start) := by
    change (family.selectorNode selectorRoot).HasChild
      (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
        (family.program index).start)
    simpa [selectorNode, selectorRoot, FiniteUFBDDNode.HasChild] using
      selectorStartChildren_mem family index
  have hrootCompatible : (family.selectorFBDD).CompatibleEdge input
      selectorRoot
      (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
        (family.program index).start) := by
    simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
      selectorNode, selectorRoot] using selectorStartChildren_mem family index
  cases hvalue : execution.result with
  | false =>
      simp [hvalue] at hresult
  | true =>
      have hend : selectorSink execution.result =
          (family.selectorFBDD).accept := by
        simp [selectorFBDD, hvalue, selectorSink]
      let componentWalk : (family.selectorFBDD).Walk
          (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
            (family.program index).start)
          (family.selectorFBDD).accept := hend ▸ execution.walk
      have componentCompatible : componentWalk.Compatible input := by
        exact (walk_compatible_cast_target input hend execution.walk).2
          execution.compatible
      exact Nonempty.intro
        { walk := .cons hrootEdge componentWalk
          compatible := ⟨hrootCompatible, componentCompatible⟩ }

theorem selectorFBDD_accepts_of_eval_eq_true {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (heval : family.eval input = true) :
    (family.selectorFBDD).Accepts input := by
  obtain ⟨index, hindex⟩ := (eval_eq_true_iff family input).1 heval
  exact selectorFBDD_accepts_of_component_eval_true
    family input index hindex

/-! ## Converse path decoding -/

/-- Endpoint-generalized sink decoder.  Keeping both endpoints as variables
avoids dependent elimination on definitionally distinct fixed vertices. -/
theorem selectorSink_walk_to_accept_eq_true_aux {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (value : Bool)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorSink value)
    (htarget : target = (family.selectorFBDD).accept)
    (walk : (family.selectorFBDD).Walk source target) :
    value = true := by
  cases walk with
  | nil vertex =>
      have heq : selectorSink value = (family.selectorFBDD).accept :=
        hsource.symm.trans htarget
      simpa [selectorFBDD, selectorSink] using heq
  | @cons _ middle _ edge tail =>
      rw [hsource] at edge
      simp [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
        selectorSink, FiniteUFBDDNode.HasChild] at edge

/-- A walk cannot leave a selector sink; hence a sink which reaches the
accepting sink is itself the accepting sink. -/
theorem selectorSink_walk_to_accept_eq_true {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (value : Bool)
    (walk : (family.selectorFBDD).Walk (selectorSink value)
      (family.selectorFBDD).accept) :
    value = true :=
  selectorSink_walk_to_accept_eq_true_aux family value rfl rfl walk

/-- Endpoint-generalized component decoder.  Its source and target equalities
make induction on the indexed walk robust while retaining the exact suffix
semantics. -/
theorem selectorComponentWalk_to_accept_implies_suffix_true_aux {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index)
    (fuel physical : Nat) (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorComponent index
      ⟨physical, by omega⟩ state)
    (htarget : target = (family.selectorFBDD).accept)
    (walk : (family.selectorFBDD).Walk source target)
    (hcompatible : walk.Compatible input) :
    (family.program index).output
      (LayeredQueryProgram.executePhysicalStateFrom
        (family.program index) input fuel physical hphysical state) = true := by
  induction fuel generalizing physical state source target with
  | zero =>
      have hnot : ¬physical < family.layers index := by omega
      cases walk with
      | nil vertex =>
          have heq : selectorComponent index ⟨physical, by omega⟩ state =
              (family.selectorFBDD).accept := hsource.symm.trans htarget
          simp [selectorComponent, selectorFBDD, selectorSink] at heq
      | @cons _ middle _ edge tail =>
          have hfirst : (family.selectorFBDD).CompatibleEdge input
              (selectorComponent index ⟨physical, by omega⟩ state) middle := by
            simpa [hsource] using hcompatible.1
          have hmiddle : middle =
              selectorSink ((family.program index).output state) := by
            simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
              selectorNode, selectorComponent, selectorSink, hnot] using
                hfirst
          have hsink := selectorSink_walk_to_accept_eq_true_aux family
            ((family.program index).output state) hmiddle htarget tail
          simpa [LayeredQueryProgram.executePhysicalStateFrom] using hsink
  | succ fuel ih =>
      have hlt : physical < family.layers index := by omega
      let layer : Fin (family.layers index) := ⟨physical, hlt⟩
      cases hquery : (family.program index).query? layer state with
      | none =>
          cases walk with
          | nil vertex =>
              have heq :
                  selectorComponent index ⟨physical, by omega⟩ state =
                    (family.selectorFBDD).accept := hsource.symm.trans htarget
              simp [selectorComponent, selectorFBDD, selectorSink] at heq
          | @cons _ middle _ edge tail =>
              have hfirst : (family.selectorFBDD).CompatibleEdge input
                  (selectorComponent index ⟨physical, by omega⟩ state)
                    middle := by
                simpa [hsource] using hcompatible.1
              have hmiddle : middle = selectorComponent index
                  ⟨physical + 1, by omega⟩
                  ((family.program index).next layer state none) := by
                simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                  selectorNode, selectorComponent, selectorSink, hlt, layer,
                  hquery, selectorNextBoundary] using hfirst
              have htail := ih (physical := physical + 1)
                (hphysical := by omega)
                (state := (family.program index).next layer state none)
                (source := middle) (target := target) hmiddle htarget tail
                hcompatible.2
              simpa [LayeredQueryProgram.executePhysicalStateFrom, layer,
                hquery] using htail
      | some queryIndex =>
          cases hbit : input queryIndex with
          | false =>
              cases walk with
              | nil vertex =>
                  have heq :
                      selectorComponent index ⟨physical, by omega⟩ state =
                        (family.selectorFBDD).accept :=
                    hsource.symm.trans htarget
                  simp [selectorComponent, selectorFBDD, selectorSink] at heq
              | @cons _ middle _ edge tail =>
                  have hfirst : (family.selectorFBDD).CompatibleEdge input
                      (selectorComponent index ⟨physical, by omega⟩ state)
                        middle := by
                    simpa [hsource] using hcompatible.1
                  have hmiddle : middle = selectorComponent index
                      ⟨physical + 1, by omega⟩
                      ((family.program index).next layer state
                        (some false)) := by
                    simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                      selectorNode, selectorComponent, selectorSink, hlt,
                      layer, hquery, hbit, selectorNextBoundary] using hfirst
                  have htail := ih (physical := physical + 1)
                    (hphysical := by omega)
                    (state := (family.program index).next layer state
                      (some false))
                    (source := middle) (target := target) hmiddle htarget tail
                    hcompatible.2
                  simpa [LayeredQueryProgram.executePhysicalStateFrom, layer,
                    hquery, hbit] using htail
          | true =>
              cases walk with
              | nil vertex =>
                  have heq :
                      selectorComponent index ⟨physical, by omega⟩ state =
                        (family.selectorFBDD).accept :=
                    hsource.symm.trans htarget
                  simp [selectorComponent, selectorFBDD, selectorSink] at heq
              | @cons _ middle _ edge tail =>
                  have hfirst : (family.selectorFBDD).CompatibleEdge input
                      (selectorComponent index ⟨physical, by omega⟩ state)
                        middle := by
                    simpa [hsource] using hcompatible.1
                  have hmiddle : middle = selectorComponent index
                      ⟨physical + 1, by omega⟩
                      ((family.program index).next layer state
                        (some true)) := by
                    simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                      selectorNode, selectorComponent, selectorSink, hlt,
                      layer, hquery, hbit, selectorNextBoundary] using hfirst
                  have htail := ih (physical := physical + 1)
                    (hphysical := by omega)
                    (state := (family.program index).next layer state
                      (some true))
                    (source := middle) (target := target) hmiddle htarget tail
                    hcompatible.2
                  simpa [LayeredQueryProgram.executePhysicalStateFrom, layer,
                    hquery, hbit] using htail

/-- Any compatible component-to-accept walk forces the deterministic suffix
execution of that component to accept. -/
theorem selectorComponentWalk_to_accept_implies_suffix_true {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index)
    (fuel physical : Nat) (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State)
    (walk : (family.selectorFBDD).Walk
      (selectorComponent index ⟨physical, by omega⟩ state)
      (family.selectorFBDD).accept)
    (hcompatible : walk.Compatible input) :
    (family.program index).output
      (LayeredQueryProgram.executePhysicalStateFrom
        (family.program index) input fuel physical hphysical state) = true :=
  selectorComponentWalk_to_accept_implies_suffix_true_aux family input index
    fuel physical hphysical state rfl rfl walk hcompatible

/-- Decoding a compatible walk from a component start recovers ordinary
component acceptance. -/
theorem selectorComponentWalk_to_accept_implies_eval_true {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (index : family.Index)
    (walk : (family.selectorFBDD).Walk
      (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
        (family.program index).start)
      (family.selectorFBDD).accept)
    (hcompatible : walk.Compatible input) :
    (family.program index).eval input = true := by
  have hsuffix := selectorComponentWalk_to_accept_implies_suffix_true
    family input index (family.layers index) 0 (by omega)
      (family.program index).start walk hcompatible
  have hfinal := LayeredQueryProgram.executePhysicalStateFrom_executePrefix
    (family.program index) input (family.layers index) 0 (by omega)
  have hfinal' :
      LayeredQueryProgram.executePhysicalStateFrom
          (family.program index) input (family.layers index) 0 (by omega)
            (family.program index).start =
        ((family.program index).executePrefix input
          (family.layers index) le_rfl).1 := by
    simpa [LayeredQueryProgram.executePrefix] using hfinal
  unfold LayeredQueryProgram.eval LayeredQueryProgram.finalState
  rw [← hfinal']
  exact hsuffix

/-- Endpoint-generalized root decoder.  The first silent edge identifies a
finite family component; the remaining compatible walk is then decoded by
the component theorem above. -/
theorem selectorRootWalk_to_accept_implies_exists_component_eval_true_aux
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n → Bool)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorRoot)
    (htarget : target = (family.selectorFBDD).accept)
    (walk : (family.selectorFBDD).Walk source target)
    (hcompatible : walk.Compatible input) :
    exists index, (family.program index).eval input = true := by
  classical
  letI : Fintype family.Index := family.indexFintype
  cases walk with
  | nil vertex =>
      have heq : (selectorRoot : family.SelectorVertex) =
          (family.selectorFBDD).accept := hsource.symm.trans htarget
      simp [selectorRoot, selectorFBDD, selectorSink] at heq
  | @cons _ middle _ edge tail =>
      have hfirst : (family.selectorFBDD).CompatibleEdge input
          selectorRoot middle := by
        simpa [hsource] using hcompatible.1
      have hmem : middle ∈ family.selectorStartChildren := by
        simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
          selectorNode, selectorRoot] using hfirst
      simp only [selectorStartChildren, List.mem_map] at hmem
      obtain ⟨index, _hindex, hmiddle⟩ := hmem
      have hsuffix :=
        selectorComponentWalk_to_accept_implies_suffix_true_aux family input
          index (family.layers index) 0 (by omega)
            (family.program index).start hmiddle.symm htarget tail
              hcompatible.2
      have hfinal := LayeredQueryProgram.executePhysicalStateFrom_executePrefix
        (family.program index) input (family.layers index) 0 (by omega)
      have hfinal' :
          LayeredQueryProgram.executePhysicalStateFrom
              (family.program index) input (family.layers index) 0 (by omega)
                (family.program index).start =
            ((family.program index).executePrefix input
              (family.layers index) le_rfl).1 := by
        simpa [LayeredQueryProgram.executePrefix] using hfinal
      refine ⟨index, ?_⟩
      unfold LayeredQueryProgram.eval LayeredQueryProgram.finalState
      rw [← hfinal']
      exact hsuffix

/-- Selector acceptance cannot arise spuriously: it decodes to an accepting
component of the finite family. -/
theorem selectorFBDD_eval_eq_true_of_accepts {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool)
    (haccepts : (family.selectorFBDD).Accepts input) :
    family.eval input = true := by
  obtain ⟨acceptingPath⟩ := haccepts
  have hexists :=
    selectorRootWalk_to_accept_implies_exists_component_eval_true_aux
      family input rfl rfl acceptingPath.walk acceptingPath.compatible
  exact (eval_eq_true_iff family input).2 hexists

/-- Exact existential semantics of the finite silent selector. -/
theorem selectorFBDD_accepts_iff_eval_eq_true {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n → Bool) :
    (family.selectorFBDD).Accepts input <-> family.eval input = true :=
  ⟨selectorFBDD_eval_eq_true_of_accepts family input,
    selectorFBDD_accepts_of_eval_eq_true family input⟩

end FiniteLayeredQueryProgramFamily
end OneTapeMagnification
end Frontier
end Pnp4
