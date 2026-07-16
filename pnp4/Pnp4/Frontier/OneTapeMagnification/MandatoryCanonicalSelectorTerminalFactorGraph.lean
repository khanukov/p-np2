import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalUFBDD
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaAdjacentCutFactorization
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDFourierFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped BigOperators

/-!
# Terminal fixed-alpha factor graph inside the mandatory selector

The mandatory fixed-order collapse has `n` query layers, but the underlying
guarded computation has already returned its Boolean result after the
`master.length`-th mandatory query.  This file identifies that exact terminal
component vertex and rewrites its compatible-prefix indicator as the
nearest-neighbour fixed-alpha factor graph.
-/

namespace LayeredQueryProgram

/-- At the end of the genuine master prefix, the mandatory collapse has
already entered its absorbing completed state.  The remaining completed-order
queries are semantically inert padding. -/
theorem collapseToMandatoryFixedOrder_executePrefix_masterLength_state
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (hmaster : master.Nodup)
    (input : Fin n → Bool) :
    let target := collapseToMandatoryFixedOrder program master hmaster
    (target.executePrefix input master.length
      (master_length_le_of_nodup master hmaster)).1 =
        Sum.inr (target.eval input) := by
  let target := collapseToMandatoryFixedOrder program master hmaster
  let hm : master.length ≤ n := master_length_le_of_nodup master hmaster
  have hinvariant :=
    collapseToMandatoryFixedOrder_executePrefix_invariant
      program master hmaster input master.length hm
  dsimp only at hinvariant ⊢
  generalize hstate :
      (target.executePrefix input master.length hm).1 = final
    at hinvariant ⊢
  cases final with
  | inl running =>
      have hvalid : MandatoryQueryStateValid program master master.length
          (Sum.inl running) := hinvariant.1
      simp only [MandatoryQueryStateValid] at hvalid
      obtain ⟨hcount, _⟩ := hvalid
      omega
  | inr done =>
      have hseek :
          mandatoryQueryStateResult program master input 0 target.start =
            rejectingMasterPhysicalResult program master input 0 L 0
              (by omega) program.start := by
        simpa [target, collapseToMandatoryFixedOrder] using
          mandatoryQuerySeek_result program master input 0 L 0 (by omega)
            program.start
      have heval : target.eval input = done := by
        calc
          target.eval input =
              rejectingMasterPhysicalResult program master input 0 L 0
                (by omega) program.start := by
            simpa [target] using
              collapseToMandatoryFixedOrder_eval_eq_physicalResult
                program master hmaster input
          _ = mandatoryQueryStateResult program master input 0
                target.start := hseek.symm
          _ = mandatoryQueryStateResult program master input master.length
                (Sum.inr done) := hinvariant.2
          _ = done := rfl
      exact congrArg Sum.inr heval.symm

/-- Once the mandatory collapse has produced a Boolean answer, every remaining
physical layer preserves that completed answer. -/
theorem collapseToMandatoryFixedOrder_executePhysicalStateFrom_completed
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (hmaster : master.Nodup)
    (input : Fin n → Bool) (value : Bool)
    (fuel physical : Nat) (hphysical : physical + fuel = n) :
    executePhysicalStateFrom
        (collapseToMandatoryFixedOrder program master hmaster)
        input fuel physical hphysical (Sum.inr value) =
      Sum.inr value := by
  induction fuel generalizing physical with
  | zero => rfl
  | succ fuel ih =>
      rw [executePhysicalStateFrom]
      exact ih (physical + 1) (by omega)

end LayeredQueryProgram

namespace FiniteLayeredQueryProgramFamily

/-- The deterministic execution of one family member has a compatible
selector walk from its component start to every program boundary. -/
private theorem exists_selectorComponentPrefixExecutionWalk
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (input : Fin n → Bool) (index : family.Index)
    (k : Nat) (hk : k ≤ family.layers index) :
    ∃ walk : (family.selectorFBDD).Walk
        (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
          (family.program index).start)
        (selectorComponent index ⟨k, by omega⟩
          ((family.program index).executePrefix input k hk).1),
      walk.Compatible input := by
  induction k with
  | zero =>
      refine ⟨FiniteUnambiguousFBDD.Walk.nil _, ?_⟩
      trivial
  | succ k ih =>
      let previous :=
        (family.program index).executePrefix input k (by omega)
      let layer : Fin (family.layers index) := ⟨k, by omega⟩
      have hlt : k < family.layers index := by omega
      let query := (family.program index).query? layer previous.1
      let nextState :=
        (family.program index).next layer previous.1 (query.map input)
      have hnextState :
          ((family.program index).executePrefix input (k + 1) hk).1 =
            nextState := by
        rfl
      obtain ⟨prefixWalk, hprefix⟩ := ih (by omega)
      let source := selectorComponent index ⟨k, by omega⟩ previous.1
      let target := selectorComponent index ⟨k + 1, by omega⟩ nextState
      have hcompatible : (family.selectorFBDD).CompatibleEdge input
          source target := by
        cases hquery : query with
        | none =>
            simp [source, target, nextState, query, layer, hquery,
              FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
              selectorNode, selectorComponent, selectorNextBoundary, hlt]
        | some coordinate =>
            cases hbit : input coordinate <;>
              simp [source, target, nextState, query, layer, hquery, hbit,
                FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                selectorNode, selectorComponent, selectorNextBoundary, hlt]
      have hedge : (family.selectorFBDD).Edge source target :=
        (family.selectorFBDD).edge_of_compatibleEdge input hcompatible
      let terminal : (family.selectorFBDD).Walk target target :=
        @FiniteUnambiguousFBDD.Walk.nil n family.selectorFBDD target
      let last : (family.selectorFBDD).Walk source target :=
        .cons hedge terminal
      have hlast : last.Compatible input := ⟨hcompatible, by trivial⟩
      have hend :
          selectorComponent index ⟨k, by omega⟩
              ((family.program index).executePrefix input k (by omega)).1 =
            source := by
        rfl
      let prefix' : (family.selectorFBDD).Walk
          (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
            (family.program index).start) source := hend ▸ prefixWalk
      have hprefix' : prefix'.Compatible input :=
        (walk_compatible_cast_target input hend prefixWalk).2 hprefix
      rw [hnextState]
      refine ⟨prefix'.append last, ?_⟩
      exact (FiniteUnambiguousFBDD.Walk.compatible_append
        input prefix' last).2 ⟨hprefix', hlast⟩

private theorem no_selectorSink_walk_to_selectorComponent_aux
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (value : Bool) (index : family.Index)
    (boundary : Fin (family.layers index + 1))
    (state : (family.program index).State)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorSink value)
    (htarget : target = selectorComponent index boundary state)
    (walk : (family.selectorFBDD).Walk source target) : False := by
  cases walk with
  | nil vertex =>
      have heq : (selectorSink value : family.SelectorVertex) =
          selectorComponent index boundary state := hsource.symm.trans htarget
      simp [selectorSink, selectorComponent] at heq
  | @cons _ middle _ edge tail =>
      rw [hsource] at edge
      simp [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
        selectorSink, FiniteUFBDDNode.HasChild] at edge

/-- Component edges never cross from one family index into another. -/
private theorem selectorComponentWalk_index_eq_aux
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (left right : family.Index)
    (leftBoundary : Fin (family.layers left + 1))
    (rightBoundary : Fin (family.layers right + 1))
    (leftState : (family.program left).State)
    (rightState : (family.program right).State)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorComponent left leftBoundary leftState)
    (htarget : target = selectorComponent right rightBoundary rightState)
    (walk : (family.selectorFBDD).Walk source target) :
    left = right := by
  induction walk generalizing left leftBoundary leftState with
  | nil vertex =>
      have heq : selectorComponent left leftBoundary leftState =
          selectorComponent right rightBoundary rightState :=
        hsource.symm.trans htarget
      have hindex := congrArg
        (fun vertex : family.SelectorVertex =>
          match vertex with
          | Sum.inr (Sum.inl slot) =>
              (some slot.1 : Option family.Index)
          | _ => none) heq
      change some left = some right at hindex
      exact Option.some.inj hindex
  | @cons source middle target edge tail ih =>
      rw [hsource] at edge
      by_cases hphysical : leftBoundary.val < family.layers left
      · let layer : Fin (family.layers left) :=
          ⟨leftBoundary.val, hphysical⟩
        let nextBoundary := selectorNextBoundary leftBoundary hphysical
        cases hquery : (family.program left).query? layer leftState with
        | none =>
            have hmiddle : middle = selectorComponent left nextBoundary
                ((family.program left).next layer leftState none) := by
              simpa [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
                selectorComponent, hphysical, layer, nextBoundary, hquery,
                FiniteUFBDDNode.HasChild] using edge
            exact ih left nextBoundary
              ((family.program left).next layer leftState none)
              hmiddle htarget
        | some coordinate =>
            have hmiddle :
                middle = selectorComponent left nextBoundary
                    ((family.program left).next layer leftState
                      (some false)) ∨
                  middle = selectorComponent left nextBoundary
                    ((family.program left).next layer leftState
                      (some true)) := by
              simpa [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
                selectorComponent, hphysical, layer, nextBoundary, hquery,
                FiniteUFBDDNode.HasChild] using edge
            rcases hmiddle with hmiddle | hmiddle
            · exact ih left nextBoundary
                ((family.program left).next layer leftState (some false))
                hmiddle htarget
            · exact ih left nextBoundary
                ((family.program left).next layer leftState (some true))
                hmiddle htarget
      · have hmiddle : middle =
            selectorSink ((family.program left).output leftState) := by
          simpa [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
            selectorComponent, hphysical, FiniteUFBDDNode.HasChild] using edge
        exact False.elim
          (no_selectorSink_walk_to_selectorComponent_aux family
            ((family.program left).output leftState) right rightBoundary
              rightState hmiddle htarget tail)

private theorem selectorComponentWalk_index_eq
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (left right : family.Index)
    (leftBoundary : Fin (family.layers left + 1))
    (rightBoundary : Fin (family.layers right + 1))
    (leftState : (family.program left).State)
    (rightState : (family.program right).State)
    (walk : (family.selectorFBDD).Walk
      (selectorComponent left leftBoundary leftState)
      (selectorComponent right rightBoundary rightState)) :
    left = right :=
  selectorComponentWalk_index_eq_aux family left right leftBoundary
    rightBoundary leftState rightState rfl rfl walk

local instance cachedInputMachineStateDecidableEqForTerminalFactorGraph
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- The component vertex immediately after all genuine queries in the
installed master have been consumed, with the completed answer fixed to
`true`.  Later mandatory layers are only ignored padding queries. -/
def mandatoryCanonicalSelectorMasterEndTrueVertex
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    (mandatoryFiniteRejectingGuardedCanonicalFamily
      machine n T b).SelectorVertex :=
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone :=
    builtRejectingGuardedCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  let hmaster :=
    builtRejectingGuardedCanonicalIndex_master_nodup machine n index
  selectorComponent index
    ⟨master.length,
      Nat.lt_succ_of_le
        (LayeredQueryProgram.master_length_le_of_nodup master hmaster)⟩
    (Sum.inr true)

/-- Reaching the fixed-`alpha` master-end `true` vertex is equivalent to that
installed mandatory component accepting the input. -/
theorem mandatoryCanonicalSelectorMasterEnd_hasCompatiblePrefix_iff_eval_true
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (input : Fin n → Bool) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily
      machine n T b
    (family.selectorFBDD).HasCompatiblePrefix input
        (mandatoryCanonicalSelectorMasterEndTrueVertex machine n index) ↔
      (mandatoryBuiltRejectingGuardedCanonicalComponent
        machine n index).eval input = true := by
  classical
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone :=
    builtRejectingGuardedCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  let hmaster :=
    builtRejectingGuardedCanonicalIndex_master_nodup machine n index
  let base :=
    compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine index.1 scheduled
  let component :=
    mandatoryBuiltRejectingGuardedCanonicalComponent machine n index
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily
    machine n T b
  let hm : master.length ≤ n :=
    LayeredQueryProgram.master_length_le_of_nodup master hmaster
  let terminal : family.SelectorVertex :=
    selectorComponent index
      ⟨master.length, Nat.lt_succ_of_le hm⟩ (Sum.inr true)
  change (family.selectorFBDD).HasCompatiblePrefix input terminal ↔
    component.eval input = true
  constructor
  · rintro ⟨walk, hcompatible⟩
    generalize hsource : (family.selectorFBDD).start = source at walk hcompatible
    generalize htarget : terminal = target at walk hcompatible
    cases walk with
    | nil vertex =>
        have heq : (selectorRoot : family.SelectorVertex) = terminal := by
          simpa [selectorFBDD] using hsource.trans htarget.symm
        simp [selectorRoot, terminal, selectorComponent] at heq
    | @cons source middle target edge tail =>
        have hfirst : (family.selectorFBDD).CompatibleEdge input
            selectorRoot middle := by
          have hsourceRoot : source = (selectorRoot : family.SelectorVertex) := by
            simpa [selectorFBDD] using hsource.symm
          simpa [hsourceRoot] using hcompatible.1
        have hmem : middle ∈ family.selectorStartChildren := by
          simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
            selectorNode, selectorRoot] using hfirst
        simp only [selectorStartChildren, List.mem_map] at hmem
        obtain ⟨left, _hleft, hmiddle⟩ := hmem
        have htargetComponent : target = selectorComponent index
            ⟨master.length, Nat.lt_succ_of_le hm⟩ (Sum.inr true) := by
          exact htarget.symm
        have hindex : left = index :=
          selectorComponentWalk_index_eq_aux family left index
            ⟨0, Nat.zero_lt_succ _⟩
            ⟨master.length, Nat.lt_succ_of_le hm⟩
            (family.program left).start (Sum.inr true)
            hmiddle.symm htargetComponent tail
        subst left
        let tail' : (family.selectorFBDD).Walk middle terminal :=
          htarget.symm ▸ tail
        have htail' : tail'.Compatible input :=
          (walk_compatible_cast_target input htarget.symm tail).2 hcompatible.2
        let execution := selectorComponentExecution family input index
          (n - master.length) master.length (by
            simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily]
            omega) (Sum.inr true)
        have hcompleted :=
          LayeredQueryProgram.collapseToMandatoryFixedOrder_executePhysicalStateFrom_completed
            base master hmaster input true (n - master.length)
              master.length (by omega)
        have hstate :
            LayeredQueryProgram.executePhysicalStateFrom
                (family.program index) input (n - master.length)
                  master.length (by
                    simp [family,
                      mandatoryFiniteRejectingGuardedCanonicalFamily]
                    omega) (Sum.inr true) =
              Sum.inr true := by
          simpa [family, component,
            mandatoryFiniteRejectingGuardedCanonicalFamily,
            mandatoryBuiltRejectingGuardedCanonicalComponent,
            base, scheduled, hmonotone, master, hmaster] using hcompleted
        have hresult : execution.result = true := by
          calc
            execution.result =
                (family.program index).output
                  (LayeredQueryProgram.executePhysicalStateFrom
                    (family.program index) input (n - master.length)
                      master.length (by
                        simp [family,
                          mandatoryFiniteRejectingGuardedCanonicalFamily]
                        omega) (Sum.inr true)) := execution.result_eq
            _ = true := by rw [hstate]; rfl
        have hend : selectorSink execution.result =
            (family.selectorFBDD).accept := by
          simp [selectorFBDD, hresult, selectorSink]
        let suffix : (family.selectorFBDD).Walk terminal
            (family.selectorFBDD).accept := hend ▸ execution.walk
        have hsuffix : suffix.Compatible input := by
          exact (walk_compatible_cast_target input hend execution.walk).2
            execution.compatible
        let combined := tail'.append suffix
        have hcombined : combined.Compatible input :=
          (FiniteUnambiguousFBDD.Walk.compatible_append
            input tail' suffix).2 ⟨htail', hsuffix⟩
        have houtput :=
          selectorComponentWalk_to_accept_implies_suffix_true_aux
            family input index n 0 (by
              simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily])
            (family.program index).start hmiddle.symm rfl combined hcombined
        have hfinal :=
          LayeredQueryProgram.executePhysicalStateFrom_executePrefix
            (family.program index) input n 0 (by
              simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily])
        have hfinal' :
            LayeredQueryProgram.executePhysicalStateFrom
                (family.program index) input n 0 (by
                  simp [family,
                    mandatoryFiniteRejectingGuardedCanonicalFamily])
                  (family.program index).start =
              ((family.program index).executePrefix input
                (family.layers index) le_rfl).1 := by
          simpa [LayeredQueryProgram.executePrefix] using hfinal
        have hevalFamily : (family.program index).eval input = true := by
          unfold LayeredQueryProgram.eval LayeredQueryProgram.finalState
          rw [← hfinal']
          exact houtput
        simpa [family, component,
          mandatoryFiniteRejectingGuardedCanonicalFamily] using hevalFamily
  · intro heval
    have hevalFamily : (family.program index).eval input = true := by
      simpa [family, component,
        mandatoryFiniteRejectingGuardedCanonicalFamily] using heval
    obtain ⟨prefixWalk, hprefix⟩ :=
      exists_selectorComponentPrefixExecutionWalk family input index
        master.length (by
          simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily]
          exact hm)
    have hmasterEnd :=
      LayeredQueryProgram.collapseToMandatoryFixedOrder_executePrefix_masterLength_state
        base master hmaster input
    have hstate :
        ((family.program index).executePrefix input master.length (by
          simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily]
          exact hm)).1 = Sum.inr true := by
      calc
        ((family.program index).executePrefix input master.length (by
          simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily]
          exact hm)).1 =
            Sum.inr ((family.program index).eval input) := by
              simpa [family, component,
                mandatoryFiniteRejectingGuardedCanonicalFamily,
                mandatoryBuiltRejectingGuardedCanonicalComponent,
                base, scheduled, hmonotone, master, hmaster] using hmasterEnd
        _ = Sum.inr true := congrArg Sum.inr hevalFamily
    have hend :
        selectorComponent index
            ⟨master.length, by
              simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily]
              exact Nat.lt_succ_of_le hm⟩
            ((family.program index).executePrefix input master.length (by
              simp [family, mandatoryFiniteRejectingGuardedCanonicalFamily]
              exact hm)).1 = terminal := by
      simp only [terminal]
      rw [hstate]
    let componentPrefix : (family.selectorFBDD).Walk
        (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
          (family.program index).start) terminal := hend ▸ prefixWalk
    have hcomponentPrefix : componentPrefix.Compatible input :=
      (walk_compatible_cast_target input hend prefixWalk).2 hprefix
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
    exact ⟨.cons hrootEdge componentPrefix,
      ⟨hrootCompatible, hcomponentPrefix⟩⟩

/-- Exact terminal bridge from the selector prefix indicator to the
nearest-neighbour fixed-`alpha` factor graph.  The unary factors certify each
advertised block replay, and the edge factors certify adjacent canonical cuts.
The schedule-validity factor is input-independent. -/
theorem mandatoryCanonicalSelectorMasterEnd_ratCompatiblePrefixIndicator_eq_factorGraph
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    let cached := cachedInputMachine machine
    let scheduled := builtTimedAlphaVisitSchedule cached index.1
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily
      machine input.length T b
    (family.selectorFBDD).ratCompatiblePrefixIndicator
        (fun coordinate => input.get coordinate)
        (mandatoryCanonicalSelectorMasterEndTrueVertex
          machine input.length index) =
      finiteRatPropIndicator
          (TimedAlphaVisitScheduleValid cached index.1 scheduled) *
        (∏ block : Fin (T / b + 1),
          finiteRatPropIndicator
            (TimedScheduleBlockReplayAcceptedFromBlank
              cached input index.1 scheduled block)) *
        (∏ bucket : Fin (T / b),
          finiteRatPropIndicator
            (TimedScheduleAdjacentCutIsLeftmostMinimum
              cached input index.1 scheduled bucket)) := by
  classical
  let cached := cachedInputMachine machine
  let scheduled := builtTimedAlphaVisitSchedule cached index.1
  let component := mandatoryBuiltRejectingGuardedCanonicalComponent
    machine input.length index
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily
    machine input.length T b
  let terminal := mandatoryCanonicalSelectorMasterEndTrueVertex
    machine input.length index
  change (family.selectorFBDD).ratCompatiblePrefixIndicator
      (fun coordinate => input.get coordinate) terminal = _
  have hprefix :=
    mandatoryCanonicalSelectorMasterEnd_hasCompatiblePrefix_iff_eval_true
      machine input.length index (fun coordinate => input.get coordinate)
  have hindicator :
      (family.selectorFBDD).ratCompatiblePrefixIndicator
          (fun coordinate => input.get coordinate) terminal =
        finiteRatPropIndicator
          (component.eval (fun coordinate => input.get coordinate) = true) := by
    have hprefix' : (family.selectorFBDD).HasCompatiblePrefix
          (fun coordinate => input.get coordinate) terminal ↔
        component.eval (fun coordinate => input.get coordinate) = true := by
      simpa [family, component, terminal] using hprefix
    rw [FiniteUnambiguousFBDD.ratCompatiblePrefixIndicator,
      FiniteUnambiguousFBDD.compatiblePrefixIndicator,
      finiteRatPropIndicator, propext hprefix']
    simp
  have hevalCheck :
      component.eval (fun coordinate => input.get coordinate) =
        timedAlphaVisitScheduleInPlaceCanonicalCutCheck
          cached input index.1 scheduled := by
    calc
      component.eval (fun coordinate => input.get coordinate) =
          ((finiteRejectingGuardedCanonicalFamily
            machine input.length T b).program index).eval
              (fun coordinate => input.get coordinate) :=
        mandatoryBuiltRejectingGuardedCanonicalComponent_eval_eq_family
          machine input.length index
            (fun coordinate => input.get coordinate)
      _ = timedAlphaVisitScheduleInPlaceCanonicalCutCheck
            cached input index.1 scheduled := by
        change
          (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
            (n := input.length) machine index.1 scheduled).eval
              (fun coordinate => input.get coordinate) = _
        exact
          compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_inPlaceCanonicalCutCheck
            machine input index.1 scheduled
  rw [hindicator, hevalCheck]
  exact finiteRatPropIndicator_inPlaceCanonicalCutCheck_eq_factorGraph
    cached input T b hb index.1 scheduled

end FiniteLayeredQueryProgramFamily

end OneTapeMagnification
end Frontier
end Pnp4
