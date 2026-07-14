import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FixedVisitFreshPrefixSync

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Soundness of the canonical fixed-visit compiler

This file develops the reverse direction of the canonical visit compiler.
The first layer is an operational head-accounting invariant: every streaming
microstep, every silent closure, every compiled query, and the final terminal
closure can only move the one-way input head to the right.  In particular, an
accepted endpoint can never hide a genuinely consumed dummy-suffix query by
later moving the input head back to its advertised value.
-/

/-- Reachability preorder seen by the one-way input head.  A rejected target
is retained because rejection is absorbing; there is deliberately no
constructor from a rejected source to a live or completed target. -/
inductive FiniteCachedVisitPhaseHeadLe
    {State : Type} {H w : Nat} :
    FiniteCachedVisitStreamingState State H w ->
      FiniteCachedVisitStreamingState State H w -> Prop
  | running_running
      {remaining nextRemaining : Fin (H + 1)}
      {live next : LocalReplayState State H w}
      (head_le : live.inputHead.val <= next.inputHead.val) :
      FiniteCachedVisitPhaseHeadLe (.running remaining live)
        (.running nextRemaining next)
  | running_completed
      {remaining : Fin (H + 1)}
      {live : LocalReplayState State H w}
      {final : FiniteLocalFinalState State H w}
      (head_le : live.inputHead.val <= final.inputHead.val) :
      FiniteCachedVisitPhaseHeadLe (.running remaining live) (.completed final)
  | completed_completed
      {initial final : FiniteLocalFinalState State H w}
      (head_le : initial.inputHead.val <= final.inputHead.val) :
      FiniteCachedVisitPhaseHeadLe (.completed initial) (.completed final)
  | to_rejected
      (source : FiniteCachedVisitStreamingState State H w)
      (failure : FiniteCachedVisitStreamingFailure) :
      FiniteCachedVisitPhaseHeadLe source (.rejected failure)

namespace FiniteCachedVisitPhaseHeadLe

/-- Reflexivity of phase head reachability. -/
theorem refl
    {State : Type} {H w : Nat}
    (phase : FiniteCachedVisitStreamingState State H w) :
    FiniteCachedVisitPhaseHeadLe phase phase := by
  cases phase with
  | running remaining live =>
      exact .running_running le_rfl
  | completed final =>
      exact .completed_completed le_rfl
  | rejected failure =>
      exact .to_rejected (.rejected failure) failure

/-- Transitivity of phase head reachability. -/
theorem trans
    {State : Type} {H w : Nat}
    {first second third : FiniteCachedVisitStreamingState State H w}
    (hfirst : FiniteCachedVisitPhaseHeadLe first second)
    (hsecond : FiniteCachedVisitPhaseHeadLe second third) :
    FiniteCachedVisitPhaseHeadLe first third := by
  cases hfirst with
  | running_running hfirst =>
      cases hsecond with
      | running_running hsecond =>
          exact .running_running (le_trans hfirst hsecond)
      | running_completed hsecond =>
          exact .running_completed (le_trans hfirst hsecond)
      | to_rejected _ failure =>
          exact .to_rejected _ failure
  | running_completed hfirst =>
      cases hsecond with
      | completed_completed hsecond =>
          exact .running_completed (le_trans hfirst hsecond)
      | to_rejected _ failure =>
          exact .to_rejected _ failure
  | completed_completed hfirst =>
      cases hsecond with
      | completed_completed hsecond =>
          exact .completed_completed (le_trans hfirst hsecond)
      | to_rejected _ failure =>
          exact .to_rejected _ failure
  | to_rejected source failure =>
      cases hsecond with
      | to_rejected _ nextFailure =>
          exact .to_rejected _ nextFailure

end FiniteCachedVisitPhaseHeadLe

/-- Resolving one cached transition never moves the one-way input head left. -/
theorem advanceFiniteCachedVisitPhase_headLe
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) :
    FiniteCachedVisitPhaseHeadLe (.running remaining live)
      (advanceFiniteCachedVisitPhase machine H w base hbound
        remaining live unread) := by
  unfold advanceFiniteCachedVisitPhase
  split
  · exact .to_rejected _ _
  · rename_i hzero
    split
    · rename_i hlast
      cases hstep : finiteLocalCachedFinalStep machine H w base unread live with
      | stepped final =>
          apply FiniteCachedVisitPhaseHeadLe.running_completed
          have hhead := finiteLocalCachedFinalStep_stepped_inputHead_eq
            machine unread live final hstep
          by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
          · rw [hhead]
            simp [hneeds]
          · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
              cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
            rw [hhead]
            simp [hneedsFalse]
      | halted outcome =>
          exact .running_completed le_rfl
      | inputHorizonExceeded =>
          exact .to_rejected _ _
      | workHorizonExceeded =>
          exact .to_rejected _ _
    · rename_i hlast
      cases hstep : finiteLocalCachedStep machine H w base unread live with
      | inside next =>
          apply FiniteCachedVisitPhaseHeadLe.running_running
          have hhead := finiteLocalCachedStep_inside_inputHead_eq
            machine unread live next hstep
          by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
          · rw [hhead]
            simp [hneeds]
          · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
              cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
            rw [hhead]
            simp [hneedsFalse]
      | halted outcome =>
          exact .running_running le_rfl
      | workHeadExit =>
          exact .to_rejected _ _
      | inputHorizonExceeded =>
          exact .to_rejected _ _

/-- Every specialized streaming microstep preserves the phase head preorder. -/
theorem finiteCachedVisitStreamingStep_headLe
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w <= H + 1)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w)
    (supplied : Option ReadOnlySymbol) :
    FiniteCachedVisitPhaseHeadLe phase
      (finiteCachedVisitStreamingStep machine n H w base hbound
        phase supplied) := by
  cases phase with
  | completed final =>
      exact FiniteCachedVisitPhaseHeadLe.refl _
  | rejected failure =>
      exact FiniteCachedVisitPhaseHeadLe.refl _
  | running remaining live =>
      by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
      · by_cases hhead : live.inputHead.val < n
        · cases supplied with
          | none =>
              simpa [finiteCachedVisitStreamingStep, hneeds, hhead] using
                (FiniteCachedVisitPhaseHeadLe.to_rejected
                  (.running remaining live) .missingFreshInput)
          | some unread =>
              simpa [finiteCachedVisitStreamingStep, hneeds, hhead] using
                advanceFiniteCachedVisitPhase_headLe machine hbound
                  remaining live unread
        · cases supplied with
          | none =>
              simpa [finiteCachedVisitStreamingStep, hneeds, hhead] using
                advanceFiniteCachedVisitPhase_headLe machine hbound
                  remaining live .rightEnd
          | some unread =>
              simpa [finiteCachedVisitStreamingStep, hneeds, hhead] using
                (FiniteCachedVisitPhaseHeadLe.to_rejected
                  (.running remaining live) .unexpectedInput)
      · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
          cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
        cases supplied with
        | none =>
            simpa [finiteCachedVisitStreamingStep, hneedsFalse] using
              advanceFiniteCachedVisitPhase_headLe machine hbound
                remaining live .rightEnd
        | some unread =>
            simpa [finiteCachedVisitStreamingStep, hneedsFalse] using
              (FiniteCachedVisitPhaseHeadLe.to_rejected
                (.running remaining live) .unexpectedInput)

/-- If a transition genuinely needs an unread symbol and its result can still
reach a completed phase, its input head is strictly below that completed
head.  The rejected cases disappear because rejection is absorbing in
`FiniteCachedVisitPhaseHeadLe`. -/
theorem advanceFiniteCachedVisitPhase_inputHead_lt_of_needsUnread_of_reaches
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State H w)
    (hneeds : cachedLocalStepNeedsUnread machine live = true)
    (hreaches : FiniteCachedVisitPhaseHeadLe
      (advanceFiniteCachedVisitPhase machine H w base hbound
        remaining live unread) (.completed final)) :
    live.inputHead.val < final.inputHead.val := by
  cases hadvance : advanceFiniteCachedVisitPhase machine H w base hbound
      remaining live unread with
  | running nextRemaining next =>
      have hzero : remaining.val ≠ 0 := by
        intro hzero
        simp [advanceFiniteCachedVisitPhase, hzero] at hadvance
      have hlast : remaining.val ≠ 1 := by
        intro hlast
        simp [advanceFiniteCachedVisitPhase, hlast] at hadvance
        cases hstep : finiteLocalCachedFinalStep machine H w base unread live <;>
          simp [hstep] at hadvance
      have hhead := advanceFiniteCachedVisitPhase_running_inputHead_eq
        machine hbound remaining nextRemaining live next unread hzero hlast
          hadvance
      rw [hadvance] at hreaches
      cases hreaches with
      | running_completed htail =>
          simp [hneeds] at hhead
          omega
  | completed steppedFinal =>
      have hlast : remaining.val = 1 := by
        by_contra hlast
        by_cases hzero : remaining.val = 0
        · simp [advanceFiniteCachedVisitPhase, hzero] at hadvance
        · simp [advanceFiniteCachedVisitPhase, hzero, hlast] at hadvance
          split at hadvance <;> contradiction
      have hhead := advanceFiniteCachedVisitPhase_completed_inputHead_eq
        machine hbound remaining live unread steppedFinal hlast hadvance
      rw [hadvance] at hreaches
      cases hreaches with
      | completed_completed htail =>
          simp [hneeds] at hhead
          omega
  | rejected failure =>
      rw [hadvance] at hreaches
      cases hreaches

/-- Consuming a supplied symbol at a genuine in-range request strictly raises
the head below every later completed phase. -/
theorem finiteCachedVisitStreamingStep_inputHead_lt_of_request_of_reaches
    (machine : DeterministicMachine) (n : Nat)
    {H w base : Nat} (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State H w)
    (hrequest : finiteCachedVisitPhaseRequestsInput machine n
      (.running remaining live) = true)
    (hreaches : FiniteCachedVisitPhaseHeadLe
      (finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live) (some unread)) (.completed final)) :
    live.inputHead.val < final.inputHead.val := by
  have hparts :=
    (finiteCachedVisitPhaseRequestsInput_running_eq_true_iff
      machine n remaining live).mp hrequest
  have hneeds := hparts.2.1
  have hhead := hparts.2.2
  have hreaches' : FiniteCachedVisitPhaseHeadLe
      (advanceFiniteCachedVisitPhase machine H w base hbound
        remaining live unread) (.completed final) := by
    simpa [finiteCachedVisitStreamingStep, hneeds, hhead] using hreaches
  exact advanceFiniteCachedVisitPhase_inputHead_lt_of_needsUnread_of_reaches
    machine hbound remaining live unread final hneeds hreaches'

/-- Exact no-dummy-query obstruction at an advertised endpoint: once a live
phase is already at the expected input head, consuming another genuine input
query is incompatible with later acceptance at that same endpoint. -/
theorem freshQuery_at_expectedInputHead_precludes_acceptance
    (machine : DeterministicMachine) [DecidableEq machine.State] (n : Nat)
    {H w base : Nat} (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State H w)
    (hatExpected : expected.inputHead = live.inputHead)
    (hrequest : finiteCachedVisitPhaseRequestsInput machine n
      (.running remaining live) = true)
    (hreaches : FiniteCachedVisitPhaseHeadLe
      (finiteCachedVisitStreamingStep machine n H w base hbound
        (.running remaining live) (some unread)) (.completed final))
    (haccept : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State (cachedInputStateDecidableEq machine)
      H w expected (.completed final) = true) :
    False := by
  have hstrict := finiteCachedVisitStreamingStep_inputHead_lt_of_request_of_reaches
    machine n hbound remaining live unread final hrequest hreaches
  have hendpoint :=
    (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
      (cachedInputMachine machine).State (cachedInputStateDecidableEq machine)
      H w expected final).mp haccept
  have hsame : live.inputHead.val = final.inputHead.val := by
    rw [← hatExpected, hendpoint.2.1]
  omega

namespace FiniteStreamingVerifier

variable {Symbol : Type}

/-- Any reflexive transitive relation preserved by silent verifier steps is
preserved by the whole recursive silent closure. -/
theorem silentClosureCore_relation
    (verifier : FiniteStreamingVerifier Symbol)
    (R : verifier.State -> verifier.State -> Prop)
    (hrefl : forall state, R state state)
    (htrans : forall {first second third},
      R first second -> R second third -> R first third)
    (hstep : forall state, R state (verifier.step state none))
    (fuel : Nat) (state : verifier.State) :
    R state (verifier.silentClosureCore fuel state).1 := by
  induction fuel generalizing state with
  | zero => exact hrefl _
  | succ fuel ih =>
      unfold silentClosureCore
      split
      · exact hrefl _
      · exact htrans (hstep state) (ih (verifier.step state none))

/-- Fixed-horizon silent closure preserves any such relation. -/
theorem silentClosure_relation
    (verifier : FiniteStreamingVerifier Symbol)
    (R : verifier.State -> verifier.State -> Prop)
    (hrefl : forall state, R state state)
    (htrans : forall {first second third},
      R first second -> R second third -> R first third)
    (hstep : forall state, R state (verifier.step state none))
    {K : Nat} (state : verifier.FueledState K) :
    R state.1 (verifier.silentClosure state).1 := by
  exact verifier.silentClosureCore_relation R hrefl htrans hstep _ _

/-- One compiled query preserves a relation whenever every underlying
optional-symbol microstep does. -/
theorem consumeQuery_relation
    (verifier : FiniteStreamingVerifier Symbol)
    (R : verifier.State -> verifier.State -> Prop)
    (hrefl : forall state, R state state)
    (htrans : forall {first second third},
      R first second -> R second third -> R first third)
    (hstep : forall state supplied, R state (verifier.step state supplied))
    {K : Nat} (encode : Bool -> Symbol)
    (state : verifier.FueledState K) (answer : Bool) :
    R state.1 (verifier.consumeQuery encode state answer).1 := by
  have hclosed : R state.1 (verifier.silentClosure state).1 :=
    verifier.silentClosure_relation R hrefl htrans
      (fun phase => hstep phase none) state
  unfold consumeQuery
  generalize hclosure : verifier.silentClosure state = closed at hclosed ⊢
  dsimp only
  split
  · exact htrans hclosed (hstep _ _)
  · exact hclosed

/-- Folding any list of hardwired query answers preserves the relation. -/
theorem foldl_consumeQuery_relation
    (verifier : FiniteStreamingVerifier Symbol)
    (R : verifier.State -> verifier.State -> Prop)
    (hrefl : forall state, R state state)
    (htrans : forall {first second third},
      R first second -> R second third -> R first third)
    (hstep : forall state supplied, R state (verifier.step state supplied))
    {K : Nat} (encode : Bool -> Symbol)
    (answers : List Bool) (state : verifier.FueledState K) :
    R state.1 (answers.foldl (verifier.consumeQuery encode) state).1 := by
  induction answers generalizing state with
  | nil => exact hrefl _
  | cons answer answers ih =>
      simp only [List.foldl_cons]
      exact htrans
        (verifier.consumeQuery_relation R hrefl htrans hstep encode state answer)
        (ih (verifier.consumeQuery encode state answer))

/-- Terminal end-symbol closure preserves the relation. -/
theorem terminalClosureCore_relation
    (verifier : FiniteStreamingVerifier Symbol)
    (R : verifier.State -> verifier.State -> Prop)
    (hrefl : forall state, R state state)
    (htrans : forall {first second third},
      R first second -> R second third -> R first third)
    (hstep : forall state supplied, R state (verifier.step state supplied))
    (endSymbol : Symbol) (fuel : Nat) (state : verifier.State) :
    R state (verifier.terminalClosureCore endSymbol fuel state) := by
  induction fuel generalizing state with
  | zero => exact hrefl _
  | succ fuel ih =>
      unfold terminalClosureCore
      split
      · exact hrefl _
      · exact htrans (hstep state _) (ih _)

/-- Final closure of a fueled state preserves the relation. -/
theorem finishWithEndSymbol_relation
    (verifier : FiniteStreamingVerifier Symbol)
    (R : verifier.State -> verifier.State -> Prop)
    (hrefl : forall state, R state state)
    (htrans : forall {first second third},
      R first second -> R second third -> R first third)
    (hstep : forall state supplied, R state (verifier.step state supplied))
    {K : Nat} (endSymbol : Symbol) (state : verifier.FueledState K) :
    R state.1 (verifier.finishWithEndSymbol endSymbol state) := by
  exact verifier.terminalClosureCore_relation R hrefl htrans hstep endSymbol
    state.2.val state.1

end FiniteStreamingVerifier

/-- The complete compressed execution of a finite cached visit can never
decrease its one-way input head or escape from an already rejected phase. -/
theorem finiteCachedVisitFinishFold_headLe
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n H w base : Nat) (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (start : LocalReplayState (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    (answers : List Bool)
    (initial : (finiteCachedVisitStreamingVerifier machine n H w base hbound
      remaining start expected).FueledState H) :
    let verifier := finiteCachedVisitStreamingVerifier machine n H w base
      hbound remaining start expected
    FiniteCachedVisitPhaseHeadLe initial.1
      (verifier.finishWithEndSymbol .rightEnd
        (answers.foldl (verifier.consumeQuery (fun bit => .bit bit))
          initial)) := by
  let verifier := finiteCachedVisitStreamingVerifier machine n H w base
    hbound remaining start expected
  have hstep : forall phase supplied,
      FiniteCachedVisitPhaseHeadLe phase (verifier.step phase supplied) := by
    intro phase supplied
    exact finiteCachedVisitStreamingStep_headLe machine n hbound phase supplied
  have hfold : FiniteCachedVisitPhaseHeadLe initial.1
      (answers.foldl (verifier.consumeQuery (fun bit => .bit bit)) initial).1 :=
    verifier.foldl_consumeQuery_relation FiniteCachedVisitPhaseHeadLe
      FiniteCachedVisitPhaseHeadLe.refl
      (fun hfirst hsecond => hfirst.trans hsecond)
      hstep _ answers initial
  exact hfold.trans
    (verifier.finishWithEndSymbol_relation FiniteCachedVisitPhaseHeadLe
      FiniteCachedVisitPhaseHeadLe.refl
      (fun hfirst hsecond => hfirst.trans hsecond)
      hstep .rightEnd _)

/-- A canonical fixed-visit program cannot accept an endpoint whose input
head lies to the left of its entry head.  This is the externally visible
head-accounting consequence of the full compiler execution, including the
dummy suffix and terminal closure. -/
theorem compileFixedVisitFiniteQueryOrder_entryInputHead_le_exitInputHead
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (haccept :
      (compileFiniteCachedFixedAlphaVisit machine alpha block visit carried
        hentry (fixedVisitFiniteQueryOrder input.length visit)
        (fixedVisitFiniteQueryOrder_length input.length visit)).eval
          (fun position => input.get position) = true) :
    visit.entry.inputHead.val <= visit.exit.inputHead.val := by
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  let answers := (fixedVisitFiniteQueryOrder input.length visit).map
    (fun position => input.get position)
  have haccept' : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State (cachedInputStateDecidableEq machine)
      T (advertisedBlockWidth alpha.offsets block) visit.exit
      (verifier.finishWithEndSymbol .rightEnd
        (answers.foldl (verifier.consumeQuery (fun bit => .bit bit))
          (verifier.initialFueledState T))) = true := by
    change (verifier.compileFixedOrderList T (fun bit => .bit bit) .rightEnd
      (fixedVisitFiniteQueryOrder input.length visit)
      (fixedVisitFiniteQueryOrder_length input.length visit)).eval
        (fun position => input.get position) = true at haccept
    rw [FiniteStreamingVerifier.compileFixedOrderList] at haccept
    rw [verifier.compileFixedOrder_eval] at haccept
    rw [verifier.runFixedOrder_fixedOrderFunctionOfList] at haccept
    simpa [answers] using haccept
  generalize hfinished : verifier.finishWithEndSymbol .rightEnd
      (answers.foldl (verifier.consumeQuery (fun bit => .bit bit))
        (verifier.initialFueledState T)) = finished at haccept'
  cases finished with
  | running remaining live =>
      simp [finiteCachedVisitPhaseAccept] at haccept'
  | rejected failure =>
      simp [finiteCachedVisitPhaseAccept] at haccept'
  | completed final =>
      have hendpoint :=
        (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block)
          visit.exit final).mp haccept'
      let initial := finiteCachedStateOfVisitEntry machine alpha block visit
        carried hentry
      have hreach := finiteCachedVisitFinishFold_headLe machine input.length T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        (fixedAlphaVisitRemaining visit) initial visit.exit answers
        (verifier.initialFueledState T)
      have hreach' : FiniteCachedVisitPhaseHeadLe
          (.running (fixedAlphaVisitRemaining visit) initial)
          (.completed final) := by
        change FiniteCachedVisitPhaseHeadLe
          (.running (fixedAlphaVisitRemaining visit) initial)
          (verifier.finishWithEndSymbol .rightEnd
            (answers.foldl (verifier.consumeQuery (fun bit => .bit bit))
              (verifier.initialFueledState T))) at hreach
        rw [hfinished] at hreach
        exact hreach
      cases hreach' with
      | running_completed hhead =>
          change visit.entry.inputHead.val <= final.inputHead.val at hhead
          calc
            visit.entry.inputHead.val <= final.inputHead.val := hhead
            _ = visit.exit.inputHead.val :=
              congrArg Fin.val hendpoint.2.1.symm

end OneTapeMagnification
end Frontier
end Pnp4
