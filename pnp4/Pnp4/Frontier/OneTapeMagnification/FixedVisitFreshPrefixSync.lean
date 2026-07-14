import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FixedVisitOrderRealization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Closing the canonical fresh prefix of one cached visit

This module discharges the local synchronization obligation isolated by
`FixedVisitFreshPrefixClosesToComparison`.  The generic part records an exact
streaming trace and proves that silent closure compresses precisely its
input-free steps.  The specialized part identifies the queried bits of a
completed cached-visit trace with its half-open input-head interval.
-/

namespace FiniteStreamingVerifier

variable {Symbol : Type}

/-- A microstep trace whose only external symbols are the listed Boolean
answers.  The step count includes both silent and querying microsteps. -/
inductive ExactFreshTrace
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool -> Symbol) :
    Nat -> verifier.State -> List Bool -> verifier.State -> Prop
  | halted (state : verifier.State)
      (hhalted : verifier.halted state = true) :
      ExactFreshTrace verifier encode 0 state [] state
  | silent {steps : Nat} {state target : verifier.State}
      {answers : List Bool}
      (hhalted : verifier.halted state = false)
      (hrequest : verifier.requestsInput state = false)
      (tail : ExactFreshTrace verifier encode steps
        (verifier.step state none) answers target) :
      ExactFreshTrace verifier encode (steps + 1) state answers target
  | query {steps : Nat} {state target : verifier.State}
      {bit : Bool} {answers : List Bool}
      (hhalted : verifier.halted state = false)
      (hrequest : verifier.requestsInput state = true)
      (tail : ExactFreshTrace verifier encode steps
        (verifier.step state (some (encode bit))) answers target) :
      ExactFreshTrace verifier encode (steps + 1) state (bit :: answers) target

/-- A positive silent state can be removed before taking silent closure. -/
theorem silentClosure_eq_silentClosure_step_none
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (state : verifier.State) (fuel : Fin (H + 1))
    (hpositive : 0 < fuel.val)
    (hhalted : verifier.halted state = false)
    (hrequest : verifier.requestsInput state = false) :
    verifier.silentClosure (state, fuel) =
      verifier.silentClosure
        (verifier.step state none, spendOne fuel) := by
  rcases fuel with ⟨fuel, hfuel⟩
  cases fuel with
  | zero => simp at hpositive
  | succ fuel =>
      simp [silentClosure, silentClosureCore, spendOne,
        hhalted, hrequest]

/-- Removing one leading silent microstep does not change the result of the
next compiled query. -/
theorem consumeQuery_eq_consumeQuery_step_none
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (encode : Bool -> Symbol) (state : verifier.State)
    (fuel : Fin (H + 1)) (answer : Bool)
    (hpositive : 0 < fuel.val)
    (hhalted : verifier.halted state = false)
    (hrequest : verifier.requestsInput state = false) :
    verifier.consumeQuery encode (state, fuel) answer =
      verifier.consumeQuery encode
        (verifier.step state none, spendOne fuel) answer := by
  unfold consumeQuery
  rw [verifier.silentClosure_eq_silentClosure_step_none
    state fuel hpositive hhalted hrequest]

/-- Removing one leading silent microstep is also valid when no further query
remains and the final operation is silent closure itself. -/
theorem closeAfterAnswers_eq_closeAfterAnswers_step_none
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (encode : Bool -> Symbol) (state : verifier.State)
    (fuel : Fin (H + 1)) (answers : List Bool)
    (hpositive : 0 < fuel.val)
    (hhalted : verifier.halted state = false)
    (hrequest : verifier.requestsInput state = false) :
    verifier.silentClosure
        (answers.foldl (verifier.consumeQuery encode) (state, fuel)) =
      verifier.silentClosure
        (answers.foldl (verifier.consumeQuery encode)
          (verifier.step state none, spendOne fuel)) := by
  cases answers with
  | nil =>
      exact verifier.silentClosure_eq_silentClosure_step_none
        state fuel hpositive hhalted hrequest
  | cons answer rest =>
      simp only [List.foldl_cons]
      rw [verifier.consumeQuery_eq_consumeQuery_step_none
        encode state fuel answer hpositive hhalted hrequest]

/-- Silent closure stops immediately at a fresh-input request. -/
theorem silentClosure_eq_self_of_requestsInput
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (state : verifier.State) (fuel : Fin (H + 1))
    (hrequest : verifier.requestsInput state = true) :
    verifier.silentClosure (state, fuel) = (state, fuel) := by
  rcases fuel with ⟨fuel, hfuel⟩
  cases fuel with
  | zero => rfl
  | succ fuel => simp [silentClosure, silentClosureCore, hrequest]

/-- At a positive requesting state, one compiled query performs exactly the
corresponding symbol-supplying microstep. -/
theorem consumeQuery_eq_step_some_of_requestsInput
    (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (encode : Bool -> Symbol) (state : verifier.State)
    (fuel : Fin (H + 1)) (answer : Bool)
    (hpositive : 0 < fuel.val)
    (hhalted : verifier.halted state = false)
    (hrequest : verifier.requestsInput state = true) :
    verifier.consumeQuery encode (state, fuel) answer =
      (verifier.step state (some (encode answer)), spendOne fuel) := by
  unfold consumeQuery
  rw [verifier.silentClosure_eq_self_of_requestsInput
    state fuel hrequest]
  simp [hpositive, hhalted, hrequest]

/-- Folding the trace's fresh answers and closing silent steps reaches its
terminal target. -/
theorem ExactFreshTrace.closeAfterAnswers
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool -> Symbol)
    {steps : Nat} {state target : verifier.State} {answers : List Bool}
    (trace : ExactFreshTrace verifier encode steps state answers target)
    {H : Nat} (fuel : Fin (H + 1)) (hsteps : steps <= fuel.val) :
    (verifier.silentClosure
      (answers.foldl (verifier.consumeQuery encode) (state, fuel))).1 =
        target := by
  induction trace generalizing fuel with
  | halted state hhalted =>
      simp only [List.foldl_nil]
      rw [verifier.silentClosure_eq_self_of_halted
        (state, fuel) hhalted]
  | @silent steps state target answers hhalted hrequest tail ih =>
      have hpositive : 0 < fuel.val := by omega
      rw [verifier.closeAfterAnswers_eq_closeAfterAnswers_step_none
        encode state fuel answers hpositive hhalted hrequest]
      apply ih (spendOne fuel)
      simp only [spendOne]
      omega
  | @query steps state target bit answers hhalted hrequest tail ih =>
      have hpositive : 0 < fuel.val := by omega
      simp only [List.foldl_cons]
      rw [verifier.consumeQuery_eq_step_some_of_requestsInput
        encode state fuel bit hpositive hhalted hrequest]
      apply ih (spendOne fuel)
      simp only [spendOne]
      omega

end FiniteStreamingVerifier

/-- An in-range immutable-tape read is the corresponding Boolean symbol. -/
@[simp]
theorem readOnlySymbol_eq_bit_get
    (input : List Bool) (position : Fin input.length) :
    readOnlySymbol input position.val = .bit (input.get position) := by
  simp [readOnlySymbol]

/-- The first in-range coordinate of a natural interval survives finite-input
filtering. -/
theorem finiteInputVariableQueryOrder_range'_succ_of_lt
    {n start count : Nat} (hstart : start < n) :
    finiteInputVariableQueryOrder n (List.range' start (count + 1)) =
      ⟨start, hstart⟩ ::
        finiteInputVariableQueryOrder n (List.range' (start + 1) count) := by
  simp [finiteInputVariableQueryOrder, finiteInputPosition?, hstart,
    List.range'_succ]

/-- An interval beginning at or beyond the finite endpoint contains no finite
input coordinate. -/
theorem finiteInputVariableQueryOrder_range'_eq_nil_of_le
    {n start count : Nat} (hstart : n <= start) :
    finiteInputVariableQueryOrder n (List.range' start count) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro coordinate hcoordinate
  rw [finiteInputVariableQueryOrder, List.mem_filterMap] at hcoordinate
  rcases hcoordinate with ⟨position, hposition, hcast⟩
  have hval : position = coordinate.val :=
    finiteInputPosition?_eq_some_iff.mp hcast
  have hrange : start <= position ∧ position < start + count := by
    simpa using hposition
  omega

/-- Split a nonempty half-open interval at its first finite coordinate. -/
theorem finiteInputVariableQueryOrder_interval_cons
    {n start stop : Nat} (hstart : start < n) (hlt : start < stop) :
    finiteInputVariableQueryOrder n
        (List.range' start (stop - start)) =
      ⟨start, hstart⟩ ::
        finiteInputVariableQueryOrder n
          (List.range' (start + 1) (stop - (start + 1))) := by
  have hcount : stop - start = (stop - (start + 1)) + 1 := by omega
  rw [hcount]
  exact finiteInputVariableQueryOrder_range'_succ_of_lt hstart

/-- On a nonhalting cached local state, the structural fresh-query predicate
is exactly the right-moving input instruction. -/
theorem cachedInputTransition_inputMove_right_iff_needsUnread
    (machine : DeterministicMachine) {H w : Nat}
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (hnonhalting : (cachedInputMachine machine).halt live.control = none) :
    (cachedInputTransition machine live.control unread
        (live.workSlab live.relativeWorkHead)).inputMove = .right ↔
      cachedLocalStepNeedsUnread machine live = true := by
  rw [cachedLocalStepNeedsUnread, hnonhalting]
  cases hcontrol : live.control with
  | none => simp [cachedInputTransition]
  | some fields =>
      rcases fields with ⟨state, cached⟩
      cases hmove : (machine.transition state cached
          (live.workSlab live.relativeWorkHead)).inputMove <;>
        simp [cachedInputTransition, hmove]

/-- A successful nonfinal local step advances the bounded input head exactly
when it requests a fresh symbol. -/
theorem finiteLocalCachedStep_inside_inputHead_eq
    (machine : DeterministicMachine) {H w base : Nat}
    (unread : ReadOnlySymbol)
    (live next : LocalReplayState
      (cachedInputMachine machine).State H w)
    (hstep : finiteLocalCachedStep machine H w base unread live =
      .inside next) :
    next.inputHead.val =
      if cachedLocalStepNeedsUnread machine live then
        live.inputHead.val + 1
      else live.inputHead.val := by
  have hnonhalting :
      (cachedInputMachine machine).halt live.control = none := by
    cases hhalt : (cachedInputMachine machine).halt live.control with
    | none => rfl
    | some outcome =>
        simp [finiteLocalCachedStep, hhalt] at hstep
  have hmove := cachedInputTransition_inputMove_right_iff_needsUnread
    machine live unread hnonhalting
  unfold finiteLocalCachedStep at hstep
  rw [hnonhalting] at hstep
  dsimp only at hstep
  split at hstep
  · split at hstep
    · cases hstep
      change moveInputHead live.inputHead.val
          (cachedInputTransition machine live.control unread
            (live.workSlab live.relativeWorkHead)).inputMove = _
      by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
      · have hright := hmove.mpr hneeds
        simp [hneeds, hright, moveInputHead]
      · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
          cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
        have hnotRight :
            (cachedInputTransition machine live.control unread
              (live.workSlab live.relativeWorkHead)).inputMove ≠ .right := by
          intro hright
          exact hneeds (hmove.mp hright)
        cases hinputMove : (cachedInputTransition machine live.control unread
            (live.workSlab live.relativeWorkHead)).inputMove with
        | stay => simp [hneedsFalse, moveInputHead]
        | right => exact (hnotRight hinputMove).elim
    · contradiction
  · contradiction

/-- A successful final local step has the same exact input-head behavior. -/
theorem finiteLocalCachedFinalStep_stepped_inputHead_eq
    (machine : DeterministicMachine) {H w base : Nat}
    (unread : ReadOnlySymbol)
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (hstep : finiteLocalCachedFinalStep machine H w base unread live =
      .stepped final) :
    final.inputHead.val =
      if cachedLocalStepNeedsUnread machine live then
        live.inputHead.val + 1
      else live.inputHead.val := by
  have hnonhalting :
      (cachedInputMachine machine).halt live.control = none := by
    cases hhalt : (cachedInputMachine machine).halt live.control with
    | none => rfl
    | some outcome =>
        simp [finiteLocalCachedFinalStep, hhalt] at hstep
  have hendpoint :=
    (finiteLocalCachedFinalStep_stepped_endpoint
      machine unread live final hstep).2.1
  have hmove := cachedInputTransition_inputMove_right_iff_needsUnread
    machine live unread hnonhalting
  rw [hendpoint]
  by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
  · have hright := hmove.mpr hneeds
    simp [hneeds, hright, moveInputHead]
  · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
      cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
    have hnotRight :
        (cachedInputTransition machine live.control unread
          (live.workSlab live.relativeWorkHead)).inputMove ≠ .right := by
      intro hright
      exact hneeds (hmove.mp hright)
    cases hinputMove : (cachedInputTransition machine live.control unread
        (live.workSlab live.relativeWorkHead)).inputMove with
    | stay => simp [hneedsFalse, moveInputHead]
    | right => exact (hnotRight hinputMove).elim

/-- A successful nonfinal phase advance has the exact requested/stay
input-head update, including halted stuttering. -/
theorem advanceFiniteCachedVisitPhase_running_inputHead_eq
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w <= H + 1)
    (remaining nextRemaining : Fin (H + 1))
    (live next : LocalReplayState
      (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (hzero : remaining.val ≠ 0) (hlast : remaining.val ≠ 1)
    (hadvance : advanceFiniteCachedVisitPhase machine H w base hbound
      remaining live unread = .running nextRemaining next) :
    next.inputHead.val =
      if cachedLocalStepNeedsUnread machine live then
        live.inputHead.val + 1
      else live.inputHead.val := by
  unfold advanceFiniteCachedVisitPhase at hadvance
  rw [dif_neg hzero, dif_neg hlast] at hadvance
  cases hstep : finiteLocalCachedStep machine H w base unread live with
  | inside stepped =>
      rw [hstep] at hadvance
      have hhead := finiteLocalCachedStep_inside_inputHead_eq
        machine unread live stepped hstep
      cases hadvance
      exact hhead
  | halted outcome =>
      rw [hstep] at hadvance
      cases hadvance
      have hhalt :=
        (finiteLocalCachedStep_eq_halted_iff
          machine unread live outcome).mp hstep
      have hneeds : cachedLocalStepNeedsUnread machine live = false := by
        simp [cachedLocalStepNeedsUnread, hhalt]
      simp [hneeds]
  | workHeadExit =>
      rw [hstep] at hadvance
      contradiction
  | inputHorizonExceeded =>
      rw [hstep] at hadvance
      contradiction

/-- A completed last phase advance has the same exact input-head update. -/
theorem advanceFiniteCachedVisitPhase_completed_inputHead_eq
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w <= H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (hlast : remaining.val = 1)
    (hadvance : advanceFiniteCachedVisitPhase machine H w base hbound
      remaining live unread = .completed final) :
    final.inputHead.val =
      if cachedLocalStepNeedsUnread machine live then
        live.inputHead.val + 1
      else live.inputHead.val := by
  have hzero : remaining.val ≠ 0 := by omega
  unfold advanceFiniteCachedVisitPhase at hadvance
  rw [dif_neg hzero, dif_pos hlast] at hadvance
  cases hstep : finiteLocalCachedFinalStep machine H w base unread live with
  | stepped stepped =>
      rw [hstep] at hadvance
      have hhead := finiteLocalCachedFinalStep_stepped_inputHead_eq
        machine unread live stepped hstep
      cases hadvance
      exact hhead
  | halted outcome =>
      rw [hstep] at hadvance
      cases hadvance
      have hhalt :=
        (finiteLocalCachedFinalStep_eq_halted_iff
          machine unread live outcome).mp hstep
      have hneeds : cachedLocalStepNeedsUnread machine live = false := by
        simp [cachedLocalStepNeedsUnread, hhalt]
      simp [finiteLocalFinalStateOfReplayState, hneeds]
  | inputHorizonExceeded =>
      rw [hstep] at hadvance
      contradiction
  | workHorizonExceeded =>
      rw [hstep] at hadvance
      contradiction

/-- Canonical Boolean answers queried between two finite input-head
positions. -/
def finiteCachedVisitFreshAnswers
    (input : List Bool) (start stop : Nat) : List Bool :=
  (finiteInputVariableQueryOrder input.length
    (List.range' start (stop - start))).map (fun position => input.get position)

/-- A completed comparison trace is an exact streaming trace whose external
answers are precisely the in-range coordinates of its half-open input-head
interval. -/
theorem finiteCachedVisitCompleted_exactFreshTrace
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {H w base : Nat}
    (hbound : base + w <= H + 1)
    (initialRemaining : Fin (H + 1))
    (initialLive : LocalReplayState
      (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    (unreads : List ReadOnlySymbol)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (hlength : initialRemaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input H w base
      unreads initialLive)
    (hcompleted :
      runFiniteCachedVisitStreamingWithUnreads machine input.length H w base
        hbound unreads (.running initialRemaining initialLive) =
          .completed final) :
    let verifier := finiteCachedVisitStreamingVerifier machine input.length
      H w base hbound initialRemaining initialLive expected
    FiniteStreamingVerifier.ExactFreshTrace verifier (fun bit => .bit bit)
      unreads.length (.running initialRemaining initialLive)
      (finiteCachedVisitFreshAnswers input initialLive.inputHead.val
        final.inputHead.val)
      (.completed final) := by
  let verifier := finiteCachedVisitStreamingVerifier machine input.length
    H w base hbound initialRemaining initialLive expected
  change FiniteStreamingVerifier.ExactFreshTrace verifier
    (fun bit => .bit bit) unreads.length
    (.running initialRemaining initialLive)
    (finiteCachedVisitFreshAnswers input initialLive.inputHead.val
      final.inputHead.val)
    (.completed final)
  have go : ∀ (trace : List ReadOnlySymbol)
      (remaining : Fin (H + 1))
      (live : LocalReplayState (cachedInputMachine machine).State H w)
      (target : FiniteLocalFinalState
        (cachedInputMachine machine).State H w),
      remaining.val = trace.length ->
      FiniteCachedVisitSymbolsAgree machine input H w base trace live ->
      runFiniteCachedVisitStreamingWithUnreads machine input.length H w base
          hbound trace (.running remaining live) = .completed target ->
      live.inputHead.val <= target.inputHead.val ∧
        FiniteStreamingVerifier.ExactFreshTrace verifier
          (fun bit => .bit bit) trace.length (.running remaining live)
          (finiteCachedVisitFreshAnswers input live.inputHead.val
            target.inputHead.val)
          (.completed target) := by
    intro trace
    induction trace with
    | nil =>
        intro remaining live target hlength hagree hrun
        simp [runFiniteCachedVisitStreamingWithUnreads] at hrun
    | cons unread rest ih =>
        intro remaining live target hlength hagree hrun
        have hpositive : 0 < remaining.val := by
          rw [hlength]
          simp
        have hphaseNotHalted :
            verifier.halted (.running remaining live) = false := by
          change finiteCachedVisitPhaseHalted (.running remaining live) = false
          simp [finiteCachedVisitPhaseHalted, Nat.ne_of_gt hpositive]
        cases rest with
        | nil =>
            have hread : readOnlySymbol input live.inputHead.val = unread := by
              simpa [FiniteCachedVisitSymbolsAgree] using hagree
            have hend : cachedLocalStepNeedsUnread machine live = true ->
                ¬ live.inputHead.val < input.length -> unread = .rightEnd := by
              intro _ hhead
              calc
                unread = readOnlySymbol input live.inputHead.val := hread.symm
                _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le
                  input live.inputHead.val (Nat.le_of_not_gt hhead)
            have hstreamStep := finiteCachedVisitStreamingStep_answerForUnread
              machine input.length hbound remaining live unread hend
            have hlast : remaining.val = 1 := by simpa using hlength
            have hadvance : advanceFiniteCachedVisitPhase machine H w base
                hbound remaining live unread = .completed target := by
              rw [runFiniteCachedVisitStreamingWithUnreads_cons] at hrun
              simp only [streamingAnswerForPhaseUnread] at hrun
              rw [hstreamStep] at hrun
              simpa [runFiniteCachedVisitStreamingWithUnreads] using hrun
            have htargetHead :=
              advanceFiniteCachedVisitPhase_completed_inputHead_eq
                machine hbound remaining live unread target hlast hadvance
            by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
            · by_cases hhead : live.inputHead.val < input.length
              · let position : Fin input.length := ⟨live.inputHead.val, hhead⟩
                have hsymbol : unread = .bit (input.get position) := by
                  calc
                    unread = readOnlySymbol input live.inputHead.val := hread.symm
                    _ = .bit (input.get position) := by
                      exact readOnlySymbol_eq_bit_get input position
                have hrequest : verifier.requestsInput
                    (.running remaining live) = true := by
                  change finiteCachedVisitPhaseRequestsInput machine
                    input.length (.running remaining live) = true
                  simp [finiteCachedVisitPhaseRequestsInput, hpositive,
                    hneeds, hhead]
                have hanswer : streamingAnswerForUnread machine input.length
                    live unread = some (.bit (input.get position)) := by
                  simp [streamingAnswerForUnread, hneeds, hhead, hsymbol]
                have hqueryStep : verifier.step (.running remaining live)
                      (some (.bit (input.get position))) = .completed target := by
                  change finiteCachedVisitStreamingStep machine input.length
                    H w base hbound (.running remaining live)
                      (some (.bit (input.get position))) = .completed target
                  rw [← hanswer, hstreamStep, hadvance]
                have htrace : FiniteStreamingVerifier.ExactFreshTrace verifier
                    (fun bit => .bit bit) 1 (.running remaining live)
                    [input.get position] (.completed target) := by
                  apply FiniteStreamingVerifier.ExactFreshTrace.query
                    hphaseNotHalted hrequest
                  rw [hqueryStep]
                  exact FiniteStreamingVerifier.ExactFreshTrace.halted _ rfl
                have hheadEq : target.inputHead.val = live.inputHead.val + 1 := by
                  simpa [hneeds] using htargetHead
                constructor
                · omega
                · simpa [finiteCachedVisitFreshAnswers, hheadEq,
                    finiteInputVariableQueryOrder, finiteInputPosition?,
                    hhead, position] using htrace
              · have hheadGe : input.length <= live.inputHead.val :=
                  Nat.le_of_not_gt hhead
                have hrequest : verifier.requestsInput
                    (.running remaining live) = false := by
                  change finiteCachedVisitPhaseRequestsInput machine
                    input.length (.running remaining live) = false
                  simp [finiteCachedVisitPhaseRequestsInput, hpositive,
                    hneeds, hhead]
                have hanswer : streamingAnswerForUnread machine input.length
                    live unread = none := by
                  simp [streamingAnswerForUnread, hneeds, hhead]
                have hsilentStep : verifier.step (.running remaining live) none =
                    .completed target := by
                  change finiteCachedVisitStreamingStep machine input.length
                    H w base hbound (.running remaining live) none =
                      .completed target
                  rw [← hanswer, hstreamStep, hadvance]
                have htrace : FiniteStreamingVerifier.ExactFreshTrace verifier
                    (fun bit => .bit bit) 1 (.running remaining live)
                    [] (.completed target) := by
                  apply FiniteStreamingVerifier.ExactFreshTrace.silent
                    hphaseNotHalted hrequest
                  rw [hsilentStep]
                  exact FiniteStreamingVerifier.ExactFreshTrace.halted _ rfl
                have hheadEq : target.inputHead.val = live.inputHead.val + 1 := by
                  simpa [hneeds] using htargetHead
                have hempty := finiteInputVariableQueryOrder_range'_eq_nil_of_le
                  (n := input.length) (start := live.inputHead.val)
                  (count := target.inputHead.val - live.inputHead.val) hheadGe
                constructor
                · omega
                · simpa [finiteCachedVisitFreshAnswers, hempty] using htrace
            · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
                cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
              have hrequest : verifier.requestsInput
                  (.running remaining live) = false := by
                change finiteCachedVisitPhaseRequestsInput machine
                  input.length (.running remaining live) = false
                simp [finiteCachedVisitPhaseRequestsInput, hpositive,
                  hneedsFalse]
              have hanswer : streamingAnswerForUnread machine input.length
                  live unread = none := by
                simp [streamingAnswerForUnread, hneedsFalse]
              have hsilentStep : verifier.step (.running remaining live) none =
                  .completed target := by
                change finiteCachedVisitStreamingStep machine input.length
                  H w base hbound (.running remaining live) none =
                    .completed target
                rw [← hanswer, hstreamStep, hadvance]
              have htrace : FiniteStreamingVerifier.ExactFreshTrace verifier
                  (fun bit => .bit bit) 1 (.running remaining live)
                  [] (.completed target) := by
                apply FiniteStreamingVerifier.ExactFreshTrace.silent
                  hphaseNotHalted hrequest
                rw [hsilentStep]
                exact FiniteStreamingVerifier.ExactFreshTrace.halted _ rfl
              have hheadEq : target.inputHead.val = live.inputHead.val := by
                simpa [hneedsFalse] using htargetHead
              constructor
              · omega
              · simpa [finiteCachedVisitFreshAnswers, hheadEq] using htrace
        | cons nextUnread tail =>
            rw [finiteCachedVisitSymbolsAgree_cons_cons] at hagree
            rcases hagree with ⟨hread, htailAgree⟩
            have hend : cachedLocalStepNeedsUnread machine live = true ->
                ¬ live.inputHead.val < input.length -> unread = .rightEnd := by
              intro _ hhead
              calc
                unread = readOnlySymbol input live.inputHead.val := hread.symm
                _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le
                  input live.inputHead.val (Nat.le_of_not_gt hhead)
            have hstreamStep := finiteCachedVisitStreamingStep_answerForUnread
              machine input.length hbound remaining live unread hend
            have hzero : remaining.val ≠ 0 := by
              have : 2 <= (unread :: nextUnread :: tail).length := by simp
              omega
            have hlast : remaining.val ≠ 1 := by
              have : 2 <= (unread :: nextUnread :: tail).length := by simp
              omega
            rw [runFiniteCachedVisitStreamingWithUnreads_cons] at hrun
            simp only [streamingAnswerForPhaseUnread] at hrun
            rw [hstreamStep] at hrun
            cases hlocal : finiteLocalCachedStep machine H w base unread live with
            | inside next =>
                have htailAgree' : FiniteCachedVisitSymbolsAgree machine input
                    H w base (nextUnread :: tail) next := by
                  simpa [hlocal] using htailAgree
                have hadvance : advanceFiniteCachedVisitPhase machine H w base
                    hbound remaining live unread =
                      .running (spendVisitStep remaining) next := by
                  unfold advanceFiniteCachedVisitPhase
                  rw [dif_neg hzero, dif_neg hlast, hlocal]
                have htailRun :
                    runFiniteCachedVisitStreamingWithUnreads machine input.length
                        H w base hbound (nextUnread :: tail)
                        (.running (spendVisitStep remaining) next) =
                      .completed target := by
                  simpa [hadvance] using hrun
                have htailLength : (spendVisitStep remaining).val =
                    (nextUnread :: tail).length := by
                  simp only [spendVisitStep]
                  rw [hlength]
                  simp
                obtain ⟨htailMono, htailTrace⟩ :=
                  ih (spendVisitStep remaining) next target htailLength
                    htailAgree' htailRun
                have hnextHead := finiteLocalCachedStep_inside_inputHead_eq
                  machine unread live next hlocal
                by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
                · by_cases hhead : live.inputHead.val < input.length
                  · let position : Fin input.length := ⟨live.inputHead.val, hhead⟩
                    have hsymbol : unread = .bit (input.get position) := by
                      calc
                        unread = readOnlySymbol input live.inputHead.val := hread.symm
                        _ = .bit (input.get position) := by
                          exact readOnlySymbol_eq_bit_get input position
                    have hrequest : verifier.requestsInput
                        (.running remaining live) = true := by
                      change finiteCachedVisitPhaseRequestsInput machine
                        input.length (.running remaining live) = true
                      simp [finiteCachedVisitPhaseRequestsInput, hpositive,
                        hneeds, hhead]
                    have hanswer : streamingAnswerForUnread machine input.length
                        live unread = some (.bit (input.get position)) := by
                      simp [streamingAnswerForUnread, hneeds, hhead, hsymbol]
                    have hqueryStep : verifier.step (.running remaining live)
                          (some (.bit (input.get position))) =
                        .running (spendVisitStep remaining) next := by
                      change finiteCachedVisitStreamingStep machine input.length
                        H w base hbound (.running remaining live)
                          (some (.bit (input.get position))) = _
                      rw [← hanswer, hstreamStep, hadvance]
                    have hheadEq : next.inputHead.val = live.inputHead.val + 1 := by
                      simpa [hneeds] using hnextHead
                    have hlt : live.inputHead.val < target.inputHead.val := by
                      omega
                    have htrace : FiniteStreamingVerifier.ExactFreshTrace
                        verifier (fun bit => .bit bit)
                        ((nextUnread :: tail).length + 1)
                        (.running remaining live)
                        (input.get position :: finiteCachedVisitFreshAnswers input
                          next.inputHead.val target.inputHead.val)
                        (.completed target) := by
                      apply FiniteStreamingVerifier.ExactFreshTrace.query
                        hphaseNotHalted hrequest
                      rw [hqueryStep]
                      exact htailTrace
                    constructor
                    · omega
                    · rw [finiteCachedVisitFreshAnswers,
                        finiteInputVariableQueryOrder_interval_cons hhead hlt,
                        List.map_cons]
                      simpa [finiteCachedVisitFreshAnswers, hheadEq, position]
                        using htrace
                  · have hheadGe : input.length <= live.inputHead.val :=
                      Nat.le_of_not_gt hhead
                    have hrequest : verifier.requestsInput
                        (.running remaining live) = false := by
                      change finiteCachedVisitPhaseRequestsInput machine
                        input.length (.running remaining live) = false
                      simp [finiteCachedVisitPhaseRequestsInput, hpositive,
                        hneeds, hhead]
                    have hanswer : streamingAnswerForUnread machine input.length
                        live unread = none := by
                      simp [streamingAnswerForUnread, hneeds, hhead]
                    have hsilentStep : verifier.step (.running remaining live)
                          none = .running (spendVisitStep remaining) next := by
                      change finiteCachedVisitStreamingStep machine input.length
                        H w base hbound (.running remaining live) none = _
                      rw [← hanswer, hstreamStep, hadvance]
                    have hheadEq : next.inputHead.val = live.inputHead.val + 1 := by
                      simpa [hneeds] using hnextHead
                    have hemptyCurrent :=
                      finiteInputVariableQueryOrder_range'_eq_nil_of_le
                        (n := input.length) (start := live.inputHead.val)
                        (count := target.inputHead.val - live.inputHead.val)
                        hheadGe
                    have hnextGe : input.length <= next.inputHead.val := by omega
                    have hemptyNext :=
                      finiteInputVariableQueryOrder_range'_eq_nil_of_le
                        (n := input.length) (start := next.inputHead.val)
                        (count := target.inputHead.val - next.inputHead.val)
                        hnextGe
                    have htrace : FiniteStreamingVerifier.ExactFreshTrace
                        verifier (fun bit => .bit bit)
                        ((nextUnread :: tail).length + 1)
                        (.running remaining live) [] (.completed target) := by
                      apply FiniteStreamingVerifier.ExactFreshTrace.silent
                        hphaseNotHalted hrequest
                      rw [hsilentStep]
                      simpa [finiteCachedVisitFreshAnswers, hemptyNext]
                        using htailTrace
                    constructor
                    · omega
                    · simpa [finiteCachedVisitFreshAnswers, hemptyCurrent]
                        using htrace
                · have hneedsFalse : cachedLocalStepNeedsUnread machine live =
                      false := by
                    cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
                  have hrequest : verifier.requestsInput
                      (.running remaining live) = false := by
                    change finiteCachedVisitPhaseRequestsInput machine
                      input.length (.running remaining live) = false
                    simp [finiteCachedVisitPhaseRequestsInput, hpositive,
                      hneedsFalse]
                  have hanswer : streamingAnswerForUnread machine input.length
                      live unread = none := by
                    simp [streamingAnswerForUnread, hneedsFalse]
                  have hsilentStep : verifier.step (.running remaining live)
                        none = .running (spendVisitStep remaining) next := by
                    change finiteCachedVisitStreamingStep machine input.length
                      H w base hbound (.running remaining live) none = _
                    rw [← hanswer, hstreamStep, hadvance]
                  have hheadEq : next.inputHead.val = live.inputHead.val := by
                    simpa [hneedsFalse] using hnextHead
                  have htrace : FiniteStreamingVerifier.ExactFreshTrace verifier
                      (fun bit => .bit bit) ((nextUnread :: tail).length + 1)
                      (.running remaining live)
                      (finiteCachedVisitFreshAnswers input live.inputHead.val
                        target.inputHead.val)
                      (.completed target) := by
                    apply FiniteStreamingVerifier.ExactFreshTrace.silent
                      hphaseNotHalted hrequest
                    rw [hsilentStep]
                    simpa [hheadEq] using htailTrace
                  constructor
                  · omega
                  · simpa using htrace
            | halted outcome =>
                have htailAgree' : FiniteCachedVisitSymbolsAgree machine input
                    H w base (nextUnread :: tail) live := by
                  simpa [hlocal] using htailAgree
                have hadvance : advanceFiniteCachedVisitPhase machine H w base
                    hbound remaining live unread =
                      .running (spendVisitStep remaining) live := by
                  unfold advanceFiniteCachedVisitPhase
                  rw [dif_neg hzero, dif_neg hlast, hlocal]
                have htailRun :
                    runFiniteCachedVisitStreamingWithUnreads machine input.length
                        H w base hbound (nextUnread :: tail)
                        (.running (spendVisitStep remaining) live) =
                      .completed target := by
                  simpa [hadvance] using hrun
                have htailLength : (spendVisitStep remaining).val =
                    (nextUnread :: tail).length := by
                  simp only [spendVisitStep]
                  rw [hlength]
                  simp
                obtain ⟨htailMono, htailTrace⟩ :=
                  ih (spendVisitStep remaining) live target htailLength
                    htailAgree' htailRun
                have hhalt := (finiteLocalCachedStep_eq_halted_iff
                  machine unread live outcome).mp hlocal
                have hneedsFalse : cachedLocalStepNeedsUnread machine live =
                    false := by simp [cachedLocalStepNeedsUnread, hhalt]
                have hrequest : verifier.requestsInput
                    (.running remaining live) = false := by
                  change finiteCachedVisitPhaseRequestsInput machine
                    input.length (.running remaining live) = false
                  simp [finiteCachedVisitPhaseRequestsInput, hpositive,
                    hneedsFalse]
                have hanswer : streamingAnswerForUnread machine input.length
                    live unread = none := by
                  simp [streamingAnswerForUnread, hneedsFalse]
                have hsilentStep : verifier.step (.running remaining live) none =
                    .running (spendVisitStep remaining) live := by
                  change finiteCachedVisitStreamingStep machine input.length
                    H w base hbound (.running remaining live) none = _
                  rw [← hanswer, hstreamStep, hadvance]
                constructor
                · exact htailMono
                · apply FiniteStreamingVerifier.ExactFreshTrace.silent
                    hphaseNotHalted hrequest
                  rw [hsilentStep]
                  exact htailTrace
            | workHeadExit =>
                simp [hlocal] at htailAgree
            | inputHorizonExceeded =>
                simp [hlocal] at htailAgree
  exact (go unreads initialRemaining initialLive final hlength hagree
    hcompleted).2

/-- Semantic validity closes the canonical chronological fresh prefix against
the finite comparison run.  Input monotonicity is derived internally from the
completed trace; it is not an additional premise. -/
theorem fixedVisitFreshPrefixClosesToComparison_of_valid
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
    (hvalid : FixedAlphaBlockVisitValid (cachedInputMachine machine) input
      alpha block visit carried) :
    FixedVisitFreshPrefixClosesToComparison machine input alpha block visit
      carried hentry (fun position => input.get position) := by
  obtain ⟨otherEntry, final, hagree, hrun,
      _hstate, hinput, _hwork⟩ :=
    (finiteCachedFixedAlphaVisitStreamingCertificate_iff
      machine input alpha block visit carried).mpr hvalid
  have hentryEq : otherEntry = hentry := Subsingleton.elim _ _
  subst otherEntry
  let initial := finiteCachedStateOfVisitEntry machine alpha block visit
    carried hentry
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block visit carried hentry
  have hlength : (fixedAlphaVisitRemaining visit).val = unreads.length := by
    simp [unreads, fixedAlphaVisitRemaining]
  have htrace : FiniteStreamingVerifier.ExactFreshTrace verifier
      (fun bit => .bit bit) unreads.length
      (.running (fixedAlphaVisitRemaining visit) initial)
      (finiteCachedVisitFreshAnswers input initial.inputHead.val
        final.inputHead.val)
      (.completed final) := by
    exact finiteCachedVisitCompleted_exactFreshTrace machine input
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      (fixedAlphaVisitRemaining visit) initial visit.exit unreads final
      hlength hagree hrun
  have hsteps : unreads.length <= T := by
    have hremaining := (fixedAlphaVisitRemaining visit).isLt
    rw [← hlength]
    omega
  have hclosed :=
    FiniteStreamingVerifier.ExactFreshTrace.closeAfterAnswers
      verifier (fun bit => .bit bit) htrace
      (⟨T, Nat.lt_succ_self T⟩ : Fin (T + 1)) hsteps
  have hanswers :
      finiteCachedVisitFreshAnswers input initial.inputHead.val
          final.inputHead.val =
        (fixedVisitFiniteFreshOrder input.length visit).map
          (fun position => input.get position) := by
    unfold finiteCachedVisitFreshAnswers fixedVisitFiniteFreshOrder
      fixedVisitNaturalFreshOrder
    change
      (finiteInputVariableQueryOrder input.length
          (List.range' visit.entry.inputHead.val
            (final.inputHead.val - visit.entry.inputHead.val))).map
          (fun position => input.get position) = _
    rw [← hinput]
  unfold FixedVisitFreshPrefixClosesToComparison
  change
    (verifier.silentClosure
      (((fixedVisitFiniteFreshOrder input.length visit).map
          (fun position => input.get position)).foldl
        (verifier.consumeQuery (fun bit => .bit bit))
        (verifier.initialFueledState T))).1 = _
  rw [hrun]
  rw [← hanswers]
  simpa [verifier, initial,
    finiteCachedFixedAlphaVisitStreamingVerifier,
    finiteCachedVisitStreamingVerifier,
    FiniteStreamingVerifier.initialFueledState] using hclosed

/-- The canonical read-once fixed-order program accepts every semantically
valid cached visit; no residual prefix-realization premise remains. -/
theorem compileFixedVisitFiniteQueryOrder_eval_eq_true_of_valid
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
    (hvalid : FixedAlphaBlockVisitValid (cachedInputMachine machine) input
      alpha block visit carried) :
    (compileFiniteCachedFixedAlphaVisit machine alpha block visit carried
      hentry (fixedVisitFiniteQueryOrder input.length visit)
      (fixedVisitFiniteQueryOrder_length input.length visit)).eval
        (fun position => input.get position) = true := by
  exact compileFixedVisitFiniteQueryOrder_eval_eq_true_of_valid_of_prefix_closes
    machine input alpha block visit carried hentry hvalid
      (fixedVisitFreshPrefixClosesToComparison_of_valid machine input alpha
        block visit carried hentry hvalid)

end OneTapeMagnification
end Frontier
end Pnp4
