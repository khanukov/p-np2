import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdaptiveSilentStepQueryCollapse
import Pnp4.Frontier.OneTapeMagnification.FixedVisitFreshPrefixSync

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Read-once adaptive compilation for one cached visit

The cached input machine moves its physical input head only when it consumes
a fresh symbol.  This file turns that local fact into a state invariant for
the executable adaptive compiler: silent closure never lowers the head rank,
and every real query raises it strictly.  Consequently each execution's
adaptive query trace is strictly increasing, hence duplicate-free.
-/

/-- Input-head rank of a finite cached phase.  Rejection is assigned the
strict upper bound `H + 1`; completed states retain their actual final head. -/
def finiteCachedVisitPhaseInputRank
    {State : Type} {H w : Nat} :
    FiniteCachedVisitStreamingState State H w → Nat
  | .running _ live => live.inputHead.val
  | .completed final => final.inputHead.val
  | .rejected _ => H + 1

/-- Resolving one cached visit transition never lowers its input-head rank. -/
theorem advanceFiniteCachedVisitPhase_inputRank_mono
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol) :
    live.inputHead.val ≤
      finiteCachedVisitPhaseInputRank
        (advanceFiniteCachedVisitPhase machine H w base hbound
          remaining live unread) := by
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
      simp only [finiteCachedVisitPhaseInputRank]
      by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
      · simp [hneeds] at hhead
        omega
      · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
          cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
        simp [hneedsFalse] at hhead
        omega
  | completed final =>
      have hlast : remaining.val = 1 := by
        by_contra hlast
        by_cases hzero : remaining.val = 0
        · simp [advanceFiniteCachedVisitPhase, hzero] at hadvance
        · simp [advanceFiniteCachedVisitPhase, hzero, hlast] at hadvance
          split at hadvance <;> contradiction
      have hhead := advanceFiniteCachedVisitPhase_completed_inputHead_eq
        machine hbound remaining live unread final hlast hadvance
      simp only [finiteCachedVisitPhaseInputRank]
      by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
      · simp [hneeds] at hhead
        omega
      · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
          cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
        simp [hneedsFalse] at hhead
        omega
  | rejected failure =>
      simp only [finiteCachedVisitPhaseInputRank]
      exact Nat.le_of_lt live.inputHead.isLt

/-- A resolved transition that genuinely needs the unread symbol raises the
input-head rank strictly, including transitions that finish or reject. -/
theorem advanceFiniteCachedVisitPhase_inputRank_lt_of_needsUnread
    (machine : DeterministicMachine) {H w base : Nat}
    (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (hneeds : cachedLocalStepNeedsUnread machine live = true) :
    live.inputHead.val <
      finiteCachedVisitPhaseInputRank
        (advanceFiniteCachedVisitPhase machine H w base hbound
          remaining live unread) := by
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
      simp only [finiteCachedVisitPhaseInputRank]
      simp [hneeds] at hhead
      omega
  | completed final =>
      have hlast : remaining.val = 1 := by
        by_contra hlast
        by_cases hzero : remaining.val = 0
        · simp [advanceFiniteCachedVisitPhase, hzero] at hadvance
        · simp [advanceFiniteCachedVisitPhase, hzero, hlast] at hadvance
          split at hadvance <;> contradiction
      have hhead := advanceFiniteCachedVisitPhase_completed_inputHead_eq
        machine hbound remaining live unread final hlast hadvance
      simp only [finiteCachedVisitPhaseInputRank]
      simp [hneeds] at hhead
      omega
  | rejected failure =>
      simp only [finiteCachedVisitPhaseInputRank]
      exact live.inputHead.isLt

/-- Every streaming microstep is nondecreasing for the phase input rank,
regardless of whether its optional symbol is expected. -/
theorem finiteCachedVisitStreamingStep_inputRank_mono
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w)
    (supplied : Option ReadOnlySymbol) :
    finiteCachedVisitPhaseInputRank phase ≤
      finiteCachedVisitPhaseInputRank
        (finiteCachedVisitStreamingStep machine n H w base hbound
          phase supplied) := by
  cases phase with
  | completed final =>
      simp [finiteCachedVisitStreamingStep,
        finiteCachedVisitPhaseInputRank]
  | rejected failure =>
      simp [finiteCachedVisitStreamingStep,
        finiteCachedVisitPhaseInputRank]
  | running remaining live =>
      change live.inputHead.val ≤ finiteCachedVisitPhaseInputRank _
      by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
      · by_cases hhead : live.inputHead.val < n
        · cases supplied with
          | none =>
              simp [finiteCachedVisitStreamingStep, hneeds, hhead,
                finiteCachedVisitPhaseInputRank]
          | some unread =>
              simpa [finiteCachedVisitStreamingStep, hneeds, hhead] using
                advanceFiniteCachedVisitPhase_inputRank_mono machine hbound
                  remaining live unread
        · cases supplied with
          | none =>
              simpa [finiteCachedVisitStreamingStep, hneeds, hhead] using
                advanceFiniteCachedVisitPhase_inputRank_mono machine hbound
                  remaining live .rightEnd
          | some unread =>
              simp [finiteCachedVisitStreamingStep, hneeds, hhead,
                finiteCachedVisitPhaseInputRank]
      · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
          cases h : cachedLocalStepNeedsUnread machine live <;> simp_all
        cases supplied with
        | none =>
            simpa [finiteCachedVisitStreamingStep, hneedsFalse] using
              advanceFiniteCachedVisitPhase_inputRank_mono machine hbound
                remaining live .rightEnd
        | some unread =>
            simp [finiteCachedVisitStreamingStep, hneedsFalse,
              finiteCachedVisitPhaseInputRank]

/-- Supplying a symbol at a genuine in-range request raises the phase input
rank strictly. -/
theorem finiteCachedVisitStreamingStep_inputRank_lt_of_requestsInput
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (hrequest : finiteCachedVisitPhaseRequestsInput machine n phase = true) :
    finiteCachedVisitPhaseInputRank phase <
      finiteCachedVisitPhaseInputRank
        (finiteCachedVisitStreamingStep machine n H w base hbound
          phase (some unread)) := by
  cases phase with
  | completed final =>
      simp [finiteCachedVisitPhaseRequestsInput] at hrequest
  | rejected failure =>
      simp [finiteCachedVisitPhaseRequestsInput] at hrequest
  | running remaining live =>
      have hparts :=
        (finiteCachedVisitPhaseRequestsInput_running_eq_true_iff
          machine n remaining live).mp hrequest
      have hneeds := hparts.2.1
      have hhead := hparts.2.2
      simpa [finiteCachedVisitPhaseInputRank,
        finiteCachedVisitStreamingStep, hneeds, hhead] using
          advanceFiniteCachedVisitPhase_inputRank_lt_of_needsUnread
            machine hbound remaining live unread hneeds

namespace FiniteStreamingVerifier

/-- Any rank preserved by individual verifier steps is preserved by the
entire executable silent closure. -/
theorem silentClosureCore_rank_mono
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol)
    (rank : verifier.State → Nat)
    (hstep : ∀ state, rank state ≤ rank (verifier.step state none))
    (fuel : Nat) (state : verifier.State) :
    rank state ≤ rank (verifier.silentClosureCore fuel state).1 := by
  induction fuel generalizing state with
  | zero =>
      simp [silentClosureCore]
  | succ fuel ih =>
      simp only [silentClosureCore]
      split
      · exact le_rfl
      · exact (hstep state).trans (ih (verifier.step state none))

/-- Fixed-horizon form of `silentClosureCore_rank_mono`. -/
theorem silentClosure_rank_mono
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol)
    (rank : verifier.State → Nat)
    (hstep : ∀ state, rank state ≤ rank (verifier.step state none))
    {K : Nat} (state : verifier.FueledState K) :
    rank state.1 ≤ rank (verifier.silentClosure state).1 := by
  change rank state.1 ≤
    rank (verifier.silentClosureCore state.2.val state.1).1
  exact verifier.silentClosureCore_rank_mono rank hstep state.2.val state.1

end FiniteStreamingVerifier

/-- Silent closure of any finite cached-visit verifier never lowers the
input-head rank. -/
theorem finiteCachedVisitStreamingVerifier_silentClosure_inputRank_mono
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n H w base : Nat) (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (start : LocalReplayState (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    {K : Nat}
    (state : (finiteCachedVisitStreamingVerifier machine n H w base hbound
      remaining start expected).FueledState K) :
    finiteCachedVisitPhaseInputRank state.1 ≤
      finiteCachedVisitPhaseInputRank
        ((finiteCachedVisitStreamingVerifier machine n H w base hbound
          remaining start expected).silentClosure state).1 := by
  let verifier := finiteCachedVisitStreamingVerifier machine n H w base
    hbound remaining start expected
  apply FiniteStreamingVerifier.silentClosure_rank_mono verifier
    finiteCachedVisitPhaseInputRank
  intro phase
  exact finiteCachedVisitStreamingStep_inputRank_mono machine n H w base
    hbound phase none

/-- One adaptive input layer of a finite cached-visit verifier never lowers
the input-head rank. -/
theorem finiteCachedVisitAdaptiveInputStep_inputRank_mono
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n H w base : Nat) (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (start : LocalReplayState (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    {K : Nat} (input : Fin n → Bool)
    (state : (finiteCachedVisitStreamingVerifier machine n H w base hbound
      remaining start expected).FueledState K) :
    finiteCachedVisitPhaseInputRank state.1 ≤
      finiteCachedVisitPhaseInputRank
        ((finiteCachedVisitStreamingVerifier machine n H w base hbound
          remaining start expected).adaptiveInputStep (fun bit => .bit bit)
            (finiteCachedVisitAdaptiveQueryIndex? machine n) input state).1 := by
  let verifier := finiteCachedVisitStreamingVerifier machine n H w base
    hbound remaining start expected
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedVisitAdaptiveQueryIndex? (H := H) (w := w) machine n
  change finiteCachedVisitPhaseInputRank state.1 ≤
    finiteCachedVisitPhaseInputRank
      (verifier.adaptiveInputStep (fun bit => .bit bit) selector input state).1
  have hclosure : finiteCachedVisitPhaseInputRank state.1 ≤
      finiteCachedVisitPhaseInputRank (verifier.silentClosure state).1 :=
    finiteCachedVisitStreamingVerifier_silentClosure_inputRank_mono
      machine n H w base hbound remaining start expected state
  cases hquery : verifier.adaptiveQuery? selector state with
  | none =>
      calc
        finiteCachedVisitPhaseInputRank state.1 ≤
            finiteCachedVisitPhaseInputRank
              (verifier.silentClosure state).1 := hclosure
        _ = finiteCachedVisitPhaseInputRank
              (verifier.adaptiveInputStep (fun bit => .bit bit) selector
                input state).1 := by
          simp [FiniteStreamingVerifier.adaptiveInputStep,
            FiniteStreamingVerifier.adaptiveNext, hquery]
  | some index =>
      have hcharacterization :=
        (FiniteStreamingVerifier.adaptiveQuery?_eq_some_iff verifier selector
          state index).mp hquery
      have hrequest := hcharacterization.2.2.1
      have hstrict :
          finiteCachedVisitPhaseInputRank (verifier.silentClosure state).1 <
            finiteCachedVisitPhaseInputRank
              (verifier.step (verifier.silentClosure state).1
                (some (.bit (input index)))) := by
        change finiteCachedVisitPhaseRequestsInput machine n
          (verifier.silentClosure state).1 = true at hrequest
        exact finiteCachedVisitStreamingStep_inputRank_lt_of_requestsInput
          machine n H w base hbound (verifier.silentClosure state).1
            (.bit (input index)) hrequest
      have hnext :
          verifier.adaptiveInputStep (fun bit => .bit bit) selector input state =
            (verifier.step (verifier.silentClosure state).1
                (some (.bit (input index))),
              FiniteStreamingVerifier.spendOne
                (verifier.silentClosure state).2) := by
        simp [FiniteStreamingVerifier.adaptiveInputStep,
          FiniteStreamingVerifier.adaptiveNext, hquery]
      rw [hnext]
      exact hclosure.trans (Nat.le_of_lt hstrict)

/-- The coordinate of every genuine adaptive query lies strictly below the
input-head rank after that layer has consumed its answer. -/
theorem finiteCachedVisitAdaptiveInputStep_query_lt_inputRank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n H w base : Nat) (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (start : LocalReplayState (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    {K : Nat} (input : Fin n → Bool)
    (state : (finiteCachedVisitStreamingVerifier machine n H w base hbound
      remaining start expected).FueledState K)
    (index : Fin n)
    (hquery :
      (finiteCachedVisitStreamingVerifier machine n H w base hbound remaining
        start expected).adaptiveQuery?
          (finiteCachedVisitAdaptiveQueryIndex? machine n) state = some index) :
    index.val <
      finiteCachedVisitPhaseInputRank
        ((finiteCachedVisitStreamingVerifier machine n H w base hbound
          remaining start expected).adaptiveInputStep (fun bit => .bit bit)
            (finiteCachedVisitAdaptiveQueryIndex? machine n) input state).1 := by
  let verifier := finiteCachedVisitStreamingVerifier machine n H w base
    hbound remaining start expected
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedVisitAdaptiveQueryIndex? (H := H) (w := w) machine n
  change verifier.adaptiveQuery? selector state = some index at hquery
  change index.val < finiteCachedVisitPhaseInputRank
    (verifier.adaptiveInputStep (fun bit => .bit bit) selector input state).1
  have hcharacterization :=
    (FiniteStreamingVerifier.adaptiveQuery?_eq_some_iff verifier selector
      state index).mp hquery
  have hrequest := hcharacterization.2.2.1
  have hselector := hcharacterization.2.2.2
  rcases (finiteCachedVisitAdaptiveQueryIndex?_eq_some_iff machine n
      (verifier.silentClosure state).1 index).mp hselector with
    ⟨closedRemaining, live, hphase, hhead, hindex⟩
  have hstrict :
      finiteCachedVisitPhaseInputRank (verifier.silentClosure state).1 <
        finiteCachedVisitPhaseInputRank
          (verifier.step (verifier.silentClosure state).1
            (some (.bit (input index)))) := by
    change finiteCachedVisitPhaseRequestsInput machine n
      (verifier.silentClosure state).1 = true at hrequest
    exact finiteCachedVisitStreamingStep_inputRank_lt_of_requestsInput
      machine n H w base hbound (verifier.silentClosure state).1
        (.bit (input index)) hrequest
  have hnext :
      verifier.adaptiveInputStep (fun bit => .bit bit) selector input state =
        (verifier.step (verifier.silentClosure state).1
            (some (.bit (input index))),
          FiniteStreamingVerifier.spendOne
            (verifier.silentClosure state).2) := by
    simp [FiniteStreamingVerifier.adaptiveInputStep,
      FiniteStreamingVerifier.adaptiveNext, hquery]
  calc
    index.val = finiteCachedVisitPhaseInputRank
        (verifier.silentClosure state).1 := by
      simp [hphase, finiteCachedVisitPhaseInputRank, hindex]
    _ < finiteCachedVisitPhaseInputRank
        (verifier.step (verifier.silentClosure state).1
          (some (.bit (input index)))) := hstrict
    _ = finiteCachedVisitPhaseInputRank
        (verifier.adaptiveInputStep (fun bit => .bit bit) selector input
          state).1 := by rw [hnext]

/-- Before a genuine adaptive query, the current phase rank is at most its
queried coordinate.  Silent closure accounts for the possible gap. -/
theorem finiteCachedVisitAdaptiveQuery_inputRank_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n H w base : Nat) (hbound : base + w ≤ H + 1)
    (remaining : Fin (H + 1))
    (start : LocalReplayState (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    {K : Nat}
    (state : (finiteCachedVisitStreamingVerifier machine n H w base hbound
      remaining start expected).FueledState K)
    (index : Fin n)
    (hquery :
      (finiteCachedVisitStreamingVerifier machine n H w base hbound remaining
        start expected).adaptiveQuery?
          (finiteCachedVisitAdaptiveQueryIndex? machine n) state = some index) :
    finiteCachedVisitPhaseInputRank state.1 ≤ index.val := by
  let verifier := finiteCachedVisitStreamingVerifier machine n H w base
    hbound remaining start expected
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedVisitAdaptiveQueryIndex? (H := H) (w := w) machine n
  change verifier.adaptiveQuery? selector state = some index at hquery
  have hclosure : finiteCachedVisitPhaseInputRank state.1 ≤
      finiteCachedVisitPhaseInputRank (verifier.silentClosure state).1 :=
    finiteCachedVisitStreamingVerifier_silentClosure_inputRank_mono
      machine n H w base hbound remaining start expected state
  have hcharacterization :=
    (FiniteStreamingVerifier.adaptiveQuery?_eq_some_iff verifier selector
      state index).mp hquery
  have hselector := hcharacterization.2.2.2
  rcases (finiteCachedVisitAdaptiveQueryIndex?_eq_some_iff machine n
      (verifier.silentClosure state).1 index).mp hselector with
    ⟨closedRemaining, live, hphase, hhead, hindex⟩
  calc
    finiteCachedVisitPhaseInputRank state.1 ≤
        finiteCachedVisitPhaseInputRank
          (verifier.silentClosure state).1 := hclosure
    _ = index.val := by
      simp [hphase, finiteCachedVisitPhaseInputRank, hindex]

/-- Specialized adaptive-layer rank monotonicity for an advertised fixed
alpha visit. -/
theorem finiteCachedFixedAlphaVisitAdaptiveInputStep_inputRank_mono
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    (input : Fin n → Bool)
    (state : (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha
      block visit carried hentry).FueledState T) :
    finiteCachedVisitPhaseInputRank state.1 ≤
      finiteCachedVisitPhaseInputRank
        ((finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block
          visit carried hentry).adaptiveInputStep (fun bit => .bit bit)
            (finiteCachedVisitAdaptiveQueryIndex? machine n) input state).1 := by
  exact finiteCachedVisitAdaptiveInputStep_inputRank_mono machine n T
    (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (fixedAlphaVisitRemaining visit)
    (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry)
    visit.exit input state

/-- Specialized strict post-query rank growth for an advertised fixed-alpha
visit. -/
theorem finiteCachedFixedAlphaVisitAdaptiveInputStep_query_lt_inputRank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    (input : Fin n → Bool)
    (state : (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha
      block visit carried hentry).FueledState T)
    (index : Fin n)
    (hquery :
      (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
        carried hentry).adaptiveQuery?
          (finiteCachedVisitAdaptiveQueryIndex? machine n) state = some index) :
    index.val < finiteCachedVisitPhaseInputRank
      ((finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block
        visit carried hentry).adaptiveInputStep (fun bit => .bit bit)
          (finiteCachedVisitAdaptiveQueryIndex? machine n) input state).1 := by
  exact finiteCachedVisitAdaptiveInputStep_query_lt_inputRank machine n T
    (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (fixedAlphaVisitRemaining visit)
    (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry)
    visit.exit input state index hquery

/-- Specialized pre-query lower bound for an advertised fixed-alpha visit. -/
theorem finiteCachedFixedAlphaVisitAdaptiveQuery_inputRank_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    (state : (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha
      block visit carried hentry).FueledState T)
    (index : Fin n)
    (hquery :
      (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
        carried hentry).adaptiveQuery?
          (finiteCachedVisitAdaptiveQueryIndex? machine n) state = some index) :
    finiteCachedVisitPhaseInputRank state.1 ≤ index.val := by
  exact finiteCachedVisitAdaptiveQuery_inputRank_le machine n T
    (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (fixedAlphaVisitRemaining visit)
    (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry)
    visit.exit state index hquery

/-- Every coordinate already queried by a compiled prefix lies strictly
below the prefix's resulting input-head rank. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_executePrefix_query_lt_rank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    (input : Fin n → Bool) (k : Nat) (hk : k ≤ T)
    (index : Fin n)
    (hmem : index ∈
      ((compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine alpha
        block visit carried hentry).executePrefix input k hk).2) :
    index.val < finiteCachedVisitPhaseInputRank
      ((compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine alpha
        block visit carried hentry).executePrefix input k hk).1.1 := by
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha
    block visit carried hentry
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedVisitAdaptiveQueryIndex? (H := T)
      (w := advertisedBlockWidth alpha.offsets block) machine n
  let program := compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine
    alpha block visit carried hentry
  change index ∈ (program.executePrefix input k hk).2 at hmem
  change index.val < finiteCachedVisitPhaseInputRank
    (program.executePrefix input k hk).1.1
  induction k generalizing index with
  | zero =>
      simp [LayeredQueryProgram.executePrefix] at hmem
  | succ k ih =>
      let previous := program.executePrefix input k (by omega)
      let layer : Fin T := ⟨k, by omega⟩
      let query := program.query? layer previous.1
      have hmemAppend : index ∈ previous.2 ++ query.toList := by
        simpa [LayeredQueryProgram.executePrefix, previous, layer, query] using
          hmem
      have hnextEq :
          program.next layer previous.1 (query.map input) =
            verifier.adaptiveInputStep (fun bit => .bit bit) selector input
              previous.1 := by
        rfl
      have hnextMono : finiteCachedVisitPhaseInputRank previous.1.1 ≤
          finiteCachedVisitPhaseInputRank
            (program.next layer previous.1 (query.map input)).1 := by
        rw [hnextEq]
        exact finiteCachedFixedAlphaVisitAdaptiveInputStep_inputRank_mono
          machine alpha block visit carried hentry input previous.1
      have hresult : index.val < finiteCachedVisitPhaseInputRank
          (program.next layer previous.1 (query.map input)).1 := by
        rw [List.mem_append] at hmemAppend
        rcases hmemAppend with hprevious | hcurrent
        · have hprior : index.val <
              finiteCachedVisitPhaseInputRank previous.1.1 := by
            exact ih (by omega) index (by simpa [previous] using hprevious)
          exact hprior.trans_le hnextMono
        · have hquerySome : query = some index := by
            cases hquery : query with
            | none =>
                simp [hquery] at hcurrent
            | some current =>
                simp only [hquery, Option.toList_some,
                  List.mem_singleton] at hcurrent
                subst current
                rfl
          have hadaptive : verifier.adaptiveQuery? selector previous.1 =
              some index := by
            change query = some index
            exact hquerySome
          rw [hnextEq]
          exact
            finiteCachedFixedAlphaVisitAdaptiveInputStep_query_lt_inputRank
              machine alpha block visit carried hentry input previous.1 index
                hadaptive
      simpa [LayeredQueryProgram.executePrefix, previous, layer, query] using
        hresult

/-- Along every compiled execution, each newly exposed cached input head is
strictly larger than every coordinate queried earlier in that execution. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_freshQueriesStrictlyIncrease
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val) :
    FiniteStreamingVerifier.FreshQueriesStrictlyIncrease
      (compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine alpha block
        visit carried hentry) := by
  intro input k hk prior current hprior hcurrent
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha
    block visit carried hentry
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedVisitAdaptiveQueryIndex? (H := T)
      (w := advertisedBlockWidth alpha.offsets block) machine n
  let program := compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine
    alpha block visit carried hentry
  let executed := program.executePrefix input k (Nat.le_of_lt hk)
  have hpriorRank : prior.val <
      finiteCachedVisitPhaseInputRank executed.1.1 := by
    exact
      compileAdaptiveFiniteCachedFixedAlphaVisit_executePrefix_query_lt_rank
        machine alpha block visit carried hentry input k (Nat.le_of_lt hk)
          prior (by simpa [program, executed] using hprior)
  have hadaptive : verifier.adaptiveQuery? selector executed.1 = some current := by
    change program.query? ⟨k, hk⟩ executed.1 = some current
    simpa [program, executed] using hcurrent
  have hcurrentRank : finiteCachedVisitPhaseInputRank executed.1.1 ≤
      current.val :=
    finiteCachedFixedAlphaVisitAdaptiveQuery_inputRank_le machine alpha block
      visit carried hentry executed.1 current hadaptive
  have hvalues : prior.val < current.val :=
    hpriorRank.trans_le hcurrentRank
  exact hvalues

/-- The adaptive cached fixed-alpha visit compiler is unconditionally
read-once; no fixed query permutation or external freshness hypothesis is
required. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val) :
    (compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine alpha block
      visit carried hentry).IsReadOnce := by
  exact FiniteStreamingVerifier.isReadOnce_of_freshQueriesStrictlyIncrease _
    (compileAdaptiveFiniteCachedFixedAlphaVisit_freshQueriesStrictlyIncrease
      (n := n) machine alpha block visit carried hentry)

end OneTapeMagnification
end Frontier
end Pnp4
