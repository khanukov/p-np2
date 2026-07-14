import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListRollingCounters
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSegmentCorrectness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Operational correctness of the rolling fixed-block visit-list verifier

This module identifies the actual input-driven execution of the rolling list
transition with the previously defined chronological rolling runner.  It is
the operational bridge needed to identify the fold carried by the fused
all-block verifier, rather than merely its erased completion state.
-/

local instance cachedInputMachineStateDecidableEqForRollingOperational
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Lift one rolling one-visit phase at a fixed list cursor. -/
def liftFiniteCachedBlockVisitListRollingPhase
    {State : Type} {H w k m : Nat} (cursor : Fin k) :
    FiniteCachedVisitRollingCounterState State H w m →
      FiniteCachedBlockVisitListRollingCounterState State H w k m
  | state =>
      ⟨liftFiniteCachedBlockVisitPhase cursor state.phase, state.counters⟩

/-- Halting, input requests, acceptance, and query selection are inherited
from the erased list phase. -/
def finiteCachedBlockVisitListRollingHalted
    {State : Type} {H w k m : Nat} :
    FiniteCachedBlockVisitListRollingCounterState State H w k m → Bool :=
  fun state => finiteCachedBlockVisitListHalted state.listState

def finiteCachedBlockVisitListRollingRequestsInput
    (machine : DeterministicMachine) (n : Nat) {T w k m : Nat} :
    FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T w k m → Bool :=
  fun state =>
    finiteCachedBlockVisitListRequestsInput machine n state.listState

def finiteCachedBlockVisitListRollingAccept
    {State : Type} {H w k m : Nat} :
    FiniteCachedBlockVisitListRollingCounterState State H w k m → Bool :=
  fun state => finiteCachedBlockVisitListAccept state.listState

def finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
    (machine : DeterministicMachine) (n : Nat) {T w k m : Nat} :
    FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T w k m → Option (Fin n) :=
  fun state =>
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n state.listState

/-- Genuine finite streaming verifier for one rolling block-visit list. -/
def finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m → Nat)
    (initialCounters : BoundedCrossingCounterVector T m) :
    FiniteStreamingVerifier ReadOnlySymbol where
  State := FiniteCachedBlockVisitListRollingCounterState
    (cachedInputMachine machine).State T
    (advertisedBlockWidth alpha.offsets block) visits.length m
  stateFintype := by
    letI := (cachedInputMachine machine).stateFintype
    exact inferInstance
  start :=
    ⟨finiteCachedBlockVisitListStart machine alpha block initialSlab visits
      hentries, initialCounters⟩
  halted := finiteCachedBlockVisitListRollingHalted
  requestsInput := finiteCachedBlockVisitListRollingRequestsInput machine n
  step := finiteCachedBlockVisitListStreamingRollingCounterStep machine n alpha
    block visits hentries boundaries
  accept := finiteCachedBlockVisitListRollingAccept

/-- The input-driven rolling list execution follows the exact semantic unread
trace of one active visit, updating its counter vector in the same steps. -/
theorem finiteCachedBlockVisitListRolling_inputDrivenCore_active_eq_streaming
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m → Nat)
    (cursor : Fin visits.length)
    (remaining : Fin (T + 1))
    (live : LocalReplayState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (initialCounters : BoundedCrossingCounterVector T m)
    (counters : BoundedCrossingCounterVector T m)
    (unreads : List ReadOnlySymbol)
    (hnonempty : unreads ≠ [])
    (hlength : remaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block) unreads live) :
    let verifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
        input.length alpha block initialSlab visits hentries boundaries
          initialCounters
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index) unreads.length
        ⟨.active cursor (.running remaining live), counters⟩ =
      liftFiniteCachedBlockVisitListRollingPhase cursor
        (runFiniteCachedVisitStreamingRollingCountersWithUnreads machine
          input.length T (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          boundaries unreads ⟨.running remaining live, counters⟩) := by
  dsimp only
  induction unreads generalizing remaining live counters with
  | nil => contradiction
  | cons unread rest ih =>
      have hpositive : 0 < remaining.val := by
        rw [hlength]
        simp
      have hread : readOnlySymbol input live.inputHead.val = unread := by
        cases rest with
        | nil => simpa [FiniteCachedVisitSymbolsAgree] using hagree
        | cons nextUnread tail =>
            exact (finiteCachedVisitSymbolsAgree_cons_cons machine input T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block) unread nextUnread
              tail live).mp hagree |>.1
      have hanswer :=
        finiteCachedVisit_inputDrivenAnswer_eq_streamingAnswer machine input
          remaining live unread hpositive hread
      simp only [List.length_cons, FiniteStreamingVerifier.inputDrivenCore]
      simp only [finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier,
        finiteCachedBlockVisitListRollingHalted,
        finiteCachedBlockVisitListHalted, Bool.false_eq_true, ↓reduceIte,
        finiteCachedBlockVisitListRollingRequestsInput,
        finiteCachedBlockVisitListRequestsInput,
        finiteCachedBlockVisitListRollingAdaptiveQueryIndex?,
        finiteCachedBlockVisitListAdaptiveQueryIndex?,
        finiteCachedBlockVisitListStreamingRollingCounterStep]
      rw [runFiniteCachedVisitStreamingRollingCountersWithUnreads_cons]
      simp only [streamingAnswerForPhaseUnread]
      rw [hanswer]
      cases rest with
      | nil => rfl
      | cons nextUnread tail =>
          have hend : cachedLocalStepNeedsUnread machine live = true →
              ¬ live.inputHead.val < input.length → unread = .rightEnd := by
            intro _ hhead
            calc
              unread = readOnlySymbol input live.inputHead.val := hread.symm
              _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le input
                live.inputHead.val (Nat.le_of_not_gt hhead)
          have hstreamStep := finiteCachedVisitStreamingStep_answerForUnread
            machine input.length
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              remaining live unread hend
          have hzero : remaining.val ≠ 0 := by omega
          have hone : remaining.val ≠ 1 := by
            rw [hlength]
            simp
          cases hlocal : finiteLocalCachedStep machine T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block) unread live with
          | inside next =>
              have htailAgree : FiniteCachedVisitSymbolsAgree machine input T
                  (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (nextUnread :: tail) next := by
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
                exact hagree.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              let stepped := finiteCachedVisitStreamingRollingCounterStep
                machine input.length T
                  (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
                  boundaries ⟨.running remaining live, counters⟩
                    (streamingAnswerForUnread machine input.length live unread)
              have hsteppedPhase : stepped.phase =
                  .running (spendVisitStep remaining) next := by
                change (finiteCachedVisitStreamingRollingCounterStep machine
                  input.length T (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (advertisedBlockLower_add_width_le_horizon
                    alpha.offsets block)
                  boundaries ⟨.running remaining live, counters⟩
                    (streamingAnswerForUnread machine input.length live unread)).phase = _
                rw [finiteCachedVisitStreamingRollingCounterStep_phase,
                  hstreamStep]
                simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
              cases hstepped : stepped with
              | mk steppedPhase steppedCounters =>
                  have hp : steppedPhase =
                      .running (spendVisitStep remaining) next := by
                    simpa [hstepped] using hsteppedPhase
                  subst steppedPhase
                  simpa [stepped, hstepped,
                    liftFiniteCachedBlockVisitListRollingPhase,
                    liftFiniteCachedBlockVisitPhase] using
                      ih (spendVisitStep remaining) next steppedCounters
                        (by simp) htailLength htailAgree
          | halted outcome =>
              have htailAgree : FiniteCachedVisitSymbolsAgree machine input T
                  (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (nextUnread :: tail) live := by
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
                exact hagree.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              let stepped := finiteCachedVisitStreamingRollingCounterStep
                machine input.length T
                  (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
                  boundaries ⟨.running remaining live, counters⟩
                    (streamingAnswerForUnread machine input.length live unread)
              have hsteppedPhase : stepped.phase =
                  .running (spendVisitStep remaining) live := by
                change (finiteCachedVisitStreamingRollingCounterStep machine
                  input.length T (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (advertisedBlockLower_add_width_le_horizon
                    alpha.offsets block)
                  boundaries ⟨.running remaining live, counters⟩
                    (streamingAnswerForUnread machine input.length live unread)).phase = _
                rw [finiteCachedVisitStreamingRollingCounterStep_phase,
                  hstreamStep]
                simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
              cases hstepped : stepped with
              | mk steppedPhase steppedCounters =>
                  have hp : steppedPhase =
                      .running (spendVisitStep remaining) live := by
                    simpa [hstepped] using hsteppedPhase
                  subst steppedPhase
                  simpa [stepped, hstepped,
                    liftFiniteCachedBlockVisitListRollingPhase,
                    liftFiniteCachedBlockVisitPhase] using
                      ih (spendVisitStep remaining) live steppedCounters
                        (by simp) htailLength htailAgree
          | workHeadExit =>
              rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
              have hfalse : False := by simpa using hagree.2
              exact hfalse.elim
          | inputHorizonExceeded =>
              rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
              have hfalse : False := by simpa using hagree.2
              exact hfalse.elim

/-- A certified head visit consumes exactly its advertised transitions in the
rolling verifier, leaving the certified final phase and precisely the counter
vector computed by the specialized rolling visit runner. -/
theorem finiteCachedBlockVisitListRolling_inputDrivenCore_head_completed_of_stepCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (first : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (boundaries : Fin m → Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (hcertificate : FiniteCachedFixedAlphaVisitStreamingStepCertificate
      machine input alpha block first initialSlab final) :
    let verifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
        input.length alpha block initialSlab (first :: rest) hentries
          boundaries initialCounters
    let listEntry := hentries.head alpha block first rest
    let current := runFiniteCachedFixedAlphaVisitRollingCounters machine input
      alpha block first initialSlab listEntry boundaries initialCounters
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index) first.steps verifier.start =
      ⟨.active ⟨0, by simp⟩ (.completed final), current.counters⟩ := by
  rcases hcertificate with
    ⟨certificateEntry, hagree, hstream, hstate, hinput, hwork⟩
  let cursor : Fin (first :: rest).length := ⟨0, by simp⟩
  let listEntry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      first.entry.workHead.val := hentries.head alpha block first rest
  have hentryEq : certificateEntry = listEntry := Subsingleton.elim _ _
  subst certificateEntry
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block first initialSlab)
    first.steps
  let initial := finiteCachedStateOfVisitEntry machine alpha block first
    initialSlab listEntry
  let current := runFiniteCachedFixedAlphaVisitRollingCounters machine input
    alpha block first initialSlab listEntry boundaries initialCounters
  let verifier :=
    finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
      input.length alpha block initialSlab (first :: rest) hentries boundaries
        initialCounters
  have hstart : verifier.start =
      ⟨.active cursor (.running (fixedAlphaVisitRemaining first) initial),
        initialCounters⟩ := by
    change
      (⟨finiteCachedBlockVisitListStart machine alpha block initialSlab
        (first :: rest) hentries, initialCounters⟩ : verifier.State) = _
    rw [finiteCachedBlockVisitListStart]
    split
    · simp [finiteCachedBlockVisitListActiveState, cursor, initial]
    · simp_all
  have hnonempty : unreads ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [unreads, FixedAlphaBlockVisit.steps_pos]
  have hlength : (fixedAlphaVisitRemaining first).val = unreads.length := by
    simp [fixedAlphaVisitRemaining, unreads]
  have hsegment :=
    finiteCachedBlockVisitListRolling_inputDrivenCore_active_eq_streaming
      machine input alpha block initialSlab (first :: rest) hentries boundaries
        cursor (fixedAlphaVisitRemaining first) initial initialCounters
          initialCounters unreads hnonempty hlength
          (by simpa [unreads, initial, listEntry] using hagree)
  change verifier.inputDrivenCore (fun bit => .bit bit)
      (finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
        machine input.length)
      (fun index => input.get index) first.steps verifier.start = _
  rw [hstart]
  have hsteps : unreads.length = first.steps := by simp [unreads]
  rw [← hsteps]
  rw [hsegment]
  have hcurrentPhase : current.phase = .completed final := by
    rw [runFiniteCachedFixedAlphaVisitRollingCounters_phase]
    simpa [unreads, initial, listEntry] using hstream
  rcases hcurrentEq : current with ⟨phase, counters⟩
  have hp : phase = .completed final := by
    simpa [hcurrentEq] using hcurrentPhase
  subst phase
  have hrunEq :
      runFiniteCachedVisitStreamingRollingCountersWithUnreads machine
          input.length T (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          boundaries unreads
          ⟨.running (fixedAlphaVisitRemaining first) initial,
            initialCounters⟩ = current := by
    rfl
  rw [hrunEq, hcurrentEq]
  have houtputCounters :
      (runFiniteCachedFixedAlphaVisitRollingCounters machine input alpha block
        first initialSlab (hentries.head alpha block first rest) boundaries
          initialCounters).counters = counters := by
    change current.counters = counters
    rw [hcurrentEq]
  simp [liftFiniteCachedBlockVisitListRollingPhase,
    liftFiniteCachedBlockVisitPhase, cursor, houtputCounters]

/-- Prepend a completed tail execution while retaining its rolling vector. -/
def prependFiniteCachedBlockVisitListRollingState
    {State : Type} {H w m : Nat}
    (first : FixedAlphaBlockVisit State H)
    (rest : List (FixedAlphaBlockVisit State H)) :
    FiniteCachedBlockVisitListRollingCounterState
        State H w rest.length m →
      FiniteCachedBlockVisitListRollingCounterState
        State H w (first :: rest).length m
  | state =>
      ⟨prependFiniteCachedBlockVisitListState first rest state.listState,
        state.counters⟩

@[simp]
theorem finiteCachedBlockVisitListRollingHalted_prepend
    {State : Type} {H w m : Nat}
    (first : FixedAlphaBlockVisit State H)
    (rest : List (FixedAlphaBlockVisit State H))
    (state : FiniteCachedBlockVisitListRollingCounterState
      State H w rest.length m) :
    finiteCachedBlockVisitListRollingHalted
        (prependFiniteCachedBlockVisitListRollingState first rest state) =
      finiteCachedBlockVisitListRollingHalted state := by
  rcases state with ⟨state, counters⟩
  exact finiteCachedBlockVisitListHalted_prepend first rest state

@[simp]
theorem finiteCachedBlockVisitListRollingRequestsInput_prepend
    (machine : DeterministicMachine) (n : Nat) {T w m : Nat}
    (first : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (state : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T w rest.length m) :
    finiteCachedBlockVisitListRollingRequestsInput machine n
        (prependFiniteCachedBlockVisitListRollingState first rest state) =
      finiteCachedBlockVisitListRollingRequestsInput machine n state := by
  rcases state with ⟨state, counters⟩
  exact finiteCachedBlockVisitListRequestsInput_prepend machine n first rest state

@[simp]
theorem finiteCachedBlockVisitListRollingAdaptiveQueryIndex?_prepend
    (machine : DeterministicMachine) (n : Nat) {T w m : Nat}
    (first : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (state : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T w rest.length m) :
    finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n
        (prependFiniteCachedBlockVisitListRollingState first rest state) =
      finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n state := by
  rcases state with ⟨state, counters⟩
  exact finiteCachedBlockVisitListAdaptiveQueryIndex?_prepend
    machine n first rest state

/-- The rolling transition commutes with the tail-cursor embedding. -/
theorem finiteCachedBlockVisitListStreamingRollingCounterStep_prepend
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (first : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hcons : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (htail : FixedAlphaBlockVisitEntriesInside alpha block rest)
    (boundaries : Fin m → Nat)
    (state : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) rest.length m)
    (supplied : Option ReadOnlySymbol) :
    finiteCachedBlockVisitListStreamingRollingCounterStep machine n alpha block
        (first :: rest) hcons boundaries
        (prependFiniteCachedBlockVisitListRollingState first rest state)
        supplied =
      prependFiniteCachedBlockVisitListRollingState first rest
        (finiteCachedBlockVisitListStreamingRollingCounterStep machine n alpha
          block rest htail boundaries state supplied) := by
  rcases state with ⟨listState, counters⟩
  cases listState with
  | completed slab =>
      have hstep := finiteCachedBlockVisitListStreamingStep_prepend machine n
        alpha block first rest hcons htail (.completed slab) supplied
      simpa [prependFiniteCachedBlockVisitListRollingState,
        finiteCachedBlockVisitListStreamingRollingCounterStep] using
        congrArg (fun next =>
          ({ listState := next, counters := counters } :
            FiniteCachedBlockVisitListRollingCounterState
              (cachedInputMachine machine).State T
              (advertisedBlockWidth alpha.offsets block)
              (first :: rest).length m)) hstep
  | rejected =>
      have hstep := finiteCachedBlockVisitListStreamingStep_prepend machine n
        alpha block first rest hcons htail (.rejected) supplied
      simpa [prependFiniteCachedBlockVisitListRollingState,
        finiteCachedBlockVisitListStreamingRollingCounterStep] using
        congrArg (fun next =>
          ({ listState := next, counters := counters } :
            FiniteCachedBlockVisitListRollingCounterState
              (cachedInputMachine machine).State T
              (advertisedBlockWidth alpha.offsets block)
              (first :: rest).length m)) hstep
  | active cursor phase =>
      cases phase with
      | running remaining live =>
          simp only [prependFiniteCachedBlockVisitListRollingState,
            prependFiniteCachedBlockVisitListState,
            finiteCachedBlockVisitListStreamingRollingCounterStep,
            liftFiniteCachedBlockVisitPhase]
          generalize finiteCachedVisitStreamingRollingCounterStep machine n T
            (advertisedBlockWidth alpha.offsets block)
            (advertisedBlockLower alpha.offsets block)
            (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
            boundaries ⟨.running remaining live, counters⟩ supplied = next
          rcases next with ⟨phase, nextCounters⟩
          cases phase <;> rfl
      | completed final =>
          have hstep := finiteCachedBlockVisitListStreamingStep_prepend machine
            n alpha block first rest hcons htail
              (.active cursor (.completed final)) supplied
          simpa [prependFiniteCachedBlockVisitListRollingState,
            prependFiniteCachedBlockVisitListState,
            finiteCachedBlockVisitListStreamingRollingCounterStep] using
            congrArg (fun next =>
              ({ listState := next, counters := counters } :
                FiniteCachedBlockVisitListRollingCounterState
                  (cachedInputMachine machine).State T
                  (advertisedBlockWidth alpha.offsets block)
                  (first :: rest).length m)) hstep
      | rejected failure =>
          have hstep := finiteCachedBlockVisitListStreamingStep_prepend machine
            n alpha block first rest hcons htail
              (.active cursor (.rejected failure)) supplied
          simpa [prependFiniteCachedBlockVisitListRollingState,
            prependFiniteCachedBlockVisitListState,
            finiteCachedBlockVisitListStreamingRollingCounterStep] using
            congrArg (fun next =>
              ({ listState := next, counters := counters } :
                FiniteCachedBlockVisitListRollingCounterState
                  (cachedInputMachine machine).State T
                  (advertisedBlockWidth alpha.offsets block)
                  (first :: rest).length m)) hstep

/-- Explicit-state input-driven execution is independent of the two proof-only
start slabs and commutes with the rolling tail embedding. -/
theorem finiteCachedBlockVisitListRolling_inputDrivenCore_prepend_twoStarts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (first : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (consInitial tailInitial : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hcons : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (htail : FixedAlphaBlockVisitEntriesInside alpha block rest)
    (boundaries : Fin m → Nat)
    (consInitialCounters tailInitialCounters :
      BoundedCrossingCounterVector T m)
    (fuel : Nat)
    (state : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) rest.length m) :
    let consVerifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
        input.length alpha block consInitial (first :: rest) hcons boundaries
          consInitialCounters
    let tailVerifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
        input.length alpha block tailInitial rest htail boundaries
          tailInitialCounters
    consVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index) fuel
        (prependFiniteCachedBlockVisitListRollingState first rest state) =
      prependFiniteCachedBlockVisitListRollingState first rest
        (tailVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
            machine input.length)
          (fun index => input.get index) fuel state) := by
  dsimp only
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [FiniteStreamingVerifier.inputDrivenCore]
      simp only [finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier]
      rw [finiteCachedBlockVisitListRollingHalted_prepend]
      by_cases hhalt : finiteCachedBlockVisitListRollingHalted state = true
      · simp [hhalt]
      · have hhaltFalse :
            finiteCachedBlockVisitListRollingHalted state = false := by
          cases h : finiteCachedBlockVisitListRollingHalted state <;> simp_all
        simp only [hhaltFalse, Bool.false_eq_true, ↓reduceIte]
        simp only [finiteCachedBlockVisitListRollingRequestsInput_prepend,
          finiteCachedBlockVisitListRollingAdaptiveQueryIndex?_prepend]
        rw [finiteCachedBlockVisitListStreamingRollingCounterStep_prepend]
        exact ih _

/-- Erasing the live counter vector from an arbitrary rolling-list execution
recovers the ordinary finite cached list execution at exactly the same fuel. -/
theorem finiteCachedBlockVisitListRolling_inputDrivenCore_listState
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m → Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (input : Fin n → Bool) (fuel : Nat)
    (state : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length m) :
    let rolling :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
        alpha block initialSlab visits hentries boundaries initialCounters
    let ordinary := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine n alpha block initialSlab visits hentries
    (rolling.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n)
        input fuel state).listState =
      ordinary.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
        input fuel state.listState := by
  dsimp only
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [FiniteStreamingVerifier.inputDrivenCore]
      simp only [finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier,
        finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
        finiteCachedBlockVisitListRollingHalted,
        finiteCachedBlockVisitListRollingRequestsInput,
        finiteCachedBlockVisitListRollingAdaptiveQueryIndex?]
      by_cases hhalt : finiteCachedBlockVisitListHalted state.listState = true
      · simp [hhalt]
      · have hhaltFalse :
            finiteCachedBlockVisitListHalted state.listState = false := by
          cases h : finiteCachedBlockVisitListHalted state.listState <;>
            simp_all
        simp only [hhaltFalse, Bool.false_eq_true, ↓reduceIte]
        let supplied : Option ReadOnlySymbol :=
          if finiteCachedBlockVisitListRequestsInput machine n state.listState
          then
            (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
              state.listState).map
                (fun index => ReadOnlySymbol.bit (input index))
          else none
        let next := finiteCachedBlockVisitListStreamingRollingCounterStep
          machine n alpha block visits hentries boundaries state supplied
        have hih := ih next
        have hstep : next.listState =
            finiteCachedBlockVisitListStreamingStep machine n alpha block
              visits hentries state.listState supplied := by
          exact finiteCachedBlockVisitListStreamingRollingCounterStep_listState
            machine n alpha block visits hentries boundaries state supplied
        calc
          _ = (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
                alpha block initialSlab visits hentries).inputDrivenCore
              (fun bit => .bit bit)
              (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
              input fuel next.listState := by
                simpa [next, supplied,
                  finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier] using
                    hih
          _ = _ := by
            rw [hstep]
            rfl

/-- A recursively certified block-visit list reaches the exact result of the
chronological rolling runner.  In particular, this identifies both the final
carried slab and every live crossing counter, without an erasure premise. -/
theorem finiteCachedBlockVisitListRolling_inputDrivenCore_completed_of_certificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m → Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (hcertificate : FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
      machine input alpha block initialSlab visits) :
    let result := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
      machine input alpha block boundaries visits hentries initialSlab
        initialCounters
    let verifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
        input.length alpha block initialSlab visits hentries boundaries
          initialCounters
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel visits) verifier.start =
      ⟨.completed result.finalSlab, result.counters⟩ := by
  induction visits generalizing initialSlab initialCounters with
  | nil =>
      rfl
  | cons first rest ih =>
      rcases hcertificate with ⟨firstFinal, hfirst, htail⟩
      let tailEntries : FixedAlphaBlockVisitEntriesInside alpha block rest :=
        fun visit hmem => hentries visit (by simp [hmem])
      let current := runFiniteCachedFixedAlphaVisitRollingCounters machine
        input alpha block first initialSlab
          (hentries.head alpha block first rest) boundaries initialCounters
      let tailResult := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
        machine input alpha block boundaries rest tailEntries
          firstFinal.workSlab current.counters
      have htailCore := ih firstFinal.workSlab tailEntries current.counters htail
      let consVerifier :=
        finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
          input.length alpha block initialSlab (first :: rest) hentries
            boundaries initialCounters
      let tailVerifier :=
        finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
          input.length alpha block firstFinal.workSlab rest tailEntries
            boundaries current.counters
      let consSelector :
          FiniteCachedBlockVisitListRollingCounterState
            (cachedInputMachine machine).State T
            (advertisedBlockWidth alpha.offsets block)
            (first :: rest).length m → Option (Fin input.length) :=
        finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
          machine input.length
      let tailSelector :
          FiniteCachedBlockVisitListRollingCounterState
            (cachedInputMachine machine).State T
            (advertisedBlockWidth alpha.offsets block) rest.length m →
              Option (Fin input.length) :=
        finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
          machine input.length
      let inputBits : Fin input.length → Bool := fun index => input.get index
      let cursor : Fin (first :: rest).length := ⟨0, by simp⟩
      have hhead : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits first.steps consVerifier.start =
          ⟨.active cursor (.completed firstFinal), current.counters⟩ := by
        simpa [consVerifier, consSelector, inputBits, cursor, current] using
          finiteCachedBlockVisitListRolling_inputDrivenCore_head_completed_of_stepCertificate
            machine input alpha block initialSlab first rest hentries
              boundaries initialCounters firstFinal hfirst
      rcases hfirst with
        ⟨firstEntry, firstAgree, firstStream, firstState, firstInput,
          firstWork⟩
      have hentryEq : firstEntry = hentries.head alpha block first rest :=
        Subsingleton.elim _ _
      subst firstEntry
      have hcurrentPhase : current.phase = .completed firstFinal := by
        change
          (runFiniteCachedFixedAlphaVisitRollingCounters machine input alpha
            block first initialSlab
              (hentries.head alpha block first rest) boundaries
                initialCounters).phase = .completed firstFinal
        rw [runFiniteCachedFixedAlphaVisitRollingCounters_phase]
        exact firstStream
      have hfirstAccept : @finiteCachedVisitPhaseAccept
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block) first.exit
          (.completed firstFinal) = true :=
        (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block) first.exit firstFinal).2
            ⟨firstState, firstInput, firstWork⟩
      have hboundary : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits 1
            ⟨.active cursor (.completed firstFinal), current.counters⟩ =
          prependFiniteCachedBlockVisitListRollingState first rest
            tailVerifier.start := by
        cases rest with
        | nil =>
            simp [consVerifier, tailVerifier, cursor,
              FiniteStreamingVerifier.inputDrivenCore,
              finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier,
              finiteCachedBlockVisitListStart,
              finiteCachedBlockVisitListRollingHalted,
              finiteCachedBlockVisitListHalted,
              finiteCachedBlockVisitListRollingRequestsInput,
              finiteCachedBlockVisitListRequestsInput,
              finiteCachedVisitPhaseRequestsInput,
              finiteCachedBlockVisitListStreamingRollingCounterStep,
              finiteCachedBlockVisitListStreamingStep,
              prependFiniteCachedBlockVisitListRollingState,
              prependFiniteCachedBlockVisitListState, hfirstAccept]
        | cons second remaining =>
            simp [consVerifier, tailVerifier, cursor,
              FiniteStreamingVerifier.inputDrivenCore,
              finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier,
              finiteCachedBlockVisitListStart,
              finiteCachedBlockVisitListRollingHalted,
              finiteCachedBlockVisitListHalted,
              finiteCachedBlockVisitListRollingRequestsInput,
              finiteCachedBlockVisitListRequestsInput,
              finiteCachedVisitPhaseRequestsInput,
              finiteCachedBlockVisitListStreamingRollingCounterStep,
              finiteCachedBlockVisitListStreamingStep, hfirstAccept,
              finiteCachedBlockVisitListActiveState,
              prependFiniteCachedBlockVisitListRollingState,
              prependFiniteCachedBlockVisitListState]
      have htailEmbedded : consVerifier.inputDrivenCore
          (fun bit => .bit bit) consSelector inputBits
          (finiteCachedBlockVisitListFuel rest)
          (prependFiniteCachedBlockVisitListRollingState first rest
            tailVerifier.start) =
          ⟨.completed tailResult.finalSlab, tailResult.counters⟩ := by
        change tailVerifier.inputDrivenCore (fun bit => .bit bit)
            tailSelector inputBits (finiteCachedBlockVisitListFuel rest)
              tailVerifier.start =
            ⟨.completed tailResult.finalSlab, tailResult.counters⟩ at htailCore
        have hembed :=
          finiteCachedBlockVisitListRolling_inputDrivenCore_prepend_twoStarts
            machine input alpha block first rest initialSlab
              firstFinal.workSlab hentries tailEntries boundaries
                initialCounters current.counters
                  (finiteCachedBlockVisitListFuel rest) tailVerifier.start
        have hembed' : consVerifier.inputDrivenCore
            (fun bit => .bit bit) consSelector inputBits
              (finiteCachedBlockVisitListFuel rest)
              (prependFiniteCachedBlockVisitListRollingState first rest
                tailVerifier.start) =
            prependFiniteCachedBlockVisitListRollingState first rest
              (tailVerifier.inputDrivenCore (fun bit => .bit bit)
                tailSelector inputBits (finiteCachedBlockVisitListFuel rest)
                  tailVerifier.start) := by
          simpa [consVerifier, tailVerifier, consSelector, tailSelector,
            inputBits] using hembed
        rw [htailCore] at hembed'
        simpa [prependFiniteCachedBlockVisitListRollingState,
          prependFiniteCachedBlockVisitListState] using hembed'
      change consVerifier.inputDrivenCore (fun bit => .bit bit) consSelector
          inputBits (finiteCachedBlockVisitListFuel (first :: rest))
            consVerifier.start = _
      have hfuel : finiteCachedBlockVisitListFuel (first :: rest) =
          first.steps + 1 + finiteCachedBlockVisitListFuel rest := by
        simp [finiteCachedBlockVisitListFuel,
          fixedAlphaBlockVisitsTotalSteps]
        omega
      rw [hfuel]
      rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit)
        consSelector inputBits (first.steps + 1)
          (finiteCachedBlockVisitListFuel rest)]
      rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit)
        consSelector inputBits first.steps 1]
      rw [hhead, hboundary]
      rw [htailEmbedded]
      simp [runFiniteCachedFixedAlphaBlockVisitListRollingCounters,
        current, tailResult, hcurrentPhase]

/-- Replay acceptance is the semantic entry point for the exact rolling-list
operational theorem. -/
theorem finiteCachedBlockVisitListRolling_inputDrivenCore_completed_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m → Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    let result := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
      machine input alpha block boundaries visits hentries initialSlab
        initialCounters
    let verifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
        input.length alpha block initialSlab visits hentries boundaries
          initialCounters
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel visits) verifier.start =
      ⟨.completed result.finalSlab, result.counters⟩ := by
  exact finiteCachedBlockVisitListRolling_inputDrivenCore_completed_of_certificate
    machine input alpha block initialSlab visits hentries boundaries
      initialCounters
      ((finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
        machine input alpha block initialSlab visits).2 haccepted)

end OneTapeMagnification
end Frontier
end Pnp4
