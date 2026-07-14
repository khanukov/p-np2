import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitStreamingVerifier
import Pnp4.Frontier.OneTapeMagnification.OnePassFixedAlphaVisit

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Rolling crossing counters fused with one finite cached visit step

The finite cached verifier already retains the pre-transition local work head
and, after every successful transition, the post-transition work head.  This
module updates a bounded vector of crossing counters in that same executable
transition.  No global configuration or actual run is added to the state.
-/

/-- One finite cached phase paired with a rolling bounded crossing vector. -/
structure FiniteCachedVisitRollingCounterState
    (State : Type) (H w m : Nat) where
  phase : FiniteCachedVisitStreamingState State H w
  counters : BoundedCrossingCounterVector H m
deriving Fintype

/-- Absolute work head exposed by a live or completed finite phase.  A failed
phase deliberately exposes no post-transition head. -/
def finiteCachedVisitStreamingPhaseWorkHead?
    {State : Type} {H w : Nat} (base : Nat) :
    FiniteCachedVisitStreamingState State H w → Option Nat
  | .running _ live => some (base + live.relativeWorkHead.val)
  | .completed final => some final.workHead.val
  | .rejected _ => none

/-- Update all rolling coordinates from the pre/post heads retained by one
finite phase transition.  Rejected transitions keep the prior vector because
they do not retain a valid post-transition endpoint. -/
def bumpBoundedCrossingCounterVectorAcrossFinitePhases
    {State : Type} {H w m : Nat}
    (base : Nat) (boundaries : Fin m → Nat)
    (before after : FiniteCachedVisitStreamingState State H w)
    (counters : BoundedCrossingCounterVector H m) :
    BoundedCrossingCounterVector H m :=
  match finiteCachedVisitStreamingPhaseWorkHead? base before,
      finiteCachedVisitStreamingPhaseWorkHead? base after with
  | some fromHead, some toHead =>
      bumpBoundedCrossingCounterVector boundaries fromHead toHead counters
  | _, _ => counters

/-- One executable streaming transition with its crossing-vector update
performed in the same state transformer. -/
def finiteCachedVisitStreamingRollingCounterStep
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat) :
    FiniteCachedVisitRollingCounterState
        (cachedInputMachine machine).State H w m →
      Option ReadOnlySymbol →
      FiniteCachedVisitRollingCounterState
        (cachedInputMachine machine).State H w m
  | state, supplied =>
      let next := finiteCachedVisitStreamingStep machine n H w base hbound
        state.phase supplied
      { phase := next
        counters := bumpBoundedCrossingCounterVectorAcrossFinitePhases base
          boundaries state.phase next state.counters }

/-- Erasing counters recovers exactly the original finite cached streaming
transition. -/
@[simp]
theorem finiteCachedVisitStreamingRollingCounterStep_phase
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (state : FiniteCachedVisitRollingCounterState
      (cachedInputMachine machine).State H w m)
    (supplied : Option ReadOnlySymbol) :
    (finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
      boundaries state supplied).phase =
      finiteCachedVisitStreamingStep machine n H w base hbound state.phase
        supplied := rfl

/-- A retained inside-slab successor bumps from the absolute pre-head to the
absolute post-head in the very same streaming transition. -/
theorem finiteCachedVisitStreamingRollingCounterStep_running
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (remaining nextRemaining : Fin (H + 1))
    (live next : LocalReplayState
      (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (supplied : Option ReadOnlySymbol)
    (hstep : finiteCachedVisitStreamingStep machine n H w base hbound
      (.running remaining live) supplied = .running nextRemaining next) :
    finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
        boundaries ⟨.running remaining live, counters⟩ supplied =
      ⟨.running nextRemaining next,
        bumpBoundedCrossingCounterVector boundaries
          (base + live.relativeWorkHead.val)
          (base + next.relativeWorkHead.val) counters⟩ := by
  simp only [finiteCachedVisitStreamingRollingCounterStep]
  rw [hstep]
  rfl

/-- A retained final successor bumps from the live absolute pre-head to the
retained final absolute post-head in the same streaming transition. -/
theorem finiteCachedVisitStreamingRollingCounterStep_completed
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (supplied : Option ReadOnlySymbol)
    (hstep : finiteCachedVisitStreamingStep machine n H w base hbound
      (.running remaining live) supplied = .completed final) :
    finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
        boundaries ⟨.running remaining live, counters⟩ supplied =
      ⟨.completed final,
        bumpBoundedCrossingCounterVector boundaries
          (base + live.relativeWorkHead.val) final.workHead.val counters⟩ := by
  simp only [finiteCachedVisitStreamingRollingCounterStep]
  rw [hstep]
  rfl

/-- A rejected local transition has no retained post-head and therefore leaves
the rolling vector unchanged. -/
theorem finiteCachedVisitStreamingRollingCounterStep_rejected
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (failure : FiniteCachedVisitStreamingFailure)
    (counters : BoundedCrossingCounterVector H m)
    (supplied : Option ReadOnlySymbol)
    (hstep : finiteCachedVisitStreamingStep machine n H w base hbound
      (.running remaining live) supplied = .rejected failure) :
    finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
      boundaries ⟨.running remaining live, counters⟩ supplied =
      ⟨.rejected failure, counters⟩ := by
  simp only [finiteCachedVisitStreamingRollingCounterStep]
  rw [hstep]
  rfl

/-- For an inside-slab local successor, the finite pre/post-head bump is
exactly the bump of the materialized global cached-machine transition. -/
theorem bumpBoundedCrossingCounterVector_inside_materialize
    (machine : DeterministicMachine) (input : List Bool)
    {H w base m : Nat} (boundaries : Fin m → Nat)
    (unread : ReadOnlySymbol)
    (live next : LocalReplayState
      (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (hunread : readOnlySymbol input live.inputHead.val = unread)
    (hlocal : finiteLocalCachedStep machine H w base unread live =
      .inside next) :
    bumpBoundedCrossingCounterVector boundaries
        (base + live.relativeWorkHead.val)
        (base + next.relativeWorkHead.val) counters =
      bumpBoundedCrossingCounterVector boundaries
        (materializeLocalReplayState base live).workHead
        (step (cachedInputMachine machine) input
          (materializeLocalReplayState base live)).workHead counters := by
  have hmaterialize := finiteLocalCachedStep_inside_materialize machine unread
    live next input hunread hlocal
  change bumpBoundedCrossingCounterVector boundaries
      (materializeLocalReplayState base live).workHead
      (materializeLocalReplayState base next).workHead counters = _
  rw [hmaterialize]

/-- The endpoint-retaining final local successor has the same exact global
pre/post-head bump, including a permitted final slab exit. -/
theorem bumpBoundedCrossingCounterVector_final_materialize
    (machine : DeterministicMachine) (input : List Bool)
    {H w base m : Nat} (boundaries : Fin m → Nat)
    (unread : ReadOnlySymbol)
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (hunread : readOnlySymbol input live.inputHead.val = unread)
    (hlocal : finiteLocalCachedFinalStep machine H w base unread live =
      .stepped final) :
    bumpBoundedCrossingCounterVector boundaries
        (base + live.relativeWorkHead.val) final.workHead.val counters =
      bumpBoundedCrossingCounterVector boundaries
        (materializeLocalReplayState base live).workHead
        (step (cachedInputMachine machine) input
          (materializeLocalReplayState base live)).workHead counters := by
  have hmaterialize :=
    finiteLocalCachedFinalStep_stepped_materialize machine unread live final
      input hunread hlocal
  change bumpBoundedCrossingCounterVector boundaries
      (materializeLocalReplayState base live).workHead
      (materializeFiniteLocalFinalState base final).workHead counters = _
  rw [hmaterialize]

/-- A nonfinal resolved streaming transition simultaneously advances the
finite phase and performs exactly the corresponding global one-pass counter
bump. -/
theorem finiteCachedVisitStreamingRollingCounterStep_inside_global
    (machine : DeterministicMachine) (input : List Bool)
    (n H w base : Nat) (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (remaining : Fin (H + 1))
    (live next : LocalReplayState
      (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (unread : ReadOnlySymbol)
    (hremaining : 1 < remaining.val)
    (hunread : readOnlySymbol input live.inputHead.val = unread)
    (hend : cachedLocalStepNeedsUnread machine live = true →
      ¬ live.inputHead.val < n → unread = .rightEnd)
    (hlocal : finiteLocalCachedStep machine H w base unread live =
      .inside next) :
    finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
        boundaries ⟨.running remaining live, counters⟩
          (streamingAnswerForUnread machine n live unread) =
      ⟨.running (spendVisitStep remaining) next,
        bumpBoundedCrossingCounterVector boundaries
          (materializeLocalReplayState base live).workHead
          (step (cachedInputMachine machine) input
            (materializeLocalReplayState base live)).workHead counters⟩ := by
  have hresolved := finiteCachedVisitStreamingStep_answerForUnread machine n
    hbound remaining live unread hend
  have hzero : remaining.val ≠ 0 := by omega
  have hone : remaining.val ≠ 1 := by omega
  have hstream : finiteCachedVisitStreamingStep machine n H w base hbound
      (.running remaining live)
        (streamingAnswerForUnread machine n live unread) =
      .running (spendVisitStep remaining) next := by
    rw [hresolved]
    simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
  rw [finiteCachedVisitStreamingRollingCounterStep_running machine n H w
    base hbound boundaries remaining (spendVisitStep remaining) live next
    counters (streamingAnswerForUnread machine n live unread) hstream]
  rw [bumpBoundedCrossingCounterVector_inside_materialize machine input
    boundaries unread live next counters hunread hlocal]

/-- The final resolved streaming transition simultaneously enters the
completed phase and performs the exact global one-pass counter bump. -/
theorem finiteCachedVisitStreamingRollingCounterStep_final_global
    (machine : DeterministicMachine) (input : List Bool)
    (n H w base : Nat) (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (unread : ReadOnlySymbol)
    (hremaining : remaining.val = 1)
    (hunread : readOnlySymbol input live.inputHead.val = unread)
    (hend : cachedLocalStepNeedsUnread machine live = true →
      ¬ live.inputHead.val < n → unread = .rightEnd)
    (hlocal : finiteLocalCachedFinalStep machine H w base unread live =
      .stepped final) :
    finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
        boundaries ⟨.running remaining live, counters⟩
          (streamingAnswerForUnread machine n live unread) =
      ⟨.completed final,
        bumpBoundedCrossingCounterVector boundaries
          (materializeLocalReplayState base live).workHead
          (step (cachedInputMachine machine) input
            (materializeLocalReplayState base live)).workHead counters⟩ := by
  have hresolved := finiteCachedVisitStreamingStep_answerForUnread machine n
    hbound remaining live unread hend
  have hstream : finiteCachedVisitStreamingStep machine n H w base hbound
      (.running remaining live)
        (streamingAnswerForUnread machine n live unread) =
      .completed final := by
    rw [hresolved]
    simp [advanceFiniteCachedVisitPhase, hremaining, hlocal]
  rw [finiteCachedVisitStreamingRollingCounterStep_completed machine n H w
    base hbound boundaries remaining live final counters
    (streamingAnswerForUnread machine n live unread) hstream]
  rw [bumpBoundedCrossingCounterVector_final_materialize machine input
    boundaries unread live final counters hunread hlocal]

/-- A nonfinal halted cached transition retains the local state and performs
the same zero-crossing bump as the stuttering global machine step. -/
theorem finiteCachedVisitStreamingRollingCounterStep_halted_global
    (machine : DeterministicMachine) (input : List Bool)
    (n H w base : Nat) (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (unread : ReadOnlySymbol) (outcome : HaltOutcome)
    (hremaining : 1 < remaining.val)
    (hend : cachedLocalStepNeedsUnread machine live = true →
      ¬ live.inputHead.val < n → unread = .rightEnd)
    (hlocal : finiteLocalCachedStep machine H w base unread live =
      .halted outcome) :
    finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
        boundaries ⟨.running remaining live, counters⟩
          (streamingAnswerForUnread machine n live unread) =
      ⟨.running (spendVisitStep remaining) live,
        bumpBoundedCrossingCounterVector boundaries
          (materializeLocalReplayState base live).workHead
          (step (cachedInputMachine machine) input
            (materializeLocalReplayState base live)).workHead counters⟩ := by
  have hresolved := finiteCachedVisitStreamingStep_answerForUnread machine n
    hbound remaining live unread hend
  have hzero : remaining.val ≠ 0 := by omega
  have hone : remaining.val ≠ 1 := by omega
  have hstream : finiteCachedVisitStreamingStep machine n H w base hbound
      (.running remaining live)
        (streamingAnswerForUnread machine n live unread) =
      .running (spendVisitStep remaining) live := by
    rw [hresolved]
    simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal]
  rw [finiteCachedVisitStreamingRollingCounterStep_running machine n H w
    base hbound boundaries remaining (spendVisitStep remaining) live live
    counters (streamingAnswerForUnread machine n live unread) hstream]
  have hhalt :=
    (finiteLocalCachedStep_eq_halted_iff machine unread live outcome).mp hlocal
  have hglobalHalt : (cachedInputMachine machine).halt
      (materializeLocalReplayState base live).state = some outcome := by
    simpa [materializeLocalReplayState] using hhalt
  rw [step_of_halted (cachedInputMachine machine) input
    (materializeLocalReplayState base live) outcome hglobalHalt]
  rfl

/-- A final halted transition enters the retained completed phase and matches
the same global stuttering bump. -/
theorem finiteCachedVisitStreamingRollingCounterStep_final_halted_global
    (machine : DeterministicMachine) (input : List Bool)
    (n H w base : Nat) (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (unread : ReadOnlySymbol) (outcome : HaltOutcome)
    (hremaining : remaining.val = 1)
    (hend : cachedLocalStepNeedsUnread machine live = true →
      ¬ live.inputHead.val < n → unread = .rightEnd)
    (hlocal : finiteLocalCachedFinalStep machine H w base unread live =
      .halted outcome) :
    finiteCachedVisitStreamingRollingCounterStep machine n H w base hbound
        boundaries ⟨.running remaining live, counters⟩
          (streamingAnswerForUnread machine n live unread) =
      ⟨.completed (finiteLocalFinalStateOfReplayState base hbound live),
        bumpBoundedCrossingCounterVector boundaries
          (materializeLocalReplayState base live).workHead
          (step (cachedInputMachine machine) input
            (materializeLocalReplayState base live)).workHead counters⟩ := by
  have hresolved := finiteCachedVisitStreamingStep_answerForUnread machine n
    hbound remaining live unread hend
  have hstream : finiteCachedVisitStreamingStep machine n H w base hbound
      (.running remaining live)
        (streamingAnswerForUnread machine n live unread) =
      .completed (finiteLocalFinalStateOfReplayState base hbound live) := by
    rw [hresolved]
    simp [advanceFiniteCachedVisitPhase, hremaining, hlocal]
  rw [finiteCachedVisitStreamingRollingCounterStep_completed machine n H w
    base hbound boundaries remaining live
    (finiteLocalFinalStateOfReplayState base hbound live) counters
    (streamingAnswerForUnread machine n live unread) hstream]
  have hhalt :=
    (finiteLocalCachedFinalStep_eq_halted_iff machine unread live outcome).mp
      hlocal
  have hglobalHalt : (cachedInputMachine machine).halt
      (materializeLocalReplayState base live).state = some outcome := by
    simpa [materializeLocalReplayState] using hhalt
  rw [step_of_halted (cachedInputMachine machine) input
    (materializeLocalReplayState base live) outcome hglobalHalt]
  rfl

/-- Run a chronological per-transition unread trace while updating the finite
streaming phase and all bounded crossing counters in one state transformer. -/
def runFiniteCachedVisitStreamingRollingCountersWithUnreads
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat) :
    List ReadOnlySymbol →
      FiniteCachedVisitRollingCounterState
        (cachedInputMachine machine).State H w m →
      FiniteCachedVisitRollingCounterState
        (cachedInputMachine machine).State H w m
  | [], state => state
  | unread :: rest, state =>
      runFiniteCachedVisitStreamingRollingCountersWithUnreads machine n H w
        base hbound boundaries rest
          (finiteCachedVisitStreamingRollingCounterStep machine n H w base
            hbound boundaries state
              (streamingAnswerForPhaseUnread machine n state.phase unread))

/-- One-step unfolding equation for the rolling comparison run. -/
theorem runFiniteCachedVisitStreamingRollingCountersWithUnreads_cons
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (unread : ReadOnlySymbol) (rest : List ReadOnlySymbol)
    (state : FiniteCachedVisitRollingCounterState
      (cachedInputMachine machine).State H w m) :
    runFiniteCachedVisitStreamingRollingCountersWithUnreads machine n H w base
        hbound boundaries (unread :: rest) state =
      runFiniteCachedVisitStreamingRollingCountersWithUnreads machine n H w
        base hbound boundaries rest
          (finiteCachedVisitStreamingRollingCounterStep machine n H w base
            hbound boundaries state
              (streamingAnswerForPhaseUnread machine n state.phase unread)) := by
  rfl

/-- Erasing the rolling counter vector after any unread trace recovers exactly
the established streaming comparison run. -/
theorem runFiniteCachedVisitStreamingRollingCountersWithUnreads_phase
    (machine : DeterministicMachine) (n H w base : Nat)
    (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat) (unreads : List ReadOnlySymbol)
    (state : FiniteCachedVisitRollingCounterState
      (cachedInputMachine machine).State H w m) :
    (runFiniteCachedVisitStreamingRollingCountersWithUnreads machine n H w
      base hbound boundaries unreads state).phase =
      runFiniteCachedVisitStreamingWithUnreads machine n H w base hbound
        unreads state.phase := by
  induction unreads generalizing state with
  | nil => rfl
  | cons unread rest ih =>
      rw [runFiniteCachedVisitStreamingRollingCountersWithUnreads_cons,
        runFiniteCachedVisitStreamingWithUnreads_cons]
      exact ih _

/-- Exact agreement with the external input supplies the terminal-marker
condition needed by one live streaming transition. -/
theorem finiteCachedVisitStreaming_endCondition_of_symbolAgreement
    (machine : DeterministicMachine) (input : List Bool)
    {H w : Nat}
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (unread : ReadOnlySymbol)
    (hread : readOnlySymbol input live.inputHead.val = unread) :
    cachedLocalStepNeedsUnread machine live = true →
      ¬ live.inputHead.val < input.length → unread = .rightEnd := by
  intro _ hhead
  calc
    unread = readOnlySymbol input live.inputHead.val := hread.symm
    _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le input
      live.inputHead.val (Nat.le_of_not_gt hhead)

/-- On every accepted finite replay, the online rolling vector is exactly the
standalone one-pass vector over the materialized cached-machine run.  Thus the
counters are not a post-processing annotation: they are updated in the same
live transitions and nevertheless recover the established semantic pass. -/
theorem runFiniteCachedVisitStreamingRollingCountersWithUnreads_counters_eq_onePass
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (unreads : List ReadOnlySymbol)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State H w)
    (hlength : remaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input H w base
      unreads live)
    (hreplay : finiteCachedVisitReplay machine H w base hbound unreads live =
      .completed final) :
    (runFiniteCachedVisitStreamingRollingCountersWithUnreads machine
      input.length H w base hbound boundaries unreads
        ⟨.running remaining live, counters⟩).counters =
      onePassBoundedCrossingCounterVectorFrom (cachedInputMachine machine)
        input boundaries (materializeLocalReplayState base live)
          unreads.length counters := by
  induction unreads generalizing remaining live counters final with
  | nil => simp [FiniteCachedVisitSymbolsAgree] at hagree
  | cons unread unreads ih =>
      cases unreads with
      | nil =>
          have hlast : remaining.val = 1 := by simpa using hlength
          simp only [FiniteCachedVisitSymbolsAgree] at hagree
          have hend :=
            finiteCachedVisitStreaming_endCondition_of_symbolAgreement
              machine input live unread hagree
          simp only [finiteCachedVisitReplay] at hreplay
          cases hlocal : finiteLocalCachedFinalStep machine H w base unread
              live with
          | stepped next =>
              rw [hlocal] at hreplay
              cases hreplay
              rw [runFiniteCachedVisitStreamingRollingCountersWithUnreads_cons]
              simp only [streamingAnswerForPhaseUnread]
              rw [finiteCachedVisitStreamingRollingCounterStep_final_global
                machine input input.length H w base hbound boundaries remaining
                live _ counters unread hlast hagree hend hlocal]
              rfl
          | halted outcome =>
              rw [hlocal] at hreplay
              cases hreplay
              rw [runFiniteCachedVisitStreamingRollingCountersWithUnreads_cons]
              simp only [streamingAnswerForPhaseUnread]
              rw [finiteCachedVisitStreamingRollingCounterStep_final_halted_global
                machine input input.length H w base hbound boundaries remaining
                live counters unread outcome hlast hend hlocal]
              rfl
          | inputHorizonExceeded => simp [hlocal] at hreplay
          | workHorizonExceeded => simp [hlocal] at hreplay
      | cons nextUnread rest =>
          have hmore : 1 < remaining.val := by
            rw [hlength]
            simp
          simp only [FiniteCachedVisitSymbolsAgree] at hagree
          rcases hagree with ⟨hread, htailAgree⟩
          have hend :=
            finiteCachedVisitStreaming_endCondition_of_symbolAgreement
              machine input live unread hread
          simp only [finiteCachedVisitReplay] at hreplay
          cases hlocal : finiteLocalCachedStep machine H w base unread live with
          | inside next =>
              rw [hlocal] at htailAgree hreplay
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: rest).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              have hmaterialize := finiteLocalCachedStep_inside_materialize
                machine unread live next input hread hlocal
              rw [runFiniteCachedVisitStreamingRollingCountersWithUnreads_cons]
              simp only [streamingAnswerForPhaseUnread]
              rw [finiteCachedVisitStreamingRollingCounterStep_inside_global
                machine input input.length H w base hbound boundaries remaining
                live next counters unread hmore hread hend hlocal]
              rw [ih (spendVisitStep remaining) next _ final htailLength
                htailAgree hreplay]
              change
                onePassBoundedCrossingCounterVectorFrom
                    (cachedInputMachine machine) input boundaries
                    (materializeLocalReplayState base next)
                    (nextUnread :: rest).length
                    (bumpBoundedCrossingCounterVector boundaries
                      (materializeLocalReplayState base live).workHead
                      (step (cachedInputMachine machine) input
                        (materializeLocalReplayState base live)).workHead
                      counters) =
                  onePassBoundedCrossingCounterVectorFrom
                    (cachedInputMachine machine) input boundaries
                    (step (cachedInputMachine machine) input
                      (materializeLocalReplayState base live))
                    (nextUnread :: rest).length
                    (bumpBoundedCrossingCounterVector boundaries
                      (materializeLocalReplayState base live).workHead
                      (step (cachedInputMachine machine) input
                        (materializeLocalReplayState base live)).workHead
                      counters)
              rw [hmaterialize]
          | halted outcome =>
              rw [hlocal] at htailAgree hreplay
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: rest).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              have hhalt :=
                (finiteLocalCachedStep_eq_halted_iff machine unread live
                  outcome).mp hlocal
              have hglobalHalt : (cachedInputMachine machine).halt
                  (materializeLocalReplayState base live).state =
                    some outcome := by
                simpa [materializeLocalReplayState] using hhalt
              have hstutter := step_of_halted (cachedInputMachine machine)
                input (materializeLocalReplayState base live) outcome
                  hglobalHalt
              rw [runFiniteCachedVisitStreamingRollingCountersWithUnreads_cons]
              simp only [streamingAnswerForPhaseUnread]
              rw [finiteCachedVisitStreamingRollingCounterStep_halted_global
                machine input input.length H w base hbound boundaries remaining
                live counters unread outcome hmore hend hlocal]
              rw [ih (spendVisitStep remaining) live _ final htailLength
                htailAgree hreplay]
              change
                onePassBoundedCrossingCounterVectorFrom
                    (cachedInputMachine machine) input boundaries
                    (materializeLocalReplayState base live)
                    (nextUnread :: rest).length
                    (bumpBoundedCrossingCounterVector boundaries
                      (materializeLocalReplayState base live).workHead
                      (step (cachedInputMachine machine) input
                        (materializeLocalReplayState base live)).workHead
                      counters) =
                  onePassBoundedCrossingCounterVectorFrom
                    (cachedInputMachine machine) input boundaries
                    (step (cachedInputMachine machine) input
                      (materializeLocalReplayState base live))
                    (nextUnread :: rest).length
                    (bumpBoundedCrossingCounterVector boundaries
                      (materializeLocalReplayState base live).workHead
                      (step (cachedInputMachine machine) input
                        (materializeLocalReplayState base live)).workHead
                      counters)
              rw [hstutter]
          | workHeadExit => simp [hlocal] at htailAgree
          | inputHorizonExceeded => simp [hlocal] at htailAgree

/-- The same exact counter conclusion, phrased directly from acceptance of the
streaming comparison run rather than from its underlying replay result. -/
theorem runFiniteCachedVisitStreamingRollingCountersWithUnreads_counters_eq_onePass_of_completed
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (unreads : List ReadOnlySymbol)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State H w)
    (hlength : remaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input H w base
      unreads live)
    (hstream : runFiniteCachedVisitStreamingWithUnreads machine input.length H
      w base hbound unreads (.running remaining live) = .completed final) :
    (runFiniteCachedVisitStreamingRollingCountersWithUnreads machine
      input.length H w base hbound boundaries unreads
        ⟨.running remaining live, counters⟩).counters =
      onePassBoundedCrossingCounterVectorFrom (cachedInputMachine machine)
        input boundaries (materializeLocalReplayState base live)
          unreads.length counters := by
  have hnonempty : unreads ≠ [] := by
    intro hempty
    subst unreads
    simp [FiniteCachedVisitSymbolsAgree] at hagree
  have hrespect : FiniteCachedVisitUnreadsRespectEnd machine input.length H w
      base unreads live :=
    finiteCachedVisitSymbolsAgree_implies_respectEnd machine input unreads live
      hagree
  have hrun := runFiniteCachedVisitStreamingWithUnreads_eq_replay
    machine input.length hbound unreads remaining live hnonempty hlength hrespect
  have hmapped : streamingStateOfFiniteReplayResult
        (finiteCachedVisitReplay machine H w base hbound unreads live) =
      .completed final := hrun.symm.trans hstream
  have hreplay : finiteCachedVisitReplay machine H w base hbound unreads live =
      .completed final := by
    cases hresult : finiteCachedVisitReplay machine H w base hbound unreads live
        with
    | completed replayFinal =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
        subst replayFinal
        rfl
    | emptyTrace =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
    | intermediateWorkHeadExit =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
    | inputHorizonExceeded =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
    | finalWorkHorizonExceeded =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
  exact
    runFiniteCachedVisitStreamingRollingCountersWithUnreads_counters_eq_onePass
      machine input hbound boundaries unreads remaining live counters final
        hlength hagree hreplay

/-- Accepted rolling streaming visits recover the counter projection of the
existing fused fixed-visit pass exactly. -/
theorem runFiniteCachedVisitStreamingRollingCountersWithUnreads_counters_eq_onePassFixedAlphaVisitFrom_of_completed
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1) {m : Nat}
    (boundaries : Fin m → Nat)
    (unreads : List ReadOnlySymbol)
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (counters : BoundedCrossingCounterVector H m)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State H w)
    (hlength : remaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input H w base
      unreads live)
    (hstream : runFiniteCachedVisitStreamingWithUnreads machine input.length H
      w base hbound unreads (.running remaining live) = .completed final) :
    (runFiniteCachedVisitStreamingRollingCountersWithUnreads machine
      input.length H w base hbound boundaries unreads
        ⟨.running remaining live, counters⟩).counters =
      (onePassFixedAlphaVisitFrom (cachedInputMachine machine) input base w
        boundaries (materializeLocalReplayState base live) unreads.length
          counters).counters := by
  rw [onePassFixedAlphaVisitFrom_counters]
  exact
    runFiniteCachedVisitStreamingRollingCountersWithUnreads_counters_eq_onePass_of_completed
      machine input hbound boundaries unreads remaining live counters final
        hlength hagree hstream

end OneTapeMagnification
end Frontier
end Pnp4
