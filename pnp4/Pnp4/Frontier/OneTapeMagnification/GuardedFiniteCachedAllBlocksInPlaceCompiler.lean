import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AcceptedAllBlocksMasterOrderExecution
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceOperational
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceCanonicalCheck

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Master-guarded fused all-block compiler

This module applies the static schedule master guard to the genuinely fused
all-block verifier carrying the rolling two-window state.  The checked wrapper
is read-once on every input.  On the canonical accepted input, erasure to the
already verified outer machine identifies the fused query trace with the
schedule master order, so the guard is semantically invisible without an
external reflection or follows-master premise.
-/

local instance cachedInputMachineStateDecidableEqForGuardedFusedAllBlocks
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Schedule specialization of the total fused all-block compiler. -/
def compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    LayeredQueryProgram n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled)) :=
  compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
    machine alpha (fun block => timedAlphaBlockVisits block scheduled)

/-- The fused schedule compiler guarded by its clipped stable-grouped master
order. -/
def compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    LayeredQueryProgram n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled)) :=
  LayeredQueryProgram.guardByMasterOrder
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)

/-- Schedule geometry makes the master-guarded fused compiler read-once. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
      (n := n) machine alpha scheduled hmonotone).IsReadOnce := by
  apply LayeredQueryProgram.guardByMasterOrder_isReadOnce
  exact finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
    (n := n) scheduled hchained hmonotone

/-- Exact width of the master-guarded fused compiler. -/
@[simp]
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
      (n := n) machine alpha scheduled hmonotone).width =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine alpha scheduled).width *
        (finiteCachedTimedAlphaScheduleMasterQueryOrder
          (n := n) scheduled hmonotone).length.succ := by
  exact LayeredQueryProgram.guardByMasterOrder_width _ _

/-- Bit budget after adjoining the finite master cursor to the fused state. -/
def finiteCachedTimedAlphaScheduleMasterGuardedInPlaceRollingBitBudget
    (machine : DeterministicMachine) {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) : Nat :=
  finiteCachedAllBlocksInPlaceRollingCompiledBitBudget machine
      (fun block => timedAlphaBlockVisits block scheduled) +
    Nat.clog 2
      (finiteCachedTimedAlphaScheduleMasterQueryOrder
        (n := n) scheduled hmonotone).length.succ

/-- The guarded cursor costs only the ceiling-logarithm of its number of
positions on top of the existing fused-state budget. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_width_le_two_pow
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
      (n := n) machine alpha scheduled hmonotone).width <=
      2 ^ finiteCachedTimedAlphaScheduleMasterGuardedInPlaceRollingBitBudget
        (n := n) machine scheduled hmonotone := by
  rw [compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_width]
  unfold finiteCachedTimedAlphaScheduleMasterGuardedInPlaceRollingBitBudget
  apply mul_le_two_pow_add
  · exact
      compileAdaptiveFiniteCachedTimedAlphaScheduleInPlaceRollingTotal_width_le_two_pow
        machine hb alpha scheduled hschedule
  · exact le_two_pow_clog_two _

/-- Total checked guarded fused compiler.  Bad schedules or nonmonotone input
endpoints select a query-free rejection program. -/
def compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    LayeredQueryProgram n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled)) :=
  if _hschedule : timedAlphaVisitScheduleCheck
      (cachedInputMachine machine) alpha scheduled = true then
    if hmonotone : timedAlphaScheduledVisitsInputMonotoneCheck
        scheduled = true then
      compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
        machine alpha scheduled
        ((timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
          scheduled).1 hmonotone)
    else
      LayeredQueryProgram.constantReject n
        (finiteCachedAllBlocksFuel
          (fun block => timedAlphaBlockVisits block scheduled))
  else
    LayeredQueryProgram.constantReject n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled))

/-- The total checked fused compiler is read-once for every schedule and
every Boolean input. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine alpha scheduled).IsReadOnce := by
  unfold
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
  split
  · rename_i hscheduleCheck
    split
    · rename_i hmonotoneCheck
      have hschedule :=
        (timedAlphaVisitScheduleCheck_eq_true_iff
          (cachedInputMachine machine) alpha scheduled).1 hscheduleCheck
      have hmonotone :=
        (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
          scheduled).1 hmonotoneCheck
      obtain ⟨_syntactic, _finalCursor, _visitsSoFar, _hfold, _hfinish,
        hchained⟩ := hschedule
      exact
        compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_isReadOnce
          machine alpha scheduled hchained hmonotone
    · exact LayeredQueryProgram.constantReject_isReadOnce _ _
  · exact LayeredQueryProgram.constantReject_isReadOnce _ _

/-- Validity and monotonicity reduce the total wrapper to the guarded fused
compiler. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eq_guarded_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine alpha scheduled =
      compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
        machine alpha scheduled hmonotone := by
  have hscheduleCheck : timedAlphaVisitScheduleCheck
      (cachedInputMachine machine) alpha scheduled = true :=
    (timedAlphaVisitScheduleCheck_eq_true_iff
      (cachedInputMachine machine) alpha scheduled).2 hschedule
  have hmonotoneCheck : timedAlphaScheduledVisitsInputMonotoneCheck
      scheduled = true :=
    (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff scheduled).2
      hmonotone
  unfold
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
  rw [dif_pos hscheduleCheck, dif_pos hmonotoneCheck]

/-- Exact total-wrapper width on the valid branch. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_width_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine alpha scheduled).width =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine alpha scheduled).width *
        (finiteCachedTimedAlphaScheduleMasterQueryOrder
          (n := n) scheduled hmonotone).length.succ := by
  rw [compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eq_guarded_of_valid
    machine alpha scheduled hschedule hmonotone]
  exact
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_width
      machine alpha scheduled hmonotone

/-- Power-of-two width bound for the valid branch of the total wrapper. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_width_le_two_pow_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine alpha scheduled).width <=
      2 ^ finiteCachedTimedAlphaScheduleMasterGuardedInPlaceRollingBitBudget
        (n := n) machine scheduled hmonotone := by
  rw [compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eq_guarded_of_valid
    machine alpha scheduled hschedule hmonotone]
  exact
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_width_le_two_pow
      machine hb alpha scheduled hschedule hmonotone

/-- Generic semantic preservation of the fused compiler by the master guard
on any input whose execution follows the supplied master order. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_eq_base_of_follows
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (input : Fin n -> Bool)
    (hfollows : LayeredQueryProgram.ExecutionQueriesFollowMaster
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled)
      (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
      input) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
        machine alpha scheduled hmonotone).eval input =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled).eval input := by
  exact LayeredQueryProgram.guardByMasterOrder_eval_eq_of_follows
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
    input hfollows

/-- Generic preservation for the valid branch of the total checked wrapper. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_base_of_follows
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (input : Fin n -> Bool)
    (hfollows : LayeredQueryProgram.ExecutionQueriesFollowMaster
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled)
      (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
      input) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled).eval input =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled).eval input := by
  rw [compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eq_guarded_of_valid
    machine alpha scheduled hschedule hmonotone]
  exact
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_eq_base_of_follows
      machine alpha scheduled hmonotone input hfollows

/-- Exact fused coordinate traces erase to exact coordinate traces of the
outer replay verifier.  The rolling counters and flags never affect halting,
input requests, query selection, or the erased transition. -/
theorem finiteCachedAllBlocksInPlaceRollingExactAdaptiveQueryOrder_erase
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (input : Fin n -> Bool)
    {steps : Nat}
    {start target : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits}
    {queries : List (Fin n)}
    (trace :
      let fused :=
        finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
          machine n alpha blockVisits
      FiniteStreamingVerifier.ExactAdaptiveQueryOrder fused
        (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n)
        input steps start queries target) :
    let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine n alpha blockVisits
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
      (fun bit => .bit bit)
      (finiteCachedAllBlocksAdaptiveQueryIndex? machine n)
      input steps
      (eraseFiniteCachedAllBlocksInPlaceRolling machine start) queries
      (eraseFiniteCachedAllBlocksInPlaceRolling machine target) := by
  dsimp only at trace ⊢
  let fused :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine n alpha blockVisits
  let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine n alpha blockVisits
  let fusedSelector : fused.State -> Option (Fin n) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n
  let outerSelector : outer.State -> Option (Fin n) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine n
  let erase : fused.State -> outer.State :=
    eraseFiniteCachedAllBlocksInPlaceRolling machine
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder fused
    (fun bit => .bit bit) fusedSelector input steps start queries target
      at trace
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
    (fun bit => .bit bit) outerSelector input steps (erase start) queries
      (erase target)
  have hfusedTargetHalted : fused.halted target = true :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.target_halted fused
      (fun bit => .bit bit) fusedSelector input trace
  have houterTargetHalted : outer.halted (erase target) = true := by
    change finiteCachedAllBlocksInPlaceRollingHalted machine target = true
      at hfusedTargetHalted
    change finiteCachedAllBlocksHalted
      (eraseFiniteCachedAllBlocksInPlaceRolling machine target) = true
    rw [← finiteCachedAllBlocksInPlaceRollingHalted_erase machine target]
    exact hfusedTargetHalted
  have terminal : FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
      (fun bit => .bit bit) outerSelector input 0 (erase target) []
        (erase target) :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.halted _
      houterTargetHalted
  have hhalted : forall state, fused.halted state = false ->
      outer.halted (erase state) = false := by
    intro state hstate
    change finiteCachedAllBlocksInPlaceRollingHalted machine state = false
      at hstate
    change finiteCachedAllBlocksHalted
      (eraseFiniteCachedAllBlocksInPlaceRolling machine state) = false
    rw [← finiteCachedAllBlocksInPlaceRollingHalted_erase machine state]
    exact hstate
  have hrequests : forall state, fused.halted state = false ->
      outer.requestsInput (erase state) = fused.requestsInput state := by
    intro state _
    exact (finiteCachedAllBlocksInPlaceRollingRequestsInput_erase
      machine n state).symm
  have hselector : forall state, fused.halted state = false ->
      outerSelector (erase state) = fusedSelector state := by
    intro state _
    exact (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?_erase
      machine n state).symm
  have hstep : forall state supplied, fused.halted state = false ->
      outer.step (erase state) supplied = erase (fused.step state supplied) := by
    intro state supplied _
    exact (eraseFiniteCachedAllBlocksInPlaceRolling_totalStep machine n alpha
      blockVisits state supplied).symm
  have mapped :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.map_append fused outer
      (fun bit => .bit bit) fusedSelector outerSelector input erase hhalted
        hrequests hselector hstep trace terminal
  simpa using mapped

/-- On the canonical accepted input, the fused compiler exposes exactly the
same static grouped master order as its erased outer replay machine. -/
theorem compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_queryTrace_eq_master_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    let hmonotone :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        (cachedInputMachine machine) input alpha scheduled haccepted
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled).queryTrace
        (fun index => input.get index) =
      finiteCachedTimedAlphaScheduleMasterQueryOrder
        scheduled hmonotone := by
  dsimp only
  let blockVisits := fun block => timedAlphaBlockVisits block scheduled
  let fused :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits
  let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let fusedSelector : fused.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
      machine input.length
  let outerSelector : outer.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  let fuel := finiteCachedAllBlocksFuel blockVisits
  have hcompletion :=
    finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_exists_completed_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  change exists fold : InPlaceTwoWindowFoldState T b,
      fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits fuel
        fused.start = .completed fold at hcompletion
  obtain ⟨fold, hcore⟩ := hcompletion
  have hhalted : fused.halted
      (fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits fuel
        fused.start) = true := by
    rw [hcore]
    rfl
  have htotal : forall state, fused.requestsInput state = true ->
      exists index, fusedSelector state = some index := by
    intro state hrequest
    exact finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?_total
      machine input.length state hrequest
  obtain ⟨steps, queries, hsteps, fusedTrace⟩ :=
    FiniteStreamingVerifier.exists_exactAdaptiveQueryOrder_of_inputDrivenCore_halted
      fused (fun bit => .bit bit) fusedSelector inputBits htotal fuel
        fused.start hhalted
  have erasedTrace :=
    finiteCachedAllBlocksInPlaceRollingExactAdaptiveQueryOrder_erase
      machine alpha blockVisits inputBits fusedTrace
  have herasedStart :
      eraseFiniteCachedAllBlocksInPlaceRolling machine fused.start =
        outer.start := by
    change eraseFiniteCachedAllBlocksInPlaceRolling machine
        (finiteCachedAllBlocksInPlaceRollingTotalStart machine alpha
          blockVisits) =
      finiteCachedAllBlocksTotalStart machine alpha blockVisits
    exact eraseFiniteCachedAllBlocksInPlaceRolling_totalStart machine alpha
      blockVisits
  rw [herasedStart] at erasedTrace
  have erasedTrace' : FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
      (fun bit => .bit bit) outerSelector inputBits steps outer.start queries
      (eraseFiniteCachedAllBlocksInPlaceRolling machine
        (fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits
          fuel fused.start)) := by
    simpa [fused, outer, fusedSelector, outerSelector, inputBits] using
      erasedTrace
  have hreplay : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) := by
    intro block
    exact (haccepted block).2
  have outerTrace :=
    finiteCachedAllBlocks_exactAdaptiveQueryOrder_of_replayAccepted
      machine input alpha blockVisits hreplay
  dsimp only at outerTrace
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder outer
      (fun bit => .bit bit) outerSelector inputBits fuel outer.start
      ((List.finRange (T / b + 1)).flatMap fun block =>
        finiteCachedBlockVisitListAdvertisedQueryOrder input.length
          (blockVisits block)) .completed at outerTrace
  have hqueries : queries =
      (List.finRange (T / b + 1)).flatMap (fun block =>
        finiteCachedBlockVisitListAdvertisedQueryOrder input.length
          (blockVisits block)) :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.queries_eq_of_same_start
      outer (fun bit => .bit bit) outerSelector inputBits erasedTrace'
        outerTrace
  have hfusedQueryTrace :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.compileAdaptive_queryTrace_eq
      fused (fun bit => .bit bit) .rightEnd fusedSelector inputBits
        fusedTrace hsteps
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) input alpha scheduled haccepted
  have hmaster := finiteCachedTimedAlphaScheduleMasterQueryOrder_eq_blockVisits
    (n := input.length) scheduled hmonotone
  calc
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled).queryTrace inputBits =
        queries := by
          simpa [compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal,
            blockVisits, fused, fusedSelector, inputBits, fuel] using
              hfusedQueryTrace
    _ = (List.finRange (T / b + 1)).flatMap (fun block =>
        finiteCachedBlockVisitListAdvertisedQueryOrder input.length
          (timedAlphaBlockVisits block scheduled)) := by
      simpa [blockVisits] using hqueries
    _ = finiteCachedTimedAlphaScheduleMasterQueryOrder
        scheduled hmonotone := hmaster.symm

/-- Accepted schedule semantics discharges follows-master for the fused
compiler on the canonical input. -/
theorem finiteCachedTimedAlphaScheduleInPlaceRollingExecutionQueriesFollowMaster_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    let hmonotone :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        (cachedInputMachine machine) input alpha scheduled haccepted
    LayeredQueryProgram.ExecutionQueriesFollowMaster
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled)
      (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
      (fun index => input.get index) := by
  dsimp only
  apply LayeredQueryProgram.executionQueriesFollowMaster_of_queryTrace_eq
  exact
    compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_queryTrace_eq_master_of_acceptedFromBlank
      machine input alpha scheduled haccepted

/-- On a valid accepted schedule and its canonical finite input, the total
master guard is observationally invisible around the fused compiler.  No
reflection or follows-master premise remains. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_base_of_valid_acceptedFromBlank_canonical
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := input.length) machine alpha scheduled).eval
          (fun index => input.get index) := by
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) input alpha scheduled haccepted
  apply
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_base_of_follows
      machine alpha scheduled hschedule hmonotone
        (fun index => input.get index)
  simpa [hmonotone] using
    finiteCachedTimedAlphaScheduleInPlaceRollingExecutionQueriesFollowMaster_of_acceptedFromBlank
      machine input alpha scheduled haccepted

/-- On a valid accepted schedule and its canonical finite input, the total
master-guarded fused compiler evaluates unconditionally to the established
timed in-place two-window fold Boolean. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_timedAlphaFold_of_valid_acceptedFromBlank_canonical
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) =
      timedAlphaInPlaceTwoWindowFoldCheck
        (cachedInputMachine machine) input alpha scheduled := by
  rw [compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_base_of_valid_acceptedFromBlank_canonical
    machine input alpha scheduled hschedule haccepted]
  let blockVisits := fun block => timedAlphaBlockVisits block scheduled
  have hoperational :=
    compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_eq_inPlace_of_acceptedFromBlank
      machine input alpha blockVisits (by
        simpa [blockVisits] using haccepted)
  simpa [compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal,
    blockVisits, timedAlphaInPlaceTwoWindowFoldCheck,
    timedScheduleBlankBlockSlabs, timedScheduleBlockVisitFamily] using
      hoperational

end OneTapeMagnification
end Frontier
end Pnp4
