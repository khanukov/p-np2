import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListRollingOperational
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceCompiler

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact operational fold carried by the fused all-block verifier

This module identifies the dependent fused execution with the chronological
finite cached in-place fold.  The proof keeps the rolling two-window counter
vector live through every visit and block boundary, so the reached fold is
identified as a whole state rather than only through erasure.
-/

local instance cachedInputMachineStateDecidableEqForInPlaceOperational
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Inject one rolling list state into the active outer block, sending the
list rejection sink to the global rejection sink. -/
def liftFiniteCachedAllBlocksInPlaceRollingListState
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (block : Fin (T / b + 1))
    (allBlockVisitsValid allClosedCutsValid : Bool) :
    FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length (b + b) →
      FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits
  | ⟨.rejected, _⟩ => .rejected
  | state =>
      .active block state allBlockVisitsValid allClosedCutsValid

/-- One nonterminal rolling-list microstep is exactly one fused outer
microstep, with only the dependent block injection and retained flags added. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_one_active
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (initial : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block)
      (blockVisits block).length (b + b))
    (allBlockVisitsValid allClosedCutsValid : Bool)
    (verifierInitialCounters : BoundedCrossingCounterVector T (b + b))
    (input : Fin n → Bool)
    (hlive : finiteCachedBlockVisitListRollingHalted initial = false) :
    let listVerifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
        alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) (hentries block)
          (advertisedBlockTwoWindowBoundaries block) verifierInitialCounters
    let outerVerifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine n alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n)
        input 1
        (.active block initial allBlockVisitsValid allClosedCutsValid) =
      liftFiniteCachedAllBlocksInPlaceRollingListState machine alpha
        blockVisits block allBlockVisitsValid allClosedCutsValid
        (listVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n)
          input 1 initial) := by
  dsimp only
  have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true :=
    (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
      alpha blockVisits).2 hentries
  rcases initial with ⟨listState, counters⟩
  cases listState with
  | completed slab =>
      simp [finiteCachedBlockVisitListRollingHalted,
        finiteCachedBlockVisitListHalted] at hlive
  | rejected =>
      simp [finiteCachedBlockVisitListRollingHalted,
        finiteCachedBlockVisitListHalted] at hlive
  | active cursor phase =>
      simp [FiniteStreamingVerifier.inputDrivenCore,
        finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier,
        finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier,
        finiteCachedAllBlocksInPlaceRollingHalted,
        finiteCachedBlockVisitListRollingHalted,
        finiteCachedBlockVisitListHalted,
        finiteCachedAllBlocksInPlaceRollingRequestsInput,
        finiteCachedBlockVisitListRollingRequestsInput,
        finiteCachedBlockVisitListRequestsInput,
        finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?,
        finiteCachedBlockVisitListRollingAdaptiveQueryIndex?,
        finiteCachedBlockVisitListAdaptiveQueryIndex?,
        finiteCachedAllBlocksInPlaceRollingTotalStreamingStep, hcheck,
        finiteCachedAllBlocksInPlaceRollingStreamingStep,
        liftFiniteCachedAllBlocksInPlaceRollingListState]
      rw [← finiteCachedBlockVisitListStreamingRollingCounterStep_listState
        machine n alpha block (blockVisits block) (hentries block)
          (advertisedBlockTwoWindowBoundaries block)
          ⟨.active cursor phase, counters⟩
          (if finiteCachedVisitPhaseRequestsInput machine n phase then
            (finiteCachedVisitAdaptiveQueryIndex? machine n phase).map
              (fun index => ReadOnlySymbol.bit (input index))
          else none)]
      generalize finiteCachedBlockVisitListStreamingRollingCounterStep machine
        n alpha block (blockVisits block) (hentries block)
          (advertisedBlockTwoWindowBoundaries block)
          ⟨.active cursor phase, counters⟩
          (if finiteCachedVisitPhaseRequestsInput machine n phase then
            (finiteCachedVisitAdaptiveQueryIndex? machine n phase).map
              (fun index => ReadOnlySymbol.bit (input index))
          else none) = next
      rcases next with ⟨nextListState, nextCounters⟩
      cases nextListState <;> rfl

/-- Under strict-prefix list liveness, an arbitrary rolling-list segment
embeds exactly into the active fused block. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_active_eq_lift_of_live
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (initial : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block)
      (blockVisits block).length (b + b))
    (allBlockVisitsValid allClosedCutsValid : Bool)
    (verifierInitialCounters : BoundedCrossingCounterVector T (b + b))
    (input : Fin n → Bool) (fuel : Nat)
    (hlive : ∀ spent : Nat, spent < fuel + 1 →
      finiteCachedBlockVisitListRollingHalted
        ((finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier
          machine n alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block)
            (advertisedBlockTwoWindowBoundaries block)
              verifierInitialCounters
          ).inputDrivenCore (fun bit => .bit bit)
            (finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n)
            input spent initial) = false) :
    let listVerifier :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
        alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) (hentries block)
          (advertisedBlockTwoWindowBoundaries block)
            verifierInitialCounters
    let outerVerifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine n alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n)
        input (fuel + 1)
        (.active block initial allBlockVisitsValid allClosedCutsValid) =
      liftFiniteCachedAllBlocksInPlaceRollingListState machine alpha
        blockVisits block allBlockVisitsValid allClosedCutsValid
        (listVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n)
          input (fuel + 1) initial) := by
  dsimp only
  let listVerifier :=
    finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
      alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) (hentries block)
        (advertisedBlockTwoWindowBoundaries block) verifierInitialCounters
  let outerVerifier :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine n alpha blockVisits
  let listSelector : listVerifier.State → Option (Fin n) :=
    finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n
  let outerSelector : outerVerifier.State → Option (Fin n) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n
  induction fuel generalizing initial with
  | zero =>
      exact finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_one_active
        machine alpha blockVisits hentries block initial
          allBlockVisitsValid allClosedCutsValid verifierInitialCounters input
            (hlive 0 (by omega))
  | succ fuel ih =>
      have hzero : finiteCachedBlockVisitListRollingHalted initial = false := by
        simpa [listVerifier, FiniteStreamingVerifier.inputDrivenCore] using
          hlive 0 (by omega)
      let next := listVerifier.inputDrivenCore (fun bit => .bit bit)
        listSelector input 1 initial
      have hnextLive : finiteCachedBlockVisitListRollingHalted next = false := by
        simpa [next, listVerifier] using hlive 1 (by omega)
      have hfirst :=
        finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_one_active
          machine alpha blockVisits hentries block initial
            allBlockVisitsValid allClosedCutsValid verifierInitialCounters
              input hzero
      have htailLive : ∀ spent : Nat, spent < fuel + 1 →
          finiteCachedBlockVisitListRollingHalted
            (listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
              input spent next) = false := by
        intro spent hspent
        have horiginal := hlive (1 + spent) (by omega)
        rw [listVerifier.inputDrivenCore_add (fun bit => .bit bit)
          listSelector input 1 spent initial] at horiginal
        simpa [next, listVerifier, listSelector] using horiginal
      have htail := ih next (by
        simpa [listVerifier, listSelector] using htailLive)
      have hfirst' : outerVerifier.inputDrivenCore (fun bit => .bit bit)
          outerSelector input 1
            (.active block initial allBlockVisitsValid allClosedCutsValid) =
          liftFiniteCachedAllBlocksInPlaceRollingListState machine alpha
            blockVisits block allBlockVisitsValid allClosedCutsValid next := by
        simpa [outerVerifier, listVerifier, outerSelector, listSelector,
          next] using hfirst
      rw [outerVerifier.inputDrivenCore_succ_front (fun bit => .bit bit)
        outerSelector input (fuel + 1)
          (.active block initial allBlockVisitsValid allClosedCutsValid)]
      rw [listVerifier.inputDrivenCore_succ_front (fun bit => .bit bit)
        listSelector input (fuel + 1) initial]
      rw [hfirst']
      rcases hnextState : next with ⟨nextListState, nextCounters⟩
      cases nextListState with
      | completed slab =>
          simp [hnextState, finiteCachedBlockVisitListRollingHalted,
            finiteCachedBlockVisitListHalted] at hnextLive
      | rejected =>
          simp [hnextState, finiteCachedBlockVisitListRollingHalted,
            finiteCachedBlockVisitListHalted] at hnextLive
      | active cursor phase =>
          simpa [outerVerifier, listVerifier, outerSelector, listSelector,
            next, hnextState,
            liftFiniteCachedAllBlocksInPlaceRollingListState] using htail

/-- A replay-accepted block advances the fused execution by its exact list
fuel plus one boundary step and installs precisely the executable in-place
block-step state. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_advance_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (fold : InPlaceTwoWindowFoldState T b)
    (block : Fin (T / b + 1))
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)) :
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine input.length alpha blockVisits
    let nextFold := finiteCachedAllBlocksInPlaceRollingBlockStep machine input
      alpha blockVisits hentries fold block
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
        (.active block
          ⟨finiteCachedBlockVisitListStart machine alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block), fold.counters⟩
          fold.allBlockVisitsValid fold.allClosedCutsValid) =
      if hnext : block.val + 1 < T / b + 1 then
        let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
        .active next
          ⟨finiteCachedBlockVisitListStart machine alpha next
            (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
            (blockVisits next) (hentries next), nextFold.counters⟩
          nextFold.allBlockVisitsValid nextFold.allClosedCutsValid
      else
        .completed nextFold := by
  dsimp only
  let blank := blankWorkSlab
    (advertisedBlockWidth alpha.offsets block)
  let listResult := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
    machine input alpha block (advertisedBlockTwoWindowBoundaries block)
      (blockVisits block) (hentries block) blank fold.counters
  let listVerifier :=
    finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
      input.length alpha block blank (blockVisits block) (hentries block)
        (advertisedBlockTwoWindowBoundaries block) fold.counters
  let ordinaryVerifier :=
    finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
      input.length alpha block blank (blockVisits block) (hentries block)
  let outerVerifier :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits
  let listSelector : listVerifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine input.length
  let ordinarySelector : ordinaryVerifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let outerSelector : outerVerifier.State → Option (Fin input.length) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
      machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let listFuel := finiteCachedBlockVisitListFuel (blockVisits block)
  have hlocalCore :=
    finiteCachedBlockVisitListRolling_inputDrivenCore_completed_of_replayAccepted
      machine input alpha block blank (blockVisits block) (hentries block)
        (advertisedBlockTwoWindowBoundaries block) fold.counters haccepted
  change listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
      inputBits listFuel listVerifier.start =
        ⟨.completed listResult.finalSlab, listResult.counters⟩ at hlocalCore
  have ordinaryLive := finiteCachedBlockVisitList_liveBefore_of_replayAccepted
    machine input alpha block blank (blockVisits block) (hentries block)
      haccepted
  change ∀ spent, spent < listFuel →
      finiteCachedBlockVisitListHalted
        (ordinaryVerifier.inputDrivenCore (fun bit => .bit bit)
          ordinarySelector inputBits spent ordinaryVerifier.start) = false
    at ordinaryLive
  have rollingLive : ∀ spent, spent < listFuel →
      finiteCachedBlockVisitListRollingHalted
        (listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
          inputBits spent listVerifier.start) = false := by
    intro spent hspent
    have herase :=
      finiteCachedBlockVisitListRolling_inputDrivenCore_listState machine
        alpha block blank (blockVisits block) (hentries block)
          (advertisedBlockTwoWindowBoundaries block) fold.counters inputBits
            spent listVerifier.start
    change (listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
        inputBits spent listVerifier.start).listState =
      ordinaryVerifier.inputDrivenCore (fun bit => .bit bit)
        ordinarySelector inputBits spent listVerifier.start.listState at herase
    have hstarts : listVerifier.start.listState = ordinaryVerifier.start := by
      rfl
    change finiteCachedBlockVisitListHalted
        (listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
          inputBits spent listVerifier.start).listState = false
    rw [herase, hstarts]
    exact ordinaryLive spent hspent
  have houterLocal : outerVerifier.inputDrivenCore (fun bit => .bit bit)
      outerSelector inputBits listFuel
      (.active block listVerifier.start fold.allBlockVisitsValid
        fold.allClosedCutsValid) =
      .active block
        ⟨.completed listResult.finalSlab, listResult.counters⟩
        fold.allBlockVisitsValid fold.allClosedCutsValid := by
    cases hfuel : listFuel with
    | zero =>
        have hstart : listVerifier.start =
            ⟨.completed listResult.finalSlab, listResult.counters⟩ := by
          simpa [hfuel, FiniteStreamingVerifier.inputDrivenCore] using
            hlocalCore
        simp [FiniteStreamingVerifier.inputDrivenCore, hstart]
    | succ fuel =>
        have hsim :=
          finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_active_eq_lift_of_live
            machine alpha blockVisits hentries block listVerifier.start
              fold.allBlockVisitsValid fold.allClosedCutsValid fold.counters
                inputBits fuel (by
                  intro spent hspent
                  apply rollingLive spent
                  omega)
        have hsim' : outerVerifier.inputDrivenCore (fun bit => .bit bit)
            outerSelector inputBits (fuel + 1)
            (.active block listVerifier.start fold.allBlockVisitsValid
              fold.allClosedCutsValid) =
          liftFiniteCachedAllBlocksInPlaceRollingListState machine alpha
            blockVisits block fold.allBlockVisitsValid
              fold.allClosedCutsValid
              (listVerifier.inputDrivenCore (fun bit => .bit bit)
                listSelector inputBits (fuel + 1) listVerifier.start) := by
          simpa [outerVerifier, listVerifier, outerSelector, listSelector]
            using hsim
        have hlocalCore' : listVerifier.inputDrivenCore
            (fun bit => .bit bit) listSelector inputBits (fuel + 1)
              listVerifier.start =
            ⟨.completed listResult.finalSlab, listResult.counters⟩ := by
          rw [← hfuel]
          exact hlocalCore
        rw [hlocalCore'] at hsim'
        simpa [liftFiniteCachedAllBlocksInPlaceRollingListState] using hsim'
  have hvalid : fixedAlphaBlockVisitReplayCheck
      (cachedInputMachine machine) input alpha block blank
        (blockVisits block) = true :=
    (fixedAlphaBlockVisitReplayCheck_eq_true_iff
      (cachedInputMachine machine) input alpha block blank
        (blockVisits block)).2 haccepted
  let nextFold := finiteCachedAllBlocksInPlaceRollingBlockStep machine input
    alpha blockVisits hentries fold block
  have hnextFold : nextFold =
      finiteCachedAllBlocksInPlaceBoundaryUpdate alpha block true
        fold.allBlockVisitsValid fold.allClosedCutsValid
          listResult.counters := by
    simp [nextFold, finiteCachedAllBlocksInPlaceRollingBlockStep,
      blank, listResult, hvalid]
  change outerVerifier.inputDrivenCore (fun bit => .bit bit) outerSelector
      inputBits (listFuel + 1)
      (.active block listVerifier.start fold.allBlockVisitsValid
        fold.allClosedCutsValid) = _
  rw [outerVerifier.inputDrivenCore_add (fun bit => .bit bit)
    outerSelector inputBits listFuel 1
      (.active block listVerifier.start fold.allBlockVisitsValid
        fold.allClosedCutsValid)]
  rw [houterLocal]
  have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true :=
    (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
      alpha blockVisits).2 hentries
  simp [outerVerifier, FiniteStreamingVerifier.inputDrivenCore,
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier,
    finiteCachedAllBlocksInPlaceRollingHalted,
    finiteCachedAllBlocksInPlaceRollingRequestsInput,
    finiteCachedBlockVisitListRequestsInput,
    finiteCachedAllBlocksInPlaceRollingTotalStreamingStep, hcheck,
    finiteCachedAllBlocksInPlaceRollingStreamingStep, nextFold, hnextFold]

/-- The executable in-place fold composes across adjacent fuel intervals. -/
theorem finiteCachedAllBlocksInPlaceRollingFoldFrom_add
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (next first second : Nat) (state : InPlaceTwoWindowFoldState T b) :
    finiteCachedAllBlocksInPlaceRollingFoldFrom machine input alpha
        blockVisits hentries next (first + second) state =
      finiteCachedAllBlocksInPlaceRollingFoldFrom machine input alpha
        blockVisits hentries (next + first) second
        (finiteCachedAllBlocksInPlaceRollingFoldFrom machine input alpha
          blockVisits hentries next first state) := by
  induction first generalizing next state with
  | zero => simp [finiteCachedAllBlocksInPlaceRollingFoldFrom]
  | succ first ih =>
      simp only [Nat.succ_add,
        finiteCachedAllBlocksInPlaceRollingFoldFrom]
      by_cases hblock : next < T / b + 1
      · simp only [dif_pos hblock]
        have htail := ih (next + 1)
          (finiteCachedAllBlocksInPlaceRollingBlockStep machine input alpha
            blockVisits hentries state ⟨next, hblock⟩)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          htail
      · simp only [dif_neg hblock]
        have hlater : ¬ next + Nat.succ first < T / b + 1 := by omega
        cases second with
        | zero => rfl
        | succ second =>
            simp [finiteCachedAllBlocksInPlaceRollingFoldFrom, hlater]

/-- Exact fused prefix invariant.  After the first `count` block budgets,
the active state carries precisely the corresponding executable prefix fold;
after all block budgets, that very fold is globally completed. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_prefix_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (count : Nat) (hcount : count ≤ T / b + 1)
    (haccepted : ∀ block : Fin (T / b + 1), block.val < count →
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block)) :
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine input.length alpha blockVisits
    let fold := finiteCachedAllBlocksInPlaceRollingFoldFrom machine input
      alpha blockVisits hentries 0 count
        (initialInPlaceTwoWindowFoldState T b)
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksPrefixFuel blockVisits count) verifier.start =
      if hactive : count < T / b + 1 then
        let block : Fin (T / b + 1) := ⟨count, hactive⟩
        .active block
          ⟨finiteCachedBlockVisitListStart machine alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block), fold.counters⟩
          fold.allBlockVisitsValid fold.allClosedCutsValid
      else
        .completed fold := by
  dsimp only
  let verifier :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
      machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksPrefixFuel blockVisits count) verifier.start = _
  revert hcount haccepted
  induction count with
  | zero =>
      intro _ _
      have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
          alpha blockVisits = true :=
        (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
          alpha blockVisits).2 hentries
      simp [verifier, selector, inputBits,
        FiniteStreamingVerifier.inputDrivenCore,
        finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier,
        finiteCachedAllBlocksInPlaceRollingTotalStart, hcheck,
        finiteCachedAllBlocksInPlaceRollingStart,
        finiteCachedAllBlocksInPlaceRollingFoldFrom,
        initialInPlaceTwoWindowFoldState]
  | succ count ih =>
      intro hcount haccepted
      have hlt : count < T / b + 1 := by omega
      let block : Fin (T / b + 1) := ⟨count, hlt⟩
      let foldBefore := finiteCachedAllBlocksInPlaceRollingFoldFrom machine
        input alpha blockVisits hentries 0 count
          (initialInPlaceTwoWindowFoldState T b)
      let foldAfter := finiteCachedAllBlocksInPlaceRollingFoldFrom machine
        input alpha blockVisits hentries 0 (count + 1)
          (initialInPlaceTwoWindowFoldState T b)
      have ihState : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits
          (finiteCachedAllBlocksPrefixFuel blockVisits count)
          verifier.start =
        .active block
          ⟨finiteCachedBlockVisitListStart machine alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block), foldBefore.counters⟩
          foldBefore.allBlockVisitsValid foldBefore.allClosedCutsValid := by
        have hprevious := ih (by omega) (fun previous hprevious =>
          haccepted previous (by omega))
        simpa [hlt, block, foldBefore] using hprevious
      have hprefix := finiteCachedAllBlocksPrefixFuel_succ
        blockVisits count hlt
      have hfoldAfter : foldAfter =
          finiteCachedAllBlocksInPlaceRollingBlockStep machine input alpha
            blockVisits hentries foldBefore block := by
        have hcompose := finiteCachedAllBlocksInPlaceRollingFoldFrom_add
          machine input alpha blockVisits hentries 0 count 1
            (initialInPlaceTwoWindowFoldState T b)
        change finiteCachedAllBlocksInPlaceRollingFoldFrom machine input alpha
            blockVisits hentries 0 (count + 1)
              (initialInPlaceTwoWindowFoldState T b) = _
        rw [hcompose]
        simp [finiteCachedAllBlocksInPlaceRollingFoldFrom, hlt, block,
          foldBefore]
      have hblock :=
        finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_advance_of_replayAccepted
          machine input alpha blockVisits hentries foldBefore block
            (haccepted block (by simp [block]))
      have hblock' : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits
          (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
          (.active block
            ⟨finiteCachedBlockVisitListStart machine alpha block
              (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
              (blockVisits block) (hentries block), foldBefore.counters⟩
            foldBefore.allBlockVisitsValid foldBefore.allClosedCutsValid) =
        if hnext : count + 1 < T / b + 1 then
          let next : Fin (T / b + 1) := ⟨count + 1, hnext⟩
          .active next
            ⟨finiteCachedBlockVisitListStart machine alpha next
              (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
              (blockVisits next) (hentries next), foldAfter.counters⟩
            foldAfter.allBlockVisitsValid foldAfter.allClosedCutsValid
        else
          .completed foldAfter := by
        simpa [verifier, selector, inputBits, block, hfoldAfter] using hblock
      have hresult : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits
          (finiteCachedAllBlocksPrefixFuel blockVisits (count + 1))
          verifier.start =
        if hnext : count + 1 < T / b + 1 then
          let next : Fin (T / b + 1) := ⟨count + 1, hnext⟩
          .active next
            ⟨finiteCachedBlockVisitListStart machine alpha next
              (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
              (blockVisits next) (hentries next), foldAfter.counters⟩
            foldAfter.allBlockVisitsValid foldAfter.allClosedCutsValid
        else
          .completed foldAfter := by
        calc
          verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits (count + 1))
              verifier.start =
            verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits count +
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1))
              verifier.start :=
            congrArg (fun fuel => verifier.inputDrivenCore
              (fun bit => .bit bit) selector inputBits fuel verifier.start)
              hprefix
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector
              inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              (verifier.inputDrivenCore (fun bit => .bit bit) selector
                inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                  verifier.start) :=
            verifier.inputDrivenCore_add (fun bit => .bit bit) selector
              inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
                  verifier.start
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector
              inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              (.active block
                ⟨finiteCachedBlockVisitListStart machine alpha block
                  (blankWorkSlab
                    (advertisedBlockWidth alpha.offsets block))
                  (blockVisits block) (hentries block), foldBefore.counters⟩
                foldBefore.allBlockVisitsValid
                  foldBefore.allClosedCutsValid) := by rw [ihState]
          _ = _ := hblock'
      simpa only [Nat.succ_eq_add_one, foldAfter] using hresult

/-- Simultaneous replay acceptance identifies the completed fused state with
the full executable rolling fold, with no existential reached-fold residual. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (haccepted : ∀ block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block)) :
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start =
      .completed
        (finiteCachedAllBlocksInPlaceRollingFold machine input alpha
          blockVisits hentries) := by
  have hprefix :=
    finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_prefix_of_replayAccepted
      machine input alpha blockVisits hentries (T / b + 1) le_rfl
        (fun block _ => haccepted block)
  rw [finiteCachedAllBlocksPrefixFuel_all blockVisits] at hprefix
  simpa [finiteCachedAllBlocksInPlaceRollingFold] using hprefix

/-- Accepted blank-slab blocks discharge geometry and identify the literal
reached fused state with the executable rolling fold. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : ∀ block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
          (blockVisits block)) :
    let hentries := fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start =
      .completed
        (finiteCachedAllBlocksInPlaceRollingFold machine input alpha
          blockVisits hentries) := by
  exact
    finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_of_replayAccepted
      machine input alpha blockVisits
        (fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank machine input
          alpha blockVisits haccepted)
        (fun block => (haccepted block).2)

/-- Exact reached-fold theorem in the established semantic API: the actual
fused execution completes with `inPlaceTwoWindowBlockFold` itself. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_eq_inPlace_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : ∀ block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
          (blockVisits block)) :
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start =
      .completed
        (inPlaceTwoWindowBlockFold (cachedInputMachine machine) input alpha
          (fun block =>
            blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          blockVisits) := by
  dsimp only
  let hentries := fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
    machine input alpha blockVisits haccepted
  have hcore :=
    finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  change
    (finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits).inputDrivenCore
        (fun bit => .bit bit)
        (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
          machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits)
        (finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
          machine input.length alpha blockVisits).start =
      .completed
        (finiteCachedAllBlocksInPlaceRollingFold machine input alpha
          blockVisits hentries) at hcore
  rw [hcore]
  congr 1
  exact finiteCachedAllBlocksInPlaceRollingFold_eq_inPlace_of_acceptedFromBlank
    machine input alpha blockVisits haccepted

/-- The total compiled fused program evaluates exactly to the two flags of
the semantic in-place fold reached by its own execution. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_eq_inPlace_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : ∀ block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
          (blockVisits block)) :
    let fold := inPlaceTwoWindowBlockFold (cachedInputMachine machine) input
      alpha
        (fun block =>
          blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        blockVisits
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha blockVisits).eval
        (fun index => input.get index) =
      (fold.allBlockVisitsValid && fold.allClosedCutsValid) := by
  dsimp only
  let verifier :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
      machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let semanticFold := inPlaceTwoWindowBlockFold
    (cachedInputMachine machine) input alpha
      (fun block =>
        blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      blockVisits
  obtain ⟨reachedFold, hreached, heval⟩ :=
    compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksFuel blockVisits) verifier.start =
        .completed reachedFold at hreached
  have hexact :=
    finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_completed_eq_inPlace_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksFuel blockVisits) verifier.start =
        .completed semanticFold at hexact
  have hfold : reachedFold = semanticFold := by
    have hstates :
        (FiniteCachedAllBlocksInPlaceRollingState.completed reachedFold :
          FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits) =
        .completed semanticFold := hreached.symm.trans hexact
    injection hstates
  subst reachedFold
  simpa [semanticFold] using heval

end OneTapeMagnification
end Frontier
end Pnp4
