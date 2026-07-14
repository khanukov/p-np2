import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksRollingCounters

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite cached all-block replay with the in-place two-window fold

This module closes the boundary-operation gap between the finite cached outer
compiler and `inPlaceTwoWindowBlockFold`.  A successful fixed-block phase is
closed in the first window, the right window is shifted left and cleared, and
both global Boolean flags are accumulated before the next blank slab starts.

The executable block fold below uses the finite cached rolling runner inside
each block.  Under accepted blank-slab certificates it is exactly equal, as a
whole `InPlaceTwoWindowFoldState`, to the established semantic in-place fold.
-/

/-- One boundary update shared by the live outer transition and the executable
block fold.  The completed left bucket is checked before the counter carrier
is shifted; the visit and cut flags are both accumulated. -/
def finiteCachedAllBlocksInPlaceBoundaryUpdate
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (blockVisitsValid : Bool)
    (allBlockVisitsValid allClosedCutsValid : Bool)
    (replayCounters : BoundedCrossingCounterVector T (b + b)) :
    InPlaceTwoWindowFoldState T b :=
  { allBlockVisitsValid := allBlockVisitsValid && blockVisitsValid
    allClosedCutsValid := allClosedCutsValid &&
      closeLeftBucketFromFirstWindowCheck alpha.offsets block replayCounters
    counters := shiftRightWindowAndClear replayCounters }

@[simp]
theorem finiteCachedAllBlocksInPlaceBoundaryUpdate_allBlockVisitsValid
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (blockVisitsValid allBlockVisitsValid allClosedCutsValid : Bool)
    (replayCounters : BoundedCrossingCounterVector T (b + b)) :
    (finiteCachedAllBlocksInPlaceBoundaryUpdate alpha block blockVisitsValid
      allBlockVisitsValid allClosedCutsValid replayCounters).allBlockVisitsValid =
        (allBlockVisitsValid && blockVisitsValid) := by
  rfl

@[simp]
theorem finiteCachedAllBlocksInPlaceBoundaryUpdate_allClosedCutsValid
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (blockVisitsValid allBlockVisitsValid allClosedCutsValid : Bool)
    (replayCounters : BoundedCrossingCounterVector T (b + b)) :
    (finiteCachedAllBlocksInPlaceBoundaryUpdate alpha block blockVisitsValid
      allBlockVisitsValid allClosedCutsValid replayCounters).allClosedCutsValid =
        (allClosedCutsValid &&
          closeLeftBucketFromFirstWindowCheck
            alpha.offsets block replayCounters) := by
  rfl

@[simp]
theorem finiteCachedAllBlocksInPlaceBoundaryUpdate_counters
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (blockVisitsValid allBlockVisitsValid allClosedCutsValid : Bool)
    (replayCounters : BoundedCrossingCounterVector T (b + b)) :
    (finiteCachedAllBlocksInPlaceBoundaryUpdate alpha block blockVisitsValid
      allBlockVisitsValid allClosedCutsValid replayCounters).counters =
        shiftRightWindowAndClear replayCounters := by
  rfl

/-- Live dependent outer state.  While a block is active, its finite cached
list state owns the rolling `2b` carrier.  The two global flags are retained
beside it and are updated only at a successful block boundary. -/
inductive FiniteCachedAllBlocksInPlaceRollingState
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) where
  | active (block : Fin (T / b + 1))
      (state : FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length (b + b))
      (allBlockVisitsValid allClosedCutsValid : Bool)
  | completed (state : InPlaceTwoWindowFoldState T b)
  | rejected

/-- Start the first block from a literal blank slab, two true accumulated
flags, and the zero two-window carrier. -/
def finiteCachedAllBlocksInPlaceRollingStart
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits :=
  let first : Fin (T / b + 1) := ⟨0, Nat.zero_lt_succ (T / b)⟩
  .active first
    ⟨finiteCachedBlockVisitListStart machine alpha first
      (blankWorkSlab (advertisedBlockWidth alpha.offsets first))
      (blockVisits first) (hentries first),
      zeroBoundedCrossingCounterVector T (b + b)⟩
    true true

/-- One live finite-cached microstep.  Same-block steps delegate to the fused
list rolling transition.  A successfully completed block performs the actual
in-place close-and-shift update and starts the successor from a blank slab
with the shifted carrier. -/
def finiteCachedAllBlocksInPlaceRollingStreamingStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits →
      Option ReadOnlySymbol →
      FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits
  | .completed state, _ => .completed state
  | .rejected, _ => .rejected
  | .active block state allBlockVisitsValid allClosedCutsValid, supplied =>
      match state.listState with
      | .rejected => .rejected
      | .completed _ =>
          match supplied with
          | some _ => .rejected
          | none =>
              let folded := finiteCachedAllBlocksInPlaceBoundaryUpdate
                alpha block true allBlockVisitsValid allClosedCutsValid
                  state.counters
              if hnext : block.val + 1 < T / b + 1 then
                let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
                .active next
                  ⟨finiteCachedBlockVisitListStart machine alpha next
                    (blankWorkSlab
                      (advertisedBlockWidth alpha.offsets next))
                    (blockVisits next) (hentries next), folded.counters⟩
                  folded.allBlockVisitsValid folded.allClosedCutsValid
              else
                .completed folded
      | .active _ _ =>
          let next := finiteCachedBlockVisitListStreamingRollingCounterStep
            machine n alpha block (blockVisits block) (hentries block)
              (advertisedBlockTwoWindowBoundaries block) state supplied
          match next.listState with
          | .rejected => .rejected
          | _ => .active block next allBlockVisitsValid allClosedCutsValid

/-- Exact nonfinal live boundary equation.  It exposes the close check, the
window shift, both flag updates, the next blank slab, and the transported
shifted vector in one theorem. -/
theorem finiteCachedAllBlocksInPlaceRollingStreamingStep_completed_next
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (slab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T (b + b))
    (allBlockVisitsValid allClosedCutsValid : Bool)
    (hnext : block.val + 1 < T / b + 1) :
    let current : FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length (b + b) := ⟨.completed slab, counters⟩
    let folded := finiteCachedAllBlocksInPlaceBoundaryUpdate alpha block true
      allBlockVisitsValid allClosedCutsValid counters
    finiteCachedAllBlocksInPlaceRollingStreamingStep machine n alpha
        blockVisits hentries
        (.active block current allBlockVisitsValid allClosedCutsValid) none =
      let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
      .active next
        ⟨finiteCachedBlockVisitListStart machine alpha next
          (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
          (blockVisits next) (hentries next), folded.counters⟩
        folded.allBlockVisitsValid folded.allClosedCutsValid := by
  simp [finiteCachedAllBlocksInPlaceRollingStreamingStep, hnext]

/-- Exact final live boundary equation. -/
theorem finiteCachedAllBlocksInPlaceRollingStreamingStep_completed_last
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (slab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T (b + b))
    (allBlockVisitsValid allClosedCutsValid : Bool)
    (hlast : ¬ block.val + 1 < T / b + 1) :
    let current : FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length (b + b) := ⟨.completed slab, counters⟩
    finiteCachedAllBlocksInPlaceRollingStreamingStep machine n alpha
        blockVisits hentries
        (.active block current allBlockVisitsValid allClosedCutsValid) none =
      .completed (finiteCachedAllBlocksInPlaceBoundaryUpdate alpha block true
        allBlockVisitsValid allClosedCutsValid counters) := by
  simp [finiteCachedAllBlocksInPlaceRollingStreamingStep, hlast]

local instance cachedInputMachineStateDecidableEqForAllBlocksInPlaceRolling
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Executable successful-block step: replay the block with the finite cached
rolling runner, accumulate its executable replay-validity Boolean, close the
left bucket, then shift and clear the two-window carrier. -/
def finiteCachedAllBlocksInPlaceRollingBlockStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (state : InPlaceTwoWindowFoldState T b)
    (block : Fin (T / b + 1)) : InPlaceTwoWindowFoldState T b :=
  let blank := blankWorkSlab (advertisedBlockWidth alpha.offsets block)
  let replay :=
    runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input alpha
      block (advertisedBlockTwoWindowBoundaries block) (blockVisits block)
      (hentries block) blank state.counters
  let blockVisitsValid := fixedAlphaBlockVisitReplayCheck
    (cachedInputMachine machine) input alpha block blank (blockVisits block)
  finiteCachedAllBlocksInPlaceBoundaryUpdate alpha block blockVisitsValid
    state.allBlockVisitsValid state.allClosedCutsValid replay.counters

/-- On an accepted blank-slab block, the finite cached close-and-shift step is
exactly the existing semantic in-place step, including both Boolean flags and
the whole shifted counter vector. -/
theorem finiteCachedAllBlocksInPlaceRollingBlockStep_eq_inPlace_of_accepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (state : InPlaceTwoWindowFoldState T b)
    (block : Fin (T / b + 1))
    (haccepted : FixedAlphaBlockVisitListAcceptedFromBlank
      (cachedInputMachine machine) input alpha block (blockVisits block)) :
    finiteCachedAllBlocksInPlaceRollingBlockStep machine input alpha
        blockVisits hentries state block =
      inPlaceTwoWindowBlockStep (cachedInputMachine machine) input alpha
        (fun currentBlock =>
          blankWorkSlab (advertisedBlockWidth alpha.offsets currentBlock))
        blockVisits state block := by
  let blank := blankWorkSlab (advertisedBlockWidth alpha.offsets block)
  let finiteReplay :=
    runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input alpha
      block (advertisedBlockTwoWindowBoundaries block) (blockVisits block)
      (hentries block) blank state.counters
  let semanticReplay := replayBlockIntoRollingTwoWindows
    (cachedInputMachine machine) input alpha
    (fun currentBlock =>
      blankWorkSlab (advertisedBlockWidth alpha.offsets currentBlock))
    blockVisits block state.counters
  have hcertificate :
      FiniteCachedFixedAlphaBlockVisitListStreamingCertificate machine input
        alpha block blank (blockVisits block) :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine input alpha block blank (blockVisits block)).mpr haccepted.2
  have hcounters : finiteReplay.counters = semanticReplay.counters := by
    exact
      runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_certificate
        machine input alpha block (advertisedBlockTwoWindowBoundaries block)
          (blockVisits block) (hentries block) blank state.counters hcertificate
  have hfiniteValid : fixedAlphaBlockVisitReplayCheck
      (cachedInputMachine machine) input alpha block blank
        (blockVisits block) = true :=
    (fixedAlphaBlockVisitReplayCheck_eq_true_iff
      (cachedInputMachine machine) input alpha block blank
        (blockVisits block)).mpr haccepted.2
  have hsemanticValid : semanticReplay.allVisitsValid = true := by
    exact (onePassFixedAlphaBlockListFrom_allVisitsValid_eq_true_iff
      (cachedInputMachine machine) input alpha block
        (advertisedBlockTwoWindowBoundaries block) blank state.counters
          (blockVisits block)).mpr haccepted.2
  cases state with
  | mk allVisits allCuts counters =>
      simp_all [finiteCachedAllBlocksInPlaceRollingBlockStep,
        finiteCachedAllBlocksInPlaceBoundaryUpdate,
        inPlaceTwoWindowBlockStep, replayBlockIntoRollingTwoWindows,
        blank, finiteReplay, semanticReplay]

/-- Fuelled increasing traversal using the finite cached close-and-shift block
step. -/
def finiteCachedAllBlocksInPlaceRollingFoldFrom
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    Nat → Nat → InPlaceTwoWindowFoldState T b →
      InPlaceTwoWindowFoldState T b
  | _, 0, state => state
  | next, fuel + 1, state =>
      if hblock : next < T / b + 1 then
        finiteCachedAllBlocksInPlaceRollingFoldFrom machine input alpha
          blockVisits hentries (next + 1) fuel
            (finiteCachedAllBlocksInPlaceRollingBlockStep machine input alpha
              blockVisits hentries state ⟨next, hblock⟩)
      else state

/-- Accepted blank-slab blocks make every finite cached block step agree with
the semantic step, hence the fuelled folds agree from every cursor and state. -/
theorem finiteCachedAllBlocksInPlaceRollingFoldFrom_eq_inPlace_of_accepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (haccepted : ∀ block,
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block (blockVisits block))
    (next fuel : Nat) (state : InPlaceTwoWindowFoldState T b) :
    finiteCachedAllBlocksInPlaceRollingFoldFrom machine input alpha blockVisits
        hentries next fuel state =
      inPlaceTwoWindowBlockFoldFrom (cachedInputMachine machine) input alpha
        (fun block =>
          blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        blockVisits next fuel state := by
  induction fuel generalizing next state with
  | zero => rfl
  | succ fuel ih =>
      simp only [finiteCachedAllBlocksInPlaceRollingFoldFrom,
        inPlaceTwoWindowBlockFoldFrom]
      by_cases hblock : next < T / b + 1
      · rw [dif_pos hblock, dif_pos hblock]
        let block : Fin (T / b + 1) := ⟨next, hblock⟩
        rw [show (⟨next, hblock⟩ : Fin (T / b + 1)) = block by rfl]
        rw [finiteCachedAllBlocksInPlaceRollingBlockStep_eq_inPlace_of_accepted
          machine input alpha blockVisits hentries state block
            (haccepted block)]
        exact ih (next + 1) _
      · rw [dif_neg hblock, dif_neg hblock]

/-- Full finite cached in-place fold from the standard zero state. -/
def finiteCachedAllBlocksInPlaceRollingFold
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    InPlaceTwoWindowFoldState T b :=
  finiteCachedAllBlocksInPlaceRollingFoldFrom machine input alpha blockVisits
    hentries 0 (T / b + 1) (initialInPlaceTwoWindowFoldState T b)

/-- Main exactness theorem: if every advertised block is accepted from its
blank slab, the complete finite cached run equals the existing
`inPlaceTwoWindowBlockFold` as a full state, not merely after projecting its
counters. -/
theorem finiteCachedAllBlocksInPlaceRollingFold_eq_inPlace_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : ∀ block,
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block (blockVisits block)) :
    let hentries := fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
    finiteCachedAllBlocksInPlaceRollingFold machine input alpha blockVisits
        hentries =
      inPlaceTwoWindowBlockFold (cachedInputMachine machine) input alpha
        (fun block =>
          blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        blockVisits := by
  dsimp only [finiteCachedAllBlocksInPlaceRollingFold,
    inPlaceTwoWindowBlockFold]
  exact finiteCachedAllBlocksInPlaceRollingFoldFrom_eq_inPlace_of_accepted
    machine input alpha blockVisits
      (fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank machine input
        alpha blockVisits haccepted)
      haccepted 0 (T / b + 1) (initialInPlaceTwoWindowFoldState T b)

end OneTapeMagnification
end Frontier
end Pnp4
