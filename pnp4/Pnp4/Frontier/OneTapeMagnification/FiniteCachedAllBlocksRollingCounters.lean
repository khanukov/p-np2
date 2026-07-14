import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListRollingCounters
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksOuterCompiler

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Rolling crossing counters through every advertised block

The outer cached compiler has a dependent active payload: slab width and visit
count both depend on the current block.  This module pairs that payload with a
single horizon-bounded crossing vector.  Same-block microsteps delegate to the
list rolling transition.  At a block boundary a fresh blank slab is installed,
but the vector is transported unchanged to the differently typed next payload.
-/

/-- Dependent all-block rolling state.  Accepted completion retains the final
counter vector; rejection discards data that can no longer affect acceptance. -/
inductive FiniteCachedAllBlocksRollingCounterState
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (m : Nat) where
  | active (block : Fin (T / b + 1))
      (state : FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length m)
  | completed (counters : BoundedCrossingCounterVector T m)
  | rejected

/-- Erase rolling counters to recover the original dependent outer state. -/
def eraseFiniteCachedAllBlocksRollingCounters
    (machine : DeterministicMachine) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)}
    {m : Nat} :
    FiniteCachedAllBlocksRollingCounterState machine alpha blockVisits m →
      FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits
  | .active block state => .active block state.listState
  | .completed _ => .completed
  | .rejected => .rejected

/-- Start the first block from its literal blank slab and an arbitrary shared
counter vector. -/
def finiteCachedAllBlocksRollingCounterStart
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    {m : Nat} (counters : BoundedCrossingCounterVector T m) :
    FiniteCachedAllBlocksRollingCounterState machine alpha blockVisits m :=
  let first : Fin (T / b + 1) := ⟨0, Nat.zero_lt_succ (T / b)⟩
  .active first
    ⟨finiteCachedBlockVisitListStart machine alpha first
      (blankWorkSlab (advertisedBlockWidth alpha.offsets first))
      (blockVisits first) (hentries first), counters⟩

/-- One live all-block transition with block-dependent named boundaries.
Running list phases use the fused list update.  Completing a block installs a
fresh next-block slab but transports the vector without resetting it. -/
def finiteCachedAllBlocksStreamingRollingCounterStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    {m : Nat} (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat) :
    FiniteCachedAllBlocksRollingCounterState machine alpha blockVisits m →
      Option ReadOnlySymbol →
      FiniteCachedAllBlocksRollingCounterState machine alpha blockVisits m
  | .completed counters, _ => .completed counters
  | .rejected, _ => .rejected
  | .active block state, supplied =>
      match state.listState with
      | .rejected => .rejected
      | .completed _ =>
          match supplied with
          | some _ => .rejected
          | none =>
              if hnext : block.val + 1 < T / b + 1 then
                let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
                let nextListState := finiteCachedBlockVisitListStart machine
                  alpha next
                  (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
                  (blockVisits next) (hentries next)
                .active next
                  (carryFiniteCachedBlockVisitListRollingCountersAcrossBlockBoundary
                    nextListState state)
              else
                .completed state.counters
      | .active _ _ =>
          let next := finiteCachedBlockVisitListStreamingRollingCounterStep
            machine n alpha block (blockVisits block) (hentries block)
              (boundaries block) state supplied
          match next.listState with
          | .rejected => .rejected
          | _ => .active block next

/-- Erasing the arbitrary initial counter vector recovers the original outer
start state exactly. -/
@[simp]
theorem eraseFiniteCachedAllBlocksRollingCounters_start
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    {m : Nat} (counters : BoundedCrossingCounterVector T m) :
    eraseFiniteCachedAllBlocksRollingCounters machine
        (finiteCachedAllBlocksRollingCounterStart machine alpha blockVisits
          hentries counters) =
      finiteCachedAllBlocksStart machine alpha blockVisits hentries := by
  rfl

/-- Exact nonfinal block-boundary equation: the next dependent list payload is
freshly blank, and its rolling vector is the previous vector verbatim. -/
theorem finiteCachedAllBlocksStreamingRollingCounterStep_completed_next
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    {m : Nat} (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (block : Fin (T / b + 1))
    (slab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (hnext : block.val + 1 < T / b + 1) :
    let current : FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length m := ⟨.completed slab, counters⟩
    finiteCachedAllBlocksStreamingRollingCounterStep machine n alpha blockVisits
        hentries boundaries (.active block current) none =
      let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
      .active next
        (carryFiniteCachedBlockVisitListRollingCountersAcrossBlockBoundary
          (finiteCachedBlockVisitListStart machine alpha next
            (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
            (blockVisits next) (hentries next))
          current) := by
  simp [finiteCachedAllBlocksStreamingRollingCounterStep, hnext]

/-- The counter vector visible after a nonfinal block boundary is unchanged. -/
theorem finiteCachedAllBlocksStreamingRollingCounterStep_completed_next_counters
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    {m : Nat} (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (block : Fin (T / b + 1))
    (slab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (hnext : block.val + 1 < T / b + 1) :
    let current : FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length m := ⟨.completed slab, counters⟩
    let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
    let stepped := finiteCachedAllBlocksStreamingRollingCounterStep machine n
      alpha blockVisits hentries boundaries
        (.active block current) none
    match stepped with
    | .active nextBlock nextState =>
        nextBlock = next ∧ nextState.counters = counters
    | _ => False := by
  simp [finiteCachedAllBlocksStreamingRollingCounterStep, hnext]

/-- A final block boundary returns the accumulated vector without changing it. -/
theorem finiteCachedAllBlocksStreamingRollingCounterStep_completed_last
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    {m : Nat} (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (block : Fin (T / b + 1))
    (slab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (hlast : ¬ block.val + 1 < T / b + 1) :
    let current : FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length m := ⟨.completed slab, counters⟩
    finiteCachedAllBlocksStreamingRollingCounterStep machine n alpha blockVisits
        hentries boundaries (.active block current) none =
      .completed counters := by
  simp [finiteCachedAllBlocksStreamingRollingCounterStep, hlast]

/-- Sequentially run the certified finite rolling list fold on an explicit
block order.  Every source block starts from its own blank slab, while the
counter vector returned by one block is the initial vector of the next. -/
def runFiniteCachedAllBlocksRollingCountersAlong
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat) :
    List (Fin (T / b + 1)) → BoundedCrossingCounterVector T m →
      BoundedCrossingCounterVector T m
  | [], counters => counters
  | block :: rest, counters =>
      let current :=
        runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input
          alpha block (boundaries block) (blockVisits block) (hentries block)
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) counters
      runFiniteCachedAllBlocksRollingCountersAlong machine input alpha
        blockVisits hentries boundaries rest current.counters

local instance cachedInputMachineStateDecidableEqForAllBlocksRolling
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- The corresponding semantic composition of the established one-pass block
list folds along the same explicit block order. -/
def onePassFixedAlphaAllBlocksCountersAlong
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat) :
    List (Fin (T / b + 1)) → BoundedCrossingCounterVector T m →
      BoundedCrossingCounterVector T m
  | [], counters => counters
  | block :: rest, counters =>
      let current := onePassFixedAlphaBlockListFrom
        (cachedInputMachine machine) input alpha block (boundaries block)
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) counters
        (blockVisits block)
      onePassFixedAlphaAllBlocksCountersAlong machine input alpha blockVisits
        boundaries rest current.counters

/-- Exact induction along any supplied block order.  Per-block replay
acceptance is the only semantic assumption; chronologicality is retained in
the public accepted-list predicate, while its replay component drives the
rolling counter proof. -/
theorem runFiniteCachedAllBlocksRollingCountersAlong_eq_onePass
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (blocks : List (Fin (T / b + 1)))
    (counters : BoundedCrossingCounterVector T m)
    (haccepted : ∀ block,
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block (blockVisits block)) :
    runFiniteCachedAllBlocksRollingCountersAlong machine input alpha blockVisits
        hentries boundaries blocks counters =
      onePassFixedAlphaAllBlocksCountersAlong machine input alpha blockVisits
        boundaries blocks counters := by
  induction blocks generalizing counters with
  | nil => rfl
  | cons block rest ih =>
      simp only [runFiniteCachedAllBlocksRollingCountersAlong,
        onePassFixedAlphaAllBlocksCountersAlong]
      have hblock :
          (runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input
            alpha block (boundaries block) (blockVisits block)
            (hentries block)
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            counters).counters =
          (onePassFixedAlphaBlockListFrom (cachedInputMachine machine) input
            alpha block (boundaries block)
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) counters
            (blockVisits block)).counters := by
        apply
          runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_certificate
        exact (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
          machine input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block)).mpr (haccepted block).2
      rw [hblock]
      exact ih _

/-- Increasing traversal of every advertised block with one shared rolling
counter vector and per-block blank slabs. -/
def runFiniteCachedAllBlocksRollingCounters
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (counters : BoundedCrossingCounterVector T m) :
    BoundedCrossingCounterVector T m :=
  runFiniteCachedAllBlocksRollingCountersAlong machine input alpha blockVisits
    hentries boundaries (List.finRange (T / b + 1)) counters

/-- Increasing sequential composition of `onePassFixedAlphaBlockListFrom` over
the same family of blocks. -/
def onePassFixedAlphaAllBlocksCountersFrom
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (counters : BoundedCrossingCounterVector T m) :
    BoundedCrossingCounterVector T m :=
  onePassFixedAlphaAllBlocksCountersAlong machine input alpha blockVisits
    boundaries (List.finRange (T / b + 1)) counters

/-- Public all-block result.  Accepted blank-slab lists make the finite cached
rolling fold exactly equal to the sequential one-pass composition, with no
counter reset between consecutive blocks. -/
theorem runFiniteCachedAllBlocksRollingCounters_eq_onePass_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (counters : BoundedCrossingCounterVector T m)
    (haccepted : ∀ block,
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block (blockVisits block)) :
    let hentries := fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
    runFiniteCachedAllBlocksRollingCounters machine input alpha blockVisits
        hentries boundaries counters =
      onePassFixedAlphaAllBlocksCountersFrom machine input alpha blockVisits
        boundaries counters := by
  dsimp only [runFiniteCachedAllBlocksRollingCounters,
    onePassFixedAlphaAllBlocksCountersFrom]
  exact runFiniteCachedAllBlocksRollingCountersAlong_eq_onePass machine input
    alpha blockVisits
    (fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank machine input
      alpha blockVisits haccepted)
    boundaries (List.finRange (T / b + 1)) counters haccepted

/-- Fuelled all-block rolling fold with an explicit post-block counter
transport.  Identity transport is the no-reset fold above; the rolling
two-window implementation uses `shiftRightWindowAndClear`. -/
def runFiniteCachedAllBlocksRollingCountersFromWithTransport
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (transport : ∀ _block : Fin (T / b + 1),
      BoundedCrossingCounterVector T m → BoundedCrossingCounterVector T m) :
    Nat → Nat → BoundedCrossingCounterVector T m →
      BoundedCrossingCounterVector T m
  | _, 0, counters => counters
  | next, fuel + 1, counters =>
      if hblock : next < T / b + 1 then
        let block : Fin (T / b + 1) := ⟨next, hblock⟩
        let current :=
          runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input
            alpha block (boundaries block) (blockVisits block)
            (hentries block)
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) counters
        runFiniteCachedAllBlocksRollingCountersFromWithTransport machine input
          alpha blockVisits hentries boundaries transport (next + 1) fuel
            (transport block current.counters)
      else counters

/-- Fuelled semantic one-pass composition with the same post-block transport. -/
def onePassFixedAlphaAllBlocksCountersFromWithTransport
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (transport : ∀ _block : Fin (T / b + 1),
      BoundedCrossingCounterVector T m → BoundedCrossingCounterVector T m) :
    Nat → Nat → BoundedCrossingCounterVector T m →
      BoundedCrossingCounterVector T m
  | _, 0, counters => counters
  | next, fuel + 1, counters =>
      if hblock : next < T / b + 1 then
        let block : Fin (T / b + 1) := ⟨next, hblock⟩
        let current := onePassFixedAlphaBlockListFrom
          (cachedInputMachine machine) input alpha block (boundaries block)
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) counters
          (blockVisits block)
        onePassFixedAlphaAllBlocksCountersFromWithTransport machine input alpha
          blockVisits boundaries transport (next + 1) fuel
            (transport block current.counters)
      else counters

/-- Accepted blank-slab lists make the fuelled finite rolling fold agree with
the transported one-pass composition for every start cursor and fuel. -/
theorem runFiniteCachedAllBlocksRollingCountersFromWithTransport_eq_onePass
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (boundaries : ∀ _block : Fin (T / b + 1), Fin m → Nat)
    (transport : ∀ _block : Fin (T / b + 1),
      BoundedCrossingCounterVector T m → BoundedCrossingCounterVector T m)
    (next fuel : Nat) (counters : BoundedCrossingCounterVector T m)
    (haccepted : ∀ block,
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block (blockVisits block)) :
    runFiniteCachedAllBlocksRollingCountersFromWithTransport machine input alpha
        blockVisits hentries boundaries transport next fuel counters =
      onePassFixedAlphaAllBlocksCountersFromWithTransport machine input alpha
        blockVisits boundaries transport next fuel counters := by
  induction fuel generalizing next counters with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFiniteCachedAllBlocksRollingCountersFromWithTransport,
        onePassFixedAlphaAllBlocksCountersFromWithTransport]
      by_cases hblock : next < T / b + 1
      · rw [dif_pos hblock, dif_pos hblock]
        let block : Fin (T / b + 1) := ⟨next, hblock⟩
        have hcurrent :
            (runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine
              input alpha block (boundaries block) (blockVisits block)
              (hentries block)
              (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
              counters).counters =
            (onePassFixedAlphaBlockListFrom (cachedInputMachine machine) input
              alpha block (boundaries block)
              (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
              counters (blockVisits block)).counters := by
          apply
            runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_certificate
          exact (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
            machine input alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block)).mpr (haccepted block).2
        rw [show (⟨next, hblock⟩ : Fin (T / b + 1)) = block by rfl]
        rw [hcurrent]
        exact ih (next + 1) _
      · rw [dif_neg hblock, dif_neg hblock]

/-- The transported semantic counter fold specializes exactly to the counter
projection of the existing in-place two-window fold.  Each block is replayed
from its literal blank slab and the post-block transport is precisely the
right-to-left window shift used by that fold. -/
theorem onePassFixedAlphaAllBlocksCountersFromWithTransport_eq_inPlace_counters
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (next fuel : Nat) (state : InPlaceTwoWindowFoldState T b) :
    onePassFixedAlphaAllBlocksCountersFromWithTransport machine input alpha
        blockVisits (fun block => advertisedBlockTwoWindowBoundaries block)
        (fun _ counters => shiftRightWindowAndClear counters)
        next fuel state.counters =
      (inPlaceTwoWindowBlockFoldFrom (cachedInputMachine machine) input alpha
        (fun block =>
          blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        blockVisits next fuel state).counters := by
  induction fuel generalizing next state with
  | zero => rfl
  | succ fuel ih =>
      simp only [onePassFixedAlphaAllBlocksCountersFromWithTransport,
        inPlaceTwoWindowBlockFoldFrom]
      by_cases hblock : next < T / b + 1
      · rw [dif_pos hblock, dif_pos hblock]
        let block : Fin (T / b + 1) := ⟨next, hblock⟩
        rw [show (⟨next, hblock⟩ : Fin (T / b + 1)) = block by rfl]
        simpa [inPlaceTwoWindowBlockStep,
          replayBlockIntoRollingTwoWindows] using
          ih (next + 1)
            (inPlaceTwoWindowBlockStep (cachedInputMachine machine) input alpha
              (fun currentBlock => blankWorkSlab
                (advertisedBlockWidth alpha.offsets currentBlock))
              blockVisits state block)
      · rw [dif_neg hblock, dif_neg hblock]

/-- Starting from the zero carrier, the full transported semantic traversal is
the counter projection of `inPlaceTwoWindowBlockFold`. -/
theorem onePassFixedAlphaAllBlocksCountersWithTransport_eq_inPlace_counters
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    onePassFixedAlphaAllBlocksCountersFromWithTransport machine input alpha
        blockVisits (fun block => advertisedBlockTwoWindowBoundaries block)
        (fun _ counters => shiftRightWindowAndClear counters)
        0 (T / b + 1) (zeroBoundedCrossingCounterVector T (b + b)) =
      (inPlaceTwoWindowBlockFold (cachedInputMachine machine) input alpha
        (fun block =>
          blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        blockVisits).counters := by
  simpa [inPlaceTwoWindowBlockFold, initialInPlaceTwoWindowFoldState] using
    onePassFixedAlphaAllBlocksCountersFromWithTransport_eq_inPlace_counters
      machine input alpha blockVisits 0 (T / b + 1)
        (initialInPlaceTwoWindowFoldState T b)

end OneTapeMagnification
end Frontier
end Pnp4
