import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitRollingCounters
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListCompiler

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Rolling crossing counters for a finite cached block-visit list

This module lifts the live one-visit rolling counter transition to the finite
cursor state of a whole fixed-block visit list.  Running microsteps update the
counter vector in the same transition.  Silent accepted visit boundaries keep
that vector unchanged while installing the completed slab in the next visit.
-/

/-- A finite cached list-streaming state paired with one rolling bounded
crossing vector shared by every visit in the list. -/
structure FiniteCachedBlockVisitListRollingCounterState
    (State : Type) (H w k m : Nat) where
  listState : FiniteCachedBlockVisitListStreamingState State H w k
  counters : BoundedCrossingCounterVector H m
deriving Fintype

/-- One executable list transition with live counter updates.  Only a running
one-visit phase can change the counters; completed-phase carry transitions
delegate to the original list step and retain the vector verbatim. -/
def finiteCachedBlockVisitListStreamingRollingCounterStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    {m : Nat} (boundaries : Fin m → Nat) :
    FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block) visits.length m →
      Option ReadOnlySymbol →
      FiniteCachedBlockVisitListRollingCounterState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block) visits.length m
  | state, supplied =>
      match state.listState with
      | .active cursor phase@(.running _ _) =>
          let next := finiteCachedVisitStreamingRollingCounterStep machine n T
            (advertisedBlockWidth alpha.offsets block)
            (advertisedBlockLower alpha.offsets block)
            (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
            boundaries ⟨phase, state.counters⟩ supplied
          { listState := liftFiniteCachedBlockVisitPhase cursor next.phase
            counters := next.counters }
      | listState =>
          { listState := finiteCachedBlockVisitListStreamingStep machine n alpha
              block visits hentries listState supplied
            counters := state.counters }

/-- Erasing counters from one lifted transition recovers exactly the original
finite cached list transition. -/
@[simp]
theorem finiteCachedBlockVisitListStreamingRollingCounterStep_listState
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    {m : Nat} (boundaries : Fin m → Nat)
    (state : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length m)
    (supplied : Option ReadOnlySymbol) :
    (finiteCachedBlockVisitListStreamingRollingCounterStep machine n alpha
      block visits hentries boundaries state supplied).listState =
      finiteCachedBlockVisitListStreamingStep machine n alpha block visits
        hentries state.listState supplied := by
  rcases state with ⟨listState, counters⟩
  cases listState with
  | active cursor phase =>
      cases phase <;> rfl
  | completed slab => rfl
  | rejected => rfl

/-- Under a running cursor, the list counter projection is definitionally the
one-visit rolling update. -/
theorem finiteCachedBlockVisitListStreamingRollingCounterStep_active_running_counters
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    {m : Nat} (boundaries : Fin m → Nat)
    (cursor : Fin visits.length) (remaining : Fin (T + 1))
    (live : LocalReplayState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (supplied : Option ReadOnlySymbol) :
    (finiteCachedBlockVisitListStreamingRollingCounterStep machine n alpha
      block visits hentries boundaries
        ⟨.active cursor (.running remaining live), counters⟩ supplied).counters =
      (finiteCachedVisitStreamingRollingCounterStep machine n T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        boundaries ⟨.running remaining live, counters⟩ supplied).counters := by
  rfl

/-- A successful nonfinal visit boundary installs the completed slab while
preserving the shared rolling vector exactly. -/
theorem finiteCachedBlockVisitListStreamingRollingCounterStep_completed_next
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    {m : Nat} (boundaries : Fin m → Nat)
    (cursor : Fin visits.length)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (haccept : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block)
      (visits.get cursor).exit (.completed final) = true)
    (hnext : cursor.val + 1 < visits.length) :
    finiteCachedBlockVisitListStreamingRollingCounterStep machine n alpha block
        visits hentries boundaries
        ⟨.active cursor (.completed final), counters⟩ none =
      ⟨finiteCachedBlockVisitListActiveState machine alpha block visits hentries
        ⟨cursor.val + 1, hnext⟩ final.workSlab, counters⟩ := by
  simp only [finiteCachedBlockVisitListStreamingRollingCounterStep]
  rw [finiteCachedBlockVisitListStreamingStep_completed_next machine n alpha
    block visits hentries cursor final haccept hnext]

/-- The final accepted visit boundary returns its slab and leaves the shared
counter vector unchanged. -/
theorem finiteCachedBlockVisitListStreamingRollingCounterStep_completed_last
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    {m : Nat} (boundaries : Fin m → Nat)
    (cursor : Fin visits.length)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (haccept : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block)
      (visits.get cursor).exit (.completed final) = true)
    (hlast : ¬ cursor.val + 1 < visits.length) :
    finiteCachedBlockVisitListStreamingRollingCounterStep machine n alpha block
        visits hentries boundaries
        ⟨.active cursor (.completed final), counters⟩ none =
      ⟨.completed final.workSlab, counters⟩ := by
  simp only [finiteCachedBlockVisitListStreamingRollingCounterStep]
  rw [finiteCachedBlockVisitListStreamingStep_completed_last machine n alpha
    block visits hentries cursor final haccept hlast]

/-- Specialize the chronological rolling runner to the semantic unread trace
of one advertised fixed-alpha visit. -/
def runFiniteCachedFixedAlphaVisitRollingCounters
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    {m : Nat} (boundaries : Fin m → Nat)
    (counters : BoundedCrossingCounterVector T m) :
    FiniteCachedVisitRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) m :=
  runFiniteCachedVisitStreamingRollingCountersWithUnreads machine input.length T
    (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    boundaries
    (cachedRunUnreadSymbols machine input
      (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
      visit.steps)
    ⟨.running (fixedAlphaVisitRemaining visit)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry),
      counters⟩

/-- Erasing counters from the specialized runner gives the established
one-visit streaming comparison. -/
theorem runFiniteCachedFixedAlphaVisitRollingCounters_phase
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    {m : Nat} (boundaries : Fin m → Nat)
    (counters : BoundedCrossingCounterVector T m) :
    (runFiniteCachedFixedAlphaVisitRollingCounters machine input alpha block
      visit carried hentry boundaries counters).phase =
      runFiniteCachedVisitStreamingWithUnreads machine input.length T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        (cachedRunUnreadSymbols machine input
          (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
          visit.steps)
        (.running (fixedAlphaVisitRemaining visit)
          (finiteCachedStateOfVisitEntry machine alpha block visit carried
            hentry)) := by
  exact runFiniteCachedVisitStreamingRollingCountersWithUnreads_phase
    machine input.length T (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    boundaries _ _

/-- A certified accepted visit updates the specialized rolling vector exactly
as the existing arbitrary-counter one-pass visit wrapper. -/
theorem runFiniteCachedFixedAlphaVisitRollingCounters_counters_eq_onePass
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    {m : Nat} (boundaries : Fin m → Nat)
    (counters : BoundedCrossingCounterVector T m)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry))
    (hstream : runFiniteCachedVisitStreamingWithUnreads machine input.length T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      (.running (fixedAlphaVisitRemaining visit)
        (finiteCachedStateOfVisitEntry machine alpha block visit carried
          hentry)) = .completed final) :
    (runFiniteCachedFixedAlphaVisitRollingCounters machine input alpha block
      visit carried hentry boundaries counters).counters =
      (onePassFixedAlphaBlockVisitFromCounters (cachedInputMachine machine)
        input alpha block visit carried boundaries counters).counters := by
  unfold runFiniteCachedFixedAlphaVisitRollingCounters
  unfold onePassFixedAlphaBlockVisitFromCounters
  rw [runFiniteCachedVisitStreamingRollingCountersWithUnreads_counters_eq_onePassFixedAlphaVisitFrom_of_completed
    machine input
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    boundaries
    (cachedRunUnreadSymbols machine input
      (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
      visit.steps)
    (fixedAlphaVisitRemaining visit)
    (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry)
    counters final (by simp [fixedAlphaVisitRemaining]) hagree hstream]
  rw [materialize_finiteCachedStateOfVisitEntry]
  simp

/-- The head entry proof extracted from a whole-list entry certificate. -/
theorem FixedAlphaBlockVisitEntriesInside.head
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit State T)
    (rest : List (FixedAlphaBlockVisit State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block (visit :: rest)) :
    WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val :=
  hentries visit (by simp)

/-- Restrict a whole-list entry certificate to its tail. -/
theorem FixedAlphaBlockVisitEntriesInside.tail
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit State T)
    (rest : List (FixedAlphaBlockVisit State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block (visit :: rest)) :
    FixedAlphaBlockVisitEntriesInside alpha block rest := by
  intro tailVisit hmem
  exact hentries tailVisit (by simp [hmem])

/-- Slab and counter outputs of the chronological rolling fold over one fixed
block's advertised visit list. -/
structure FiniteCachedFixedAlphaBlockVisitListRollingResult
    (H m width : Nat) where
  finalSlab : WorkSlab width
  counters : BoundedCrossingCounterVector H m

/-- Chronologically fold the specialized rolling visit runner over one block.
The completed finite slab starts the next visit, and the counter vector is
passed to that visit without reinitialization.  On an uncertified failed phase
the old slab is retained; the correctness theorem below only uses accepted
lists, where every phase is completed. -/
def runFiniteCachedFixedAlphaBlockVisitListRollingCounters
    (machine : DeterministicMachine) (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (boundaries : Fin m → Nat) :
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)) →
      FixedAlphaBlockVisitEntriesInside alpha block visits →
      WorkSlab (advertisedBlockWidth alpha.offsets block) →
      BoundedCrossingCounterVector T m →
      FiniteCachedFixedAlphaBlockVisitListRollingResult T m
        (advertisedBlockWidth alpha.offsets block)
  | [], _, carried, counters =>
      { finalSlab := carried
        counters := counters }
  | visit :: rest, hentries, carried, counters =>
      let hentry := hentries.head alpha block visit rest
      let current := runFiniteCachedFixedAlphaVisitRollingCounters machine input
        alpha block visit carried hentry boundaries counters
      let nextSlab :=
        match current.phase with
        | .completed final => final.workSlab
        | _ => carried
      runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input alpha
        block boundaries rest (hentries.tail alpha block visit rest) nextSlab
          current.counters

local instance cachedInputMachineStateDecidableEqForRollingList
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- For every recursively accepted finite cached visit list, the final rolling
vector is exactly the counter projection of `onePassFixedAlphaBlockListFrom`.
In particular, the vector is carried—not reset—at every visit boundary. -/
theorem runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_certificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (boundaries : Fin m → Nat)
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (hcertificate :
      FiniteCachedFixedAlphaBlockVisitListStreamingCertificate machine input
        alpha block carried visits) :
    (runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input alpha
      block boundaries visits hentries carried counters).counters =
      (onePassFixedAlphaBlockListFrom (cachedInputMachine machine) input alpha
        block boundaries carried counters visits).counters := by
  induction visits generalizing carried counters with
  | nil => rfl
  | cons visit rest ih =>
      rw [FiniteCachedFixedAlphaBlockVisitListStreamingCertificate]
        at hcertificate
      rcases hcertificate with ⟨final, hstep, htail⟩
      have houtput := hstep.outputSlab_eq machine input alpha block visit
        carried final
      rcases hstep with
        ⟨hentry, hagree, hstream, hstate, hinput, hwork⟩
      let current := runFiniteCachedFixedAlphaVisitRollingCounters machine input
        alpha block visit carried hentry boundaries counters
      have hphase : current.phase = .completed final := by
        rw [runFiniteCachedFixedAlphaVisitRollingCounters_phase]
        exact hstream
      have hcurrentCounters : current.counters =
          (onePassFixedAlphaBlockVisitFromCounters (cachedInputMachine machine)
            input alpha block visit carried boundaries counters).counters := by
        exact
          runFiniteCachedFixedAlphaVisitRollingCounters_counters_eq_onePass
            machine input alpha block visit carried hentry boundaries counters
              final hagree hstream
      have hnextSlab :
          onePassFixedAlphaBlockVisitResultOutputSlab alpha block
              (onePassFixedAlphaBlockVisitFromCounters
                (cachedInputMachine machine) input alpha block visit carried
                  boundaries counters) = final.workSlab := by
        rw [onePassFixedAlphaBlockVisitResultOutputSlab_fromCounters_eq]
        exact houtput.symm
      simp only [runFiniteCachedFixedAlphaBlockVisitListRollingCounters]
      change
        (runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input
          alpha block boundaries rest
          (hentries.tail alpha block visit rest)
          (match current.phase with
            | .completed visitFinal => visitFinal.workSlab
            | _ => carried)
          current.counters).counters = _
      rw [hphase, hcurrentCounters]
      rw [ih (hentries.tail alpha block visit rest) final.workSlab
        (onePassFixedAlphaBlockVisitFromCounters (cachedInputMachine machine)
          input alpha block visit carried boundaries counters).counters htail]
      simp only [onePassFixedAlphaBlockListFrom]
      rw [hnextSlab]

/-- Public semantic form: replay acceptance alone supplies both the entry
proofs used by the executable finite fold and its recursive streaming
certificate, hence the final rolling vector equals the one-pass list vector. -/
theorem runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (boundaries : Fin m → Nat)
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (counters : BoundedCrossingCounterVector T m)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block carried visits) :
    let hentries := fixedAlphaBlockVisitEntriesInside_of_replayAccepted
      (cachedInputMachine machine) input alpha block carried visits haccepted
    (runFiniteCachedFixedAlphaBlockVisitListRollingCounters machine input alpha
      block boundaries visits hentries carried counters).counters =
      (onePassFixedAlphaBlockListFrom (cachedInputMachine machine) input alpha
        block boundaries carried counters visits).counters := by
  dsimp only
  apply
    runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_certificate
  exact (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
    machine input alpha block carried visits).mpr haccepted

/-- Dependent outer-boundary transport.  The next block may have a different
slab width and a different visit count, while the horizon-sized rolling vector
is carried unchanged.  This is the small type-level interface needed by an
all-block outer state. -/
def carryFiniteCachedBlockVisitListRollingCountersAcrossBlockBoundary
    {State : Type} {H w k nextWidth nextCount m : Nat}
    (nextListState : FiniteCachedBlockVisitListStreamingState
      State H nextWidth nextCount)
    (state : FiniteCachedBlockVisitListRollingCounterState State H w k m) :
    FiniteCachedBlockVisitListRollingCounterState
      State H nextWidth nextCount m :=
  ⟨nextListState, state.counters⟩

@[simp]
theorem carryFiniteCachedBlockVisitListRollingCountersAcrossBlockBoundary_listState
    {State : Type} {H w k nextWidth nextCount m : Nat}
    (nextListState : FiniteCachedBlockVisitListStreamingState
      State H nextWidth nextCount)
    (state : FiniteCachedBlockVisitListRollingCounterState State H w k m) :
    (carryFiniteCachedBlockVisitListRollingCountersAcrossBlockBoundary
      nextListState state).listState = nextListState := rfl

@[simp]
theorem carryFiniteCachedBlockVisitListRollingCountersAcrossBlockBoundary_counters
    {State : Type} {H w k nextWidth nextCount m : Nat}
    (nextListState : FiniteCachedBlockVisitListStreamingState
      State H nextWidth nextCount)
    (state : FiniteCachedBlockVisitListRollingCounterState State H w k m) :
    (carryFiniteCachedBlockVisitListRollingCountersAcrossBlockBoundary
      nextListState state).counters = state.counters := rfl

end OneTapeMagnification
end Frontier
end Pnp4
