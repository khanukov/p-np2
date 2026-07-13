import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaVisitSchedule
import Pnp4.Frontier.OneTapeMagnification.WorkSlabPersistence

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Global glue for an arbitrary accepted timed alpha

The fixed-alpha validator replays the visits of each advertised block from one
blank slab, carrying only that slab between later returns.  This file proves
that simultaneous acceptance of all those filtered lists is nevertheless a
global condition once the advertised visit schedule is chained.

The proof interleaves the per-block replay folds in chronological order.  At
one visit, local replay identifies the actual state-and-head endpoint and the
updated source slab.  Every other advertised slab is disjoint from the source
slab and is therefore unchanged.  Thus all carried slabs remain equal to the
corresponding restrictions of the single deterministic global run.

This is a soundness/glue theorem for the advertised cuts.  It does not prove
that the offsets select leftmost-minimum crossing cuts, nor any width or lower
bound consequence.
-/

/-- One carried finite slab for every advertised work block. -/
abbrev FixedAlphaSlabStore
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) :=
  (block : Fin (T / b + 1)) →
    WorkSlab (advertisedBlockWidth alpha.offsets block)

/-- Initially every advertised slab is blank. -/
def blankFixedAlphaSlabStore
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) :
    FixedAlphaSlabStore alpha :=
  fun block => blankWorkSlab (advertisedBlockWidth alpha.offsets block)

/-- Update exactly the slab owning one scheduled visit. -/
def updateFixedAlphaSlabStore
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (scheduled : TimedAlphaScheduledVisit machine.State T b) :
    FixedAlphaSlabStore alpha :=
  fun target =>
    if htarget : scheduled.block = target then
      cast
        (congrArg WorkSlab
          (congrArg (advertisedBlockWidth alpha.offsets) htarget))
        (fixedAlphaBlockVisitOutputSlab machine input alpha scheduled.block
          scheduled.visit (store scheduled.block))
    else
      store target

@[simp]
theorem updateFixedAlphaSlabStore_owner
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (scheduled : TimedAlphaScheduledVisit machine.State T b) :
    updateFixedAlphaSlabStore machine input alpha store scheduled
        scheduled.block =
      fixedAlphaBlockVisitOutputSlab machine input alpha scheduled.block
        scheduled.visit (store scheduled.block) := by
  simp [updateFixedAlphaSlabStore]

@[simp]
theorem updateFixedAlphaSlabStore_other
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (scheduled : TimedAlphaScheduledVisit machine.State T b)
    (target : Fin (T / b + 1))
    (hne : scheduled.block ≠ target) :
    updateFixedAlphaSlabStore machine input alpha store scheduled target =
      store target := by
  simp [updateFixedAlphaSlabStore, hne]

/-- Chronological interleaving of all per-block local replay checks. -/
def AllScheduledVisitsReplayAccepted
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    FixedAlphaSlabStore alpha →
      List (TimedAlphaScheduledVisit machine.State T b) → Prop
  | _, [] => True
  | store, scheduled :: rest =>
      FixedAlphaBlockVisitValid machine input alpha scheduled.block
          scheduled.visit (store scheduled.block) ∧
        AllScheduledVisitsReplayAccepted machine input alpha
          (updateFixedAlphaSlabStore machine input alpha store scheduled) rest

/-- Per-block replay acceptance can be interleaved in the unique global
chronological order without adding any hypothesis. -/
theorem allScheduledVisitsReplayAccepted_of_perBlock
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hblocks : ∀ target,
      FixedAlphaBlockVisitReplayAccepted machine input alpha target
        (store target) (timedAlphaBlockVisits target visits)) :
    AllScheduledVisitsReplayAccepted machine input alpha store visits := by
  induction visits generalizing store with
  | nil =>
      simp [AllScheduledVisitsReplayAccepted]
  | cons scheduled rest ih =>
      constructor
      · have howner :
            FixedAlphaBlockVisitValid machine input alpha scheduled.block
                scheduled.visit (store scheduled.block) ∧
              FixedAlphaBlockVisitReplayAccepted machine input alpha
                scheduled.block
                (fixedAlphaBlockVisitOutputSlab machine input alpha
                  scheduled.block scheduled.visit (store scheduled.block))
                (timedAlphaBlockVisits scheduled.block rest) := by
          simpa [timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
            FixedAlphaBlockVisitReplayAccepted] using
              (hblocks scheduled.block)
        exact howner.1
      · apply ih
        intro target
        by_cases hsame : scheduled.block = target
        · subst target
          have howner :
              FixedAlphaBlockVisitValid machine input alpha scheduled.block
                  scheduled.visit (store scheduled.block) ∧
                FixedAlphaBlockVisitReplayAccepted machine input alpha
                  scheduled.block
                  (fixedAlphaBlockVisitOutputSlab machine input alpha
                    scheduled.block scheduled.visit (store scheduled.block))
                  (timedAlphaBlockVisits scheduled.block rest) := by
            simpa [timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
              FixedAlphaBlockVisitReplayAccepted] using
                (hblocks scheduled.block)
          simpa using howner.2
        · have hother := hblocks target
          simpa [timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
            hsame] using hother

/-- One accepted visit advances the unique global configuration and updates
exactly its owning slab in the global slab store. -/
theorem fixedAlphaAcceptedVisit_globalStep
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (scheduled : TimedAlphaScheduledVisit machine.State T b)
    (config : Configuration machine.State)
    (hvalid : FixedAlphaBlockVisitValid machine input alpha scheduled.block
      scheduled.visit (store scheduled.block))
    (hentry : ConfigurationMatchesFixedAlphaEndpoint
      scheduled.visit.entry config)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target) :
    ConfigurationMatchesFixedAlphaEndpoint scheduled.visit.exit
        (runFrom machine input config scheduled.visit.steps) ∧
      ∀ target,
        restrictWorkSlab
            (advertisedBlockLower alpha.offsets target)
            (advertisedBlockWidth alpha.offsets target)
            (runFrom machine input config scheduled.visit.steps).workTape =
          updateFixedAlphaSlabStore machine input alpha store scheduled target := by
  let base := advertisedBlockLower alpha.offsets scheduled.block
  let width := advertisedBlockWidth alpha.offsets scheduled.block
  let localEntry := fixedAlphaBlockVisitEntryConfiguration
    alpha scheduled.block scheduled.visit (store scheduled.block)
  have hsameEntry : SameOnWorkSlab base width localEntry config := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [localEntry, base, width] using hentry.1
    · simpa [localEntry, base, width] using hentry.2.1
    · simpa [localEntry, base, width] using hentry.2.2
    · calc
        restrictWorkSlab base width localEntry.workTape =
            store scheduled.block := by
          simp [localEntry, base, width,
            fixedAlphaBlockVisitEntryConfiguration]
        _ = restrictWorkSlab base width config.workTape := by
          simpa [base, width] using (hstore scheduled.block).symm
  have hinsideGlobal : ∀ time, time < scheduled.visit.steps →
      WorkCellInSlab base width
        (runFrom machine input config time).workHead := by
    intro time htime
    have hsameAt := runFrom_sameOnWorkSlab_same_input (steps := time)
      machine input hsameEntry (fun earlier hearlier =>
        hvalid.1 ⟨earlier, by omega⟩)
    have hinsideLocal := hvalid.1 ⟨time, htime⟩
    rw [← hsameAt.2.2.1]
    exact hinsideLocal
  have hexit := fixedAlphaBlockVisitValid_concrete_exit_interface
    machine input alpha scheduled.block scheduled.visit
      (store scheduled.block) hvalid config hsameEntry
  constructor
  · exact hexit.1
  · intro target
    by_cases hsame : scheduled.block = target
    · subst target
      simpa using hexit.2
    · rw [updateFixedAlphaSlabStore_other
          machine input alpha store scheduled target hsame,
        restrictWorkSlab_runFrom_eq_of_avoids
          machine input config
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target)
          scheduled.visit.steps]
      · exact hstore target
      · intro time htime
        exact advertisedBlockSlabsDisjoint_of_ne alpha.offsets
          scheduled.block target hsame _ (hinsideGlobal time htime)

/-- Total number of advertised transitions in a chronological visit list. -/
def timedAlphaScheduledVisitsTotalSteps
    {State : Type} {T b : Nat} :
    List (TimedAlphaScheduledVisit State T b) → Nat
  | [] => 0
  | scheduled :: rest =>
      scheduled.visit.steps + timedAlphaScheduledVisitsTotalSteps rest

/-- Exit endpoint of the last visit of a nonempty scheduled list. -/
def timedAlphaScheduledVisitsFinalExit
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b) :
    List (TimedAlphaScheduledVisit State T b) →
      FixedAlphaVisitEndpoint State T
  | [] => first.visit.exit
  | next :: rest => timedAlphaScheduledVisitsFinalExit next rest

/-- Exit time of the last visit of a nonempty scheduled list. -/
def timedAlphaScheduledVisitsFinalExitTime
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b) :
    List (TimedAlphaScheduledVisit State T b) → Fin (T + 1)
  | [] => first.visit.exitTime
  | next :: rest => timedAlphaScheduledVisitsFinalExitTime next rest

/-- Sequential local acceptance plus endpoint chaining replays the entire
nonempty visit list on one global work tape. -/
theorem allScheduledVisitsReplayAccepted_globalReplay
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (config : Configuration machine.State)
    (first : TimedAlphaScheduledVisit machine.State T b)
    (rest : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllScheduledVisitsReplayAccepted machine input alpha store
      (first :: rest))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hentry : ConfigurationMatchesFixedAlphaEndpoint first.visit.entry config)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target) :
    ConfigurationMatchesFixedAlphaEndpoint
      (timedAlphaScheduledVisitsFinalExit first rest)
      (runFrom machine input config
        (timedAlphaScheduledVisitsTotalSteps (first :: rest))) := by
  induction rest generalizing first store config with
  | nil =>
      have hone := fixedAlphaAcceptedVisit_globalStep
        machine input alpha store first config haccepted.1 hentry hstore
      simpa [timedAlphaScheduledVisitsFinalExit,
        timedAlphaScheduledVisitsTotalSteps] using hone.1
  | cons next rest ih =>
      have hone := fixedAlphaAcceptedVisit_globalStep
        machine input alpha store first config haccepted.1 hentry hstore
      unfold TimedAlphaScheduledVisitsChained at hchained
      rw [List.chain'_cons] at hchained
      have hlink : TimedAlphaScheduledVisitLink first next := hchained.1
      have htail : TimedAlphaScheduledVisitsChained (next :: rest) :=
        hchained.2
      have hnextEntry : ConfigurationMatchesFixedAlphaEndpoint next.visit.entry
          (runFrom machine input config first.visit.steps) := by
        simpa [hlink.2.1] using hone.1
      have hrec := ih
        (first := next)
        (store := updateFixedAlphaSlabStore machine input alpha store first)
        (config := runFrom machine input config first.visit.steps)
        haccepted.2 htail hnextEntry hone.2
      simpa [timedAlphaScheduledVisitsFinalExit,
        timedAlphaScheduledVisitsTotalSteps, runFrom_add] using hrec

/-- Every advertised segment is realized, in order, by one deterministic
global configuration sequence. -/
def TimedAlphaScheduledVisitsMatchGlobalRunFrom
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} :
    Configuration machine.State →
      List (TimedAlphaScheduledVisit machine.State T b) → Prop
  | _, [] => True
  | config, scheduled :: rest =>
      ConfigurationMatchesFixedAlphaEndpoint scheduled.visit.entry config ∧
        ConfigurationMatchesFixedAlphaEndpoint scheduled.visit.exit
          (runFrom machine input config scheduled.visit.steps) ∧
        TimedAlphaScheduledVisitsMatchGlobalRunFrom machine input
          (runFrom machine input config scheduled.visit.steps) rest

/-- Sequential acceptance glues every visit, not merely the terminal one, to
the same deterministic global run. -/
theorem allScheduledVisitsReplayAccepted_matchesGlobalRunFrom
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (config : Configuration machine.State)
    (first : TimedAlphaScheduledVisit machine.State T b)
    (rest : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllScheduledVisitsReplayAccepted machine input alpha store
      (first :: rest))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hentry : ConfigurationMatchesFixedAlphaEndpoint first.visit.entry config)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target) :
    TimedAlphaScheduledVisitsMatchGlobalRunFrom machine input config
      (first :: rest) := by
  induction rest generalizing first store config with
  | nil =>
      have hone := fixedAlphaAcceptedVisit_globalStep
        machine input alpha store first config haccepted.1 hentry hstore
      exact ⟨hentry, hone.1, trivial⟩
  | cons next rest ih =>
      have hone := fixedAlphaAcceptedVisit_globalStep
        machine input alpha store first config haccepted.1 hentry hstore
      unfold TimedAlphaScheduledVisitsChained at hchained
      rw [List.chain'_cons] at hchained
      have hnextEntry : ConfigurationMatchesFixedAlphaEndpoint next.visit.entry
          (runFrom machine input config first.visit.steps) := by
        simpa [hchained.1.2.1] using hone.1
      have htail := ih
        (first := next)
        (store := updateFixedAlphaSlabStore machine input alpha store first)
        (config := runFrom machine input config first.visit.steps)
        haccepted.2 hchained.2 hnextEntry hone.2
      exact ⟨hentry, hone.1, htail⟩

/-- Exact telescoping of the advertised visit durations. -/
theorem timedAlphaScheduledVisits_entry_add_totalSteps_eq_finalExitTime
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest)) :
    first.visit.entryTime.val +
        timedAlphaScheduledVisitsTotalSteps (first :: rest) =
      (timedAlphaScheduledVisitsFinalExitTime first rest).val := by
  induction rest generalizing first with
  | nil =>
      simpa [timedAlphaScheduledVisitsTotalSteps,
        timedAlphaScheduledVisitsFinalExitTime] using
          first.visit.entryTime_add_steps
  | cons next rest ih =>
      unfold TimedAlphaScheduledVisitsChained at hchained
      rw [List.chain'_cons] at hchained
      have htail : TimedAlphaScheduledVisitsChained (next :: rest) :=
        hchained.2
      have hrec := ih next htail
      have hfirst := first.visit.entryTime_add_steps
      have htime := hchained.1.1
      have htimeVal : first.visit.exitTime.val =
          next.visit.entryTime.val := congrArg Fin.val htime
      simp only [timedAlphaScheduledVisitsTotalSteps] at hrec
      simp only [timedAlphaScheduledVisitsTotalSteps,
        timedAlphaScheduledVisitsFinalExitTime]
      omega

/-- Boundary information retained by a token fold. -/
def TimedAlphaTokenVisitFoldCovers
    {State : Type} {T b : Nat}
    (cursor : TimedAlphaVisitCursor State T b)
    (visits : List (TimedAlphaScheduledVisit State T b))
    (finalCursor : TimedAlphaVisitCursor State T b) : Prop :=
  match visits with
  | [] => finalCursor = cursor
  | first :: rest =>
      first.visit.entryTime = cursor.time ∧
        first.visit.entry = cursor.endpoint ∧
        timedAlphaScheduledVisitsFinalExitTime first rest = finalCursor.time ∧
        timedAlphaScheduledVisitsFinalExit first rest = finalCursor.endpoint

/-- The relational token fold neither loses nor invents its initial/final
cursor boundary data. -/
theorem TimedAlphaTokenVisitFold.covers
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {cursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    {finalCursor : TimedAlphaVisitCursor State T b}
    (hfold : TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor) :
    TimedAlphaTokenVisitFoldCovers cursor visits finalCursor := by
  induction hfold with
  | nil cursor =>
      rfl
  | @cons cursor crossing rest visits finalCursor htime hsource htail ih =>
      cases visits with
      | nil =>
          change finalCursor =
              timedAlphaVisitCursorAfterCrossing alpha crossing at ih
          subst finalCursor
          exact ⟨rfl, rfl, rfl, rfl⟩
      | cons next visits =>
          change
            next.visit.entryTime =
                (timedAlphaVisitCursorAfterCrossing alpha crossing).time ∧
              next.visit.entry =
                (timedAlphaVisitCursorAfterCrossing alpha crossing).endpoint ∧
              timedAlphaScheduledVisitsFinalExitTime next visits =
                finalCursor.time ∧
              timedAlphaScheduledVisitsFinalExit next visits =
                finalCursor.endpoint at ih
          exact ⟨rfl, rfl, ih.2.2.1, ih.2.2.2⟩

@[simp]
theorem timedAlphaScheduledVisitsFinalExit_append_singleton
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (last : TimedAlphaScheduledVisit State T b) :
    timedAlphaScheduledVisitsFinalExit first (rest ++ [last]) =
      last.visit.exit := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      exact ih next

@[simp]
theorem timedAlphaScheduledVisitsFinalExitTime_append_singleton
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (last : TimedAlphaScheduledVisit State T b) :
    timedAlphaScheduledVisitsFinalExitTime first (rest ++ [last]) =
      last.visit.exitTime := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      exact ih next

/-- A complete advertised schedule covers exactly the interval from the
machine's initial endpoint at time zero to `alpha.terminal` at time `T`. -/
def TimedAlphaVisitScheduleCoversHorizon
    (machine : DeterministicMachine)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) : Prop :=
  match visits with
  | [] =>
      T = 0 ∧
        alpha.terminal = initialFixedAlphaVisitEndpoint machine T
  | first :: rest =>
      first.visit.entryTime.val = 0 ∧
        first.visit.entry = initialFixedAlphaVisitEndpoint machine T ∧
        (timedAlphaScheduledVisitsFinalExitTime first rest).val = T ∧
        timedAlphaScheduledVisitsFinalExit first rest = alpha.terminal

/-- The fold/finish clauses of schedule validity imply exact horizon
coverage, including the empty `T = 0` case. -/
theorem TimedAlphaVisitScheduleValid.coversHorizon
    (machine : DeterministicMachine)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha machine.State T b}
    {visits : List (TimedAlphaScheduledVisit machine.State T b)}
    (hvalid : TimedAlphaVisitScheduleValid machine alpha visits) :
    TimedAlphaVisitScheduleCoversHorizon machine alpha visits := by
  rcases hvalid with
    ⟨_, finalCursor, visitsSoFar, hfold, hfinish, _⟩
  have hfoldCovers := hfold.covers
  cases hfinish with
  | atTerminal htime hendpoint =>
      cases visits with
      | nil =>
          change finalCursor = initialTimedAlphaVisitCursor machine T b
            at hfoldCovers
          subst finalCursor
          constructor
          · change T = 0
            simpa [initialTimedAlphaVisitCursor] using htime.symm
          · change alpha.terminal = initialFixedAlphaVisitEndpoint machine T
            simpa [initialTimedAlphaVisitCursor] using hendpoint.symm
      | cons first rest =>
          change
            first.visit.entryTime =
                (initialTimedAlphaVisitCursor machine T b).time ∧
              first.visit.entry =
                (initialTimedAlphaVisitCursor machine T b).endpoint ∧
              timedAlphaScheduledVisitsFinalExitTime first rest =
                finalCursor.time ∧
              timedAlphaScheduledVisitsFinalExit first rest =
                finalCursor.endpoint at hfoldCovers
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [initialTimedAlphaVisitCursor] using
              congrArg Fin.val hfoldCovers.1
          · simpa [initialTimedAlphaVisitCursor] using hfoldCovers.2.1
          · have hlast := congrArg Fin.val hfoldCovers.2.2.1
            omega
          · exact hfoldCovers.2.2.2.trans hendpoint
  | finalVisit htime hterminalHead =>
      cases visitsSoFar with
      | nil =>
          change finalCursor = initialTimedAlphaVisitCursor machine T b
            at hfoldCovers
          subst finalCursor
          exact ⟨rfl, rfl, rfl, rfl⟩
      | cons first rest =>
          change
            first.visit.entryTime =
                (initialTimedAlphaVisitCursor machine T b).time ∧
              first.visit.entry =
                (initialTimedAlphaVisitCursor machine T b).endpoint ∧
              timedAlphaScheduledVisitsFinalExitTime first rest =
                finalCursor.time ∧
              timedAlphaScheduledVisitsFinalExit first rest =
                finalCursor.endpoint at hfoldCovers
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [initialTimedAlphaVisitCursor] using
              congrArg Fin.val hfoldCovers.1
          · simpa [initialTimedAlphaVisitCursor] using hfoldCovers.2.1
          · simp [timedAlphaFinalScheduledVisit]
          · simp [timedAlphaFinalScheduledVisit]

/-- Simultaneous local acceptance of every block list from its blank slab. -/
def AllFixedAlphaBlockVisitListsAcceptedFromBlank
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) : Prop :=
  ∀ target,
    FixedAlphaBlockVisitListAcceptedFromBlank machine input alpha target
      (timedAlphaBlockVisits target visits)

/-- The public all-block predicate supplies the chronological interleaving
from the all-blank slab store. -/
theorem allScheduledVisitsReplayAccepted_fromBlank_of_allBlockLists
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    AllScheduledVisitsReplayAccepted machine input alpha
      (blankFixedAlphaSlabStore alpha) visits := by
  apply allScheduledVisitsReplayAccepted_of_perBlock
  intro target
  have htarget := haccepted target
  change FixedAlphaBlockVisitListAccepted machine input alpha target
    (blankWorkSlab (advertisedBlockWidth alpha.offsets target))
    (timedAlphaBlockVisits target visits) at htarget
  simpa [blankFixedAlphaSlabStore] using htarget.2

/-- A valid, locally accepted arbitrary-alpha schedule realizes every visit
on the one blank-start deterministic global run. -/
theorem timedAlphaVisitScheduleValid_allBlockVisitsAccepted_matchesGlobalRun
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    TimedAlphaScheduledVisitsMatchGlobalRunFrom machine input
      (initialConfiguration machine) visits := by
  have hcover := hschedule.coversHorizon machine
  obtain ⟨finalCursor, visitsSoFar, hfold, hfinish, hchained⟩ := hschedule.2
  cases visits with
  | nil =>
      trivial
  | cons first rest =>
      change
        first.visit.entryTime.val = 0 ∧
          first.visit.entry = initialFixedAlphaVisitEndpoint machine T ∧
          (timedAlphaScheduledVisitsFinalExitTime first rest).val = T ∧
          timedAlphaScheduledVisitsFinalExit first rest = alpha.terminal
        at hcover
      have hentry : ConfigurationMatchesFixedAlphaEndpoint first.visit.entry
          (initialConfiguration machine) := by
        rw [hcover.2.1]
        exact ⟨rfl, rfl, rfl⟩
      have hblankStore : ∀ target,
          restrictWorkSlab
              (advertisedBlockLower alpha.offsets target)
              (advertisedBlockWidth alpha.offsets target)
              (initialConfiguration machine).workTape =
            (blankFixedAlphaSlabStore alpha) target := by
        intro target
        simp [blankFixedAlphaSlabStore, initialConfiguration]
      apply allScheduledVisitsReplayAccepted_matchesGlobalRunFrom
        machine input alpha (blankFixedAlphaSlabStore alpha)
          (initialConfiguration machine) first rest
      · exact allScheduledVisitsReplayAccepted_fromBlank_of_allBlockLists
          machine input alpha (first :: rest) haccepted
      · exact hchained
      · exact hentry
      · exact hblankStore

/-- Fieldwise equality principle for bounded endpoints, stated in the form
produced by `ConfigurationMatchesFixedAlphaEndpoint`. -/
theorem boundedTerminalEndpoint_eq_of_state_inputHead_workHead
    {State : Type} {T : Nat}
    (left right : BoundedTerminalEndpoint State T)
    (hstate : left.state = right.state)
    (hinputHead : left.inputHead.val = right.inputHead.val)
    (hworkHead : left.workHead.val = right.workHead.val) :
    left = right := by
  cases left with
  | mk leftState leftInputHead leftWorkHead =>
      cases right with
      | mk rightState rightInputHead rightWorkHead =>
          simp only at hstate hinputHead hworkHead
          subst rightState
          have hinput : leftInputHead = rightInputHead := Fin.ext hinputHead
          have hwork : leftWorkHead = rightWorkHead := Fin.ext hworkHead
          subst rightInputHead
          subst rightWorkHead
          rfl

/-- **Arbitrary-alpha global glue.**

If an arbitrary ambient alpha has a valid advertised schedule and every
filtered block list passes the exact local replay validator from blank, then
the advertised terminal endpoint is the endpoint of the unique deterministic
global run at time `T`.  Thus there is no small counterexample to global glue
under these two predicates; the remaining soundness obligation is cut
selection/minimality, not cross-block tape consistency. -/
theorem timedAlphaVisitScheduleValid_allBlockVisitsAccepted_globalGlue
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    alpha.terminal = boundedTerminalEndpointAtRun machine input T := by
  have hcover := hschedule.coversHorizon machine
  rcases hschedule with
    ⟨_, finalCursor, visitsSoFar, hfold, hfinish, hchained⟩
  cases visits with
  | nil =>
      change T = 0 ∧
          alpha.terminal = initialFixedAlphaVisitEndpoint machine T at hcover
      rcases hcover with ⟨rfl, hterminal⟩
      rw [hterminal]
      apply boundedTerminalEndpoint_eq_of_state_inputHead_workHead
      · rfl
      · rfl
      · rfl
  | cons first rest =>
      change
        first.visit.entryTime.val = 0 ∧
          first.visit.entry = initialFixedAlphaVisitEndpoint machine T ∧
          (timedAlphaScheduledVisitsFinalExitTime first rest).val = T ∧
          timedAlphaScheduledVisitsFinalExit first rest = alpha.terminal
        at hcover
      have hperBlock : ∀ target,
          FixedAlphaBlockVisitReplayAccepted machine input alpha target
            ((blankFixedAlphaSlabStore alpha) target)
            (timedAlphaBlockVisits target (first :: rest)) := by
        intro target
        have htarget := haccepted target
        change FixedAlphaBlockVisitListAccepted machine input alpha target
          (blankWorkSlab (advertisedBlockWidth alpha.offsets target))
          (timedAlphaBlockVisits target (first :: rest)) at htarget
        simpa [blankFixedAlphaSlabStore] using htarget.2
      have hsequential := allScheduledVisitsReplayAccepted_of_perBlock
        machine input alpha (blankFixedAlphaSlabStore alpha)
          (first :: rest) hperBlock
      have hentry : ConfigurationMatchesFixedAlphaEndpoint first.visit.entry
          (initialConfiguration machine) := by
        rw [hcover.2.1]
        exact ⟨rfl, rfl, rfl⟩
      have hblankStore : ∀ target,
          restrictWorkSlab
              (advertisedBlockLower alpha.offsets target)
              (advertisedBlockWidth alpha.offsets target)
              (initialConfiguration machine).workTape =
            (blankFixedAlphaSlabStore alpha) target := by
        intro target
        simp [blankFixedAlphaSlabStore, initialConfiguration]
      have hglobal := allScheduledVisitsReplayAccepted_globalReplay
        machine input alpha (blankFixedAlphaSlabStore alpha)
          (initialConfiguration machine) first rest hsequential hchained
          hentry hblankStore
      have htelescopes :=
        timedAlphaScheduledVisits_entry_add_totalSteps_eq_finalExitTime
          first rest hchained
      have hsteps : timedAlphaScheduledVisitsTotalSteps (first :: rest) = T := by
        omega
      rw [hcover.2.2.2, hsteps] at hglobal
      change ConfigurationMatchesFixedAlphaEndpoint alpha.terminal
        (run machine input T) at hglobal
      apply boundedTerminalEndpoint_eq_of_state_inputHead_workHead
      · simpa using hglobal.1
      · simpa using hglobal.2.1
      · simpa using hglobal.2.2

end OneTapeMagnification
end Frontier
end Pnp4
