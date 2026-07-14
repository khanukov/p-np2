import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.OnePassFixedAlphaVisit

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One-pass replay of a supplied visit list for one fixed-alpha block

This file extends the fused one-visit traversal to an arbitrary supplied list
of visits of one advertised block.  The fold carries exactly one finite work
slab and one bounded crossing-counter vector.  In particular, the counters
are not reset between visits.

The Boolean component reflects the pre-existing recursive local-validity
relation.  The counter theorem is deliberately stated with an explicit
total-step budget: if the supplied initial vector has enough room for all
advertised transitions, every final coordinate is the initial value plus the
recursive locally replayed crossing-count specification.

This is only a per-block list layer.  It makes no claim that visit lists from
different blocks can be composed while retaining a single counter vector.
-/

/-- Output of the fused fold over one block's supplied visit list. -/
structure OnePassFixedAlphaBlockListResult (H m width : Nat) where
  allVisitsValid : Bool
  finalSlab : WorkSlab width
  counters : BoundedCrossingCounterVector H m

/-- Run the fused one-visit traversal from an arbitrary bounded counter
vector.  Unlike `onePassFixedAlphaBlockVisit`, this wrapper does not reset the
counter vector and allows a horizon independent of the ambient time `T`. -/
def onePassFixedAlphaBlockVisitFromCounters
    (machine : DeterministicMachine) (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat)
    (initial : BoundedCrossingCounterVector H m) :
    OnePassFixedAlphaVisitResult machine.State H m :=
  onePassFixedAlphaVisitFrom machine input
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block) boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps initial

/-- Read the local-validity Boolean from a fused one-visit result. -/
def onePassFixedAlphaBlockVisitResultCheck
    {State : Type} [DecidableEq State] {T H m : Nat}
    (visit : FixedAlphaBlockVisit State T)
    (result : OnePassFixedAlphaVisitResult State H m) : Bool :=
  result.allPreHeadsInside &&
    (decide (visit.exit.state = result.finalConfig.state) &&
      (decide (visit.exit.inputHead.val = result.finalConfig.inputHead) &&
        decide (visit.exit.workHead.val = result.finalConfig.workHead)))

/-- Restrict a fused visit's final tape to the one advertised block. -/
def onePassFixedAlphaBlockVisitResultOutputSlab
    {State : Type} {T b H m : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (result : OnePassFixedAlphaVisitResult State H m) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) :=
  restrictWorkSlab
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block)
    result.finalConfig.workTape

/-- The arbitrary-counter visit wrapper reaches the ordinary local replay's
exact final configuration. -/
theorem onePassFixedAlphaBlockVisitFromCounters_finalConfig
    (machine : DeterministicMachine) (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat)
    (initial : BoundedCrossingCounterVector H m) :
    (onePassFixedAlphaBlockVisitFromCounters machine input alpha block visit
      carried boundaries initial).finalConfig =
      fixedAlphaBlockVisitRun machine input alpha block visit carried := by
  exact onePassFixedAlphaVisitFrom_finalConfig machine input
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block) boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps initial

/-- The slab transferred by the arbitrary-counter wrapper is exactly the
pre-existing carried output slab. -/
theorem onePassFixedAlphaBlockVisitResultOutputSlab_fromCounters_eq
    (machine : DeterministicMachine) (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat)
    (initial : BoundedCrossingCounterVector H m) :
    onePassFixedAlphaBlockVisitResultOutputSlab alpha block
        (onePassFixedAlphaBlockVisitFromCounters machine input alpha block
          visit carried boundaries initial) =
      fixedAlphaBlockVisitOutputSlab
        machine input alpha block visit carried := by
  unfold onePassFixedAlphaBlockVisitResultOutputSlab
  rw [onePassFixedAlphaBlockVisitFromCounters_finalConfig]
  rfl

/-- Changing the supplied counter vector does not change the exact local
validity predicate reflected by the fused visit result. -/
theorem onePassFixedAlphaBlockVisitResultCheck_fromCounters_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat)
    (initial : BoundedCrossingCounterVector H m) :
    onePassFixedAlphaBlockVisitResultCheck visit
        (onePassFixedAlphaBlockVisitFromCounters machine input alpha block
          visit carried boundaries initial) = true ↔
      FixedAlphaBlockVisitValid
        machine input alpha block visit carried := by
  unfold onePassFixedAlphaBlockVisitFromCounters
  simp only [onePassFixedAlphaBlockVisitResultCheck, Bool.and_eq_true,
    decide_eq_true_eq]
  rw [onePassFixedAlphaVisitFrom_allPreHeadsInside_eq_true_iff,
    onePassFixedAlphaVisitFrom_finalConfig]
  rfl

/-- Total number of advertised transitions in one supplied block visit list. -/
def fixedAlphaBlockVisitsTotalSteps
    {State : Type} {T : Nat} :
    List (FixedAlphaBlockVisit State T) → Nat
  | [] => 0
  | visit :: rest => visit.steps + fixedAlphaBlockVisitsTotalSteps rest

/-- A nonempty strictly chronological list fits between its first entry and
the ambient horizon.  Strict gaps only make the sum of visit durations
smaller. -/
theorem fixedAlphaBlockVisits_firstEntry_add_totalSteps_le_horizon
    {State : Type} {T : Nat}
    (first : FixedAlphaBlockVisit State T)
    (rest : List (FixedAlphaBlockVisit State T))
    (hchronological : FixedAlphaBlockVisitsChronological (first :: rest)) :
    first.entryTime.val +
        fixedAlphaBlockVisitsTotalSteps (first :: rest) ≤ T := by
  induction rest generalizing first with
  | nil =>
      have hadd := first.entryTime_add_steps
      have hexit := first.exitTime.isLt
      simp only [fixedAlphaBlockVisitsTotalSteps]
      omega
  | cons next rest ih =>
      have hpair := hchronological
      rw [FixedAlphaBlockVisitsChronological, List.pairwise_cons] at hpair
      have hfirstNext : first.exitTime.val < next.entryTime.val :=
        hpair.1 next (by simp)
      have htail : FixedAlphaBlockVisitsChronological (next :: rest) := by
        exact hpair.2
      have hrec := ih next htail
      have hadd := first.entryTime_add_steps
      simp only [fixedAlphaBlockVisitsTotalSteps] at hrec ⊢
      omega

/-- Consequently every chronological supplied list of one block has total
duration at most the ambient time horizon. -/
theorem fixedAlphaBlockVisitsTotalSteps_le_horizon
    {State : Type} {T : Nat}
    (visits : List (FixedAlphaBlockVisit State T))
    (hchronological : FixedAlphaBlockVisitsChronological visits) :
    fixedAlphaBlockVisitsTotalSteps visits ≤ T := by
  cases visits with
  | nil => simp [fixedAlphaBlockVisitsTotalSteps]
  | cons first rest =>
      have hfit :=
        fixedAlphaBlockVisits_firstEntry_add_totalSteps_le_horizon
          first rest hchronological
      omega

/-- Stable filtering of any chained timed schedule therefore leaves at most
`T` advertised transitions for each individual block. -/
theorem timedAlphaBlockVisits_totalSteps_le_horizon_of_chained
    {State : Type} {T b : Nat}
    (target : Fin (T / b + 1))
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained visits) :
    fixedAlphaBlockVisitsTotalSteps
        (timedAlphaBlockVisits target visits) ≤ T := by
  exact fixedAlphaBlockVisitsTotalSteps_le_horizon
    (timedAlphaBlockVisits target visits)
    (timedAlphaBlockVisits_chronological_of_chained
      target visits hchained)

/-- Valid timed-alpha schedules supply the same per-block `T`-step budget. -/
theorem TimedAlphaVisitScheduleValid.blockVisitsTotalSteps_le_horizon
    (machine : DeterministicMachine)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha machine.State T b}
    {visits : List (TimedAlphaScheduledVisit machine.State T b)}
    (hvalid : TimedAlphaVisitScheduleValid machine alpha visits)
    (target : Fin (T / b + 1)) :
    fixedAlphaBlockVisitsTotalSteps
        (timedAlphaBlockVisits target visits) ≤ T := by
  exact fixedAlphaBlockVisitsTotalSteps_le_horizon
    (timedAlphaBlockVisits target visits)
    (hvalid.blockVisitsChronological machine target)

/-- Recursive semantic crossing count for one block's supplied visit list.
The slab is evolved exactly as in `FixedAlphaBlockVisitReplayAccepted`. -/
def fixedAlphaBlockVisitListStreamingCrossingCount
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundary : Nat) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) →
      List (FixedAlphaBlockVisit machine.State T) → Nat
  | _, [] => 0
  | carried, visit :: rest =>
      streamingWorkBoundaryCrossingCountFrom machine input
          (fixedAlphaBlockVisitEntryConfiguration
            alpha block visit carried) visit.steps boundary +
        fixedAlphaBlockVisitListStreamingCrossingCount
          machine input alpha block boundary
          (fixedAlphaBlockVisitOutputSlab
            machine input alpha block visit carried) rest

/-- A streaming crossing count has at most one contribution per transition. -/
theorem streamingWorkBoundaryCrossingCountFrom_le_steps
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom machine input config
      steps boundary ≤ steps := by
  induction steps generalizing config with
  | zero => simp [streamingWorkBoundaryCrossingCountFrom]
  | succ steps ih =>
      simp only [streamingWorkBoundaryCrossingCountFrom]
      have htail := ih (step machine input config)
      split <;> omega

/-- Coordinate correctness for one visit started from an arbitrary bounded
vector with enough remaining room. -/
theorem onePassFixedAlphaBlockVisitFromCounters_counter_val
    (machine : DeterministicMachine) (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m → Nat)
    (initial : BoundedCrossingCounterVector H m)
    (hroom : ∀ i, (initial i).val + visit.steps ≤ H)
    (i : Fin m) :
    ((onePassFixedAlphaBlockVisitFromCounters machine input alpha block visit
        carried boundaries initial).counters i).val =
      (initial i).val +
        streamingWorkBoundaryCrossingCountFrom machine input
          (fixedAlphaBlockVisitEntryConfiguration
            alpha block visit carried) visit.steps (boundaries i) := by
  unfold onePassFixedAlphaBlockVisitFromCounters
  rw [onePassFixedAlphaVisitFrom_counters]
  exact onePassBoundedCrossingCounterVectorFrom_apply_val
    machine input boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps initial hroom i

/-- Fused fold over a supplied list of visits of one fixed block.  The
computed output slab and the single counter vector are threaded to the tail;
neither is reinitialized between visits. -/
def onePassFixedAlphaBlockListFrom
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m → Nat) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) →
      BoundedCrossingCounterVector H m →
        List (FixedAlphaBlockVisit machine.State T) →
          OnePassFixedAlphaBlockListResult H m
            (advertisedBlockWidth alpha.offsets block)
  | carried, initial, [] =>
      { allVisitsValid := true
        finalSlab := carried
        counters := initial }
  | carried, initial, visit :: rest =>
      let current := onePassFixedAlphaBlockVisitFromCounters
        machine input alpha block visit carried boundaries initial
      let nextSlab := onePassFixedAlphaBlockVisitResultOutputSlab
        alpha block current
      let tail := onePassFixedAlphaBlockListFrom
        machine input alpha block boundaries nextSlab current.counters rest
      { allVisitsValid :=
          onePassFixedAlphaBlockVisitResultCheck visit current &&
            tail.allVisitsValid
        finalSlab := tail.finalSlab
        counters := tail.counters }

/-- The slab returned by the fused list fold is the old deterministic slab
fold, independently of counter horizon and initial counter contents. -/
theorem onePassFixedAlphaBlockListFrom_finalSlab_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m → Nat)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (initial : BoundedCrossingCounterVector H m)
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    (onePassFixedAlphaBlockListFrom machine input alpha block boundaries
      carried initial visits).finalSlab =
      replayFixedAlphaBlockVisits
        machine input alpha block carried visits := by
  induction visits generalizing carried initial with
  | nil => rfl
  | cons visit rest ih =>
      simp only [onePassFixedAlphaBlockListFrom,
        replayFixedAlphaBlockVisits]
      rw [ih]
      rw [onePassFixedAlphaBlockVisitResultOutputSlab_fromCounters_eq]

/-- The accumulated list Boolean accepts exactly the old recursive
per-visit validity relation, for every supplied initial counter vector. -/
theorem onePassFixedAlphaBlockListFrom_allVisitsValid_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m → Nat)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (initial : BoundedCrossingCounterVector H m)
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    (onePassFixedAlphaBlockListFrom machine input alpha block boundaries
        carried initial visits).allVisitsValid = true ↔
      FixedAlphaBlockVisitReplayAccepted
        machine input alpha block carried visits := by
  induction visits generalizing carried initial with
  | nil => simp [onePassFixedAlphaBlockListFrom,
      FixedAlphaBlockVisitReplayAccepted]
  | cons visit rest ih =>
      simp only [onePassFixedAlphaBlockListFrom, Bool.and_eq_true,
        FixedAlphaBlockVisitReplayAccepted]
      rw [onePassFixedAlphaBlockVisitResultCheck_fromCounters_eq_true_iff,
        ih,
        onePassFixedAlphaBlockVisitResultOutputSlab_fromCounters_eq]

/-- Final coordinate correctness for the whole per-block fold.  The explicit
room hypothesis is the exact condition ensuring that the bounded vector never
saturates anywhere in the visit list. -/
theorem onePassFixedAlphaBlockListFrom_counter_val
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m → Nat)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (initial : BoundedCrossingCounterVector H m)
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hroom : ∀ j,
      (initial j).val + fixedAlphaBlockVisitsTotalSteps visits ≤ H)
    (i : Fin m) :
    ((onePassFixedAlphaBlockListFrom machine input alpha block boundaries
        carried initial visits).counters i).val =
      (initial i).val +
        fixedAlphaBlockVisitListStreamingCrossingCount
          machine input alpha block (boundaries i) carried visits := by
  induction visits generalizing carried initial with
  | nil =>
      simp [onePassFixedAlphaBlockListFrom,
        fixedAlphaBlockVisitListStreamingCrossingCount]
  | cons visit rest ih =>
      let current := onePassFixedAlphaBlockVisitFromCounters
        machine input alpha block visit carried boundaries initial
      let nextSlab := onePassFixedAlphaBlockVisitResultOutputSlab
        alpha block current
      have hfirstRoom : ∀ j, (initial j).val + visit.steps ≤ H := by
        intro j
        have hall := hroom j
        simp only [fixedAlphaBlockVisitsTotalSteps] at hall
        omega
      have hcurrent : ∀ j,
          (current.counters j).val =
            (initial j).val +
              streamingWorkBoundaryCrossingCountFrom machine input
                (fixedAlphaBlockVisitEntryConfiguration
                  alpha block visit carried) visit.steps (boundaries j) := by
        intro j
        exact onePassFixedAlphaBlockVisitFromCounters_counter_val
          machine input alpha block visit carried boundaries initial
          hfirstRoom j
      have htailRoom : ∀ j,
          (current.counters j).val +
              fixedAlphaBlockVisitsTotalSteps rest ≤ H := by
        intro j
        rw [hcurrent j]
        have hcount := streamingWorkBoundaryCrossingCountFrom_le_steps
          machine input
          (fixedAlphaBlockVisitEntryConfiguration
            alpha block visit carried) visit.steps (boundaries j)
        have hall := hroom j
        simp only [fixedAlphaBlockVisitsTotalSteps] at hall
        omega
      simp only [onePassFixedAlphaBlockListFrom]
      rw [ih nextSlab current.counters htailRoom]
      rw [hcurrent i]
      dsimp [nextSlab, current]
      rw [onePassFixedAlphaBlockVisitResultOutputSlab_fromCounters_eq]
      simp only [fixedAlphaBlockVisitListStreamingCrossingCount]
      omega

/-- Zero-start convenience wrapper for the common bounded-counter use. -/
def onePassFixedAlphaBlockList
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m → Nat)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    OnePassFixedAlphaBlockListResult H m
      (advertisedBlockWidth alpha.offsets block) :=
  onePassFixedAlphaBlockListFrom machine input alpha block boundaries
    initialSlab (zeroBoundedCrossingCounterVector H m) visits

/-- Reflection theorem for the zero-start convenience wrapper. -/
theorem onePassFixedAlphaBlockList_allVisitsValid_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m → Nat)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    (onePassFixedAlphaBlockList (H := H) machine input alpha block boundaries
        initialSlab visits).allVisitsValid = true ↔
      FixedAlphaBlockVisitReplayAccepted
        machine input alpha block initialSlab visits := by
  exact onePassFixedAlphaBlockListFrom_allVisitsValid_eq_true_iff
    machine input alpha block boundaries initialSlab
    (zeroBoundedCrossingCounterVector H m) visits

/-- Coordinate correctness from the zero vector under the advertised explicit
total-step bound. -/
theorem onePassFixedAlphaBlockList_counter_val
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m → Nat)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hsteps : fixedAlphaBlockVisitsTotalSteps visits ≤ H)
    (i : Fin m) :
    ((onePassFixedAlphaBlockList (H := H) machine input alpha block boundaries
        initialSlab visits).counters i).val =
      fixedAlphaBlockVisitListStreamingCrossingCount
        machine input alpha block (boundaries i) initialSlab visits := by
  unfold onePassFixedAlphaBlockList
  rw [onePassFixedAlphaBlockListFrom_counter_val machine input alpha block
    boundaries initialSlab (zeroBoundedCrossingCounterVector H m) visits
    (by
      intro j
      simpa [zeroBoundedCrossingCounterVector] using hsteps) i]
  simp [zeroBoundedCrossingCounterVector]

/-- Timed-schedule specialization: schedule validity provides the exact
`H = T` budget needed by the zero-start bounded vector for every one-block
sublist. -/
theorem onePassFixedAlphaBlockList_timed_counter_val
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (target : Fin (T / b + 1)) (boundaries : Fin m → Nat)
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets target))
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (i : Fin m) :
    ((onePassFixedAlphaBlockList (H := T) machine input alpha target
        boundaries initialSlab
        (timedAlphaBlockVisits target scheduled)).counters i).val =
      fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
        target (boundaries i) initialSlab
        (timedAlphaBlockVisits target scheduled) := by
  exact onePassFixedAlphaBlockList_counter_val machine input alpha target
    boundaries initialSlab (timedAlphaBlockVisits target scheduled)
    (hschedule.blockVisitsTotalSteps_le_horizon machine target) i

end OneTapeMagnification
end Frontier
end Pnp4
