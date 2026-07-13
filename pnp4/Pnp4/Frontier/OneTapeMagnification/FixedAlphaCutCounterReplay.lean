import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutMinimalityChecker
import Pnp4.Frontier.OneTapeMagnification.ArbitraryAlphaGlobalGlue
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaVisitChecker

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Crossing counters accumulated by fixed-alpha local replay

The actual-run cut checker evaluates the blank-start trajectory directly.
This file separates that semantic specification from an executable source of
the same counts.  A streaming counter follows a supplied configuration one
transition at a time.  A scheduled counter then runs that stream only on the
locally materialized slab entry of each advertised visit and evolves the
existing finite slab store between visits.

The main theorem proves that a schedule accepted by the existing exact
schedule/all-block checker produces precisely the actual blank-start crossing
profile.  Consequently the leftmost-minimum checker may consume the locally
replayed counters without consulting the actual run in its definition.

This is an exact semantic and executable correspondence.  It does not encode
natural counters as bits, compile the replay to a branching program, or prove
a width bound.  The fixed-bucket projection below exhibits exactly `b`
natural-valued counters, but the claimed `O(b log (tq))` live-bit accounting
still needs a bounded representation and a circuit/branching-program
realization.
-/

/-- Count crossings of one named boundary by streaming a deterministic run.
The recursion consumes the first transition and continues from its exact
successor configuration. -/
def streamingWorkBoundaryCrossingCountFrom
    (machine : DeterministicMachine) (input : List Bool) :
    Configuration machine.State → Nat → Nat → Nat
  | _, 0, _ => 0
  | config, steps + 1, boundary =>
      (if CrossesWorkBoundary boundary config.workHead
          (step machine input config).workHead then 1 else 0) +
        streamingWorkBoundaryCrossingCountFrom machine input
          (step machine input config) steps boundary

/-- The streaming counter splits exactly at any transition boundary. -/
theorem streamingWorkBoundaryCrossingCountFrom_add
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (first suffix boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom machine input config
        (first + suffix) boundary =
      streamingWorkBoundaryCrossingCountFrom machine input config
          first boundary +
        streamingWorkBoundaryCrossingCountFrom machine input
          (runFrom machine input config first) suffix boundary := by
  induction first generalizing config with
  | zero =>
      simp [streamingWorkBoundaryCrossingCountFrom]
  | succ first ih =>
      simp only [Nat.succ_add, streamingWorkBoundaryCrossingCountFrom,
        runFrom, ih, Nat.add_assoc]

/-- Streaming agrees with the pre-existing finite-sum crossing-count
specification. -/
theorem streamingWorkBoundaryCrossingCountFrom_eq
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom machine input config
        steps boundary =
      workBoundaryCrossingCountFrom machine input config steps boundary := by
  induction steps generalizing config with
  | zero =>
      simp [streamingWorkBoundaryCrossingCountFrom,
        workBoundaryCrossingCountFrom]
  | succ steps ih =>
      rw [workBoundaryCrossingCountFrom, Fin.sum_univ_succ]
      simp only [streamingWorkBoundaryCrossingCountFrom]
      change
        (if CrossesWorkBoundary boundary config.workHead
            (step machine input config).workHead then 1 else 0) +
            streamingWorkBoundaryCrossingCountFrom machine input
              (step machine input config) steps boundary =
          (if CrossesWorkBoundary boundary config.workHead
            (step machine input config).workHead then 1 else 0) +
            ∑ i : Fin steps,
              if WorkBoundaryCrossingAtFrom machine input config
                i.succ.val boundary then 1 else 0
      rw [ih]
      congr 1

/-- Two same-input runs with the same visible slab interface accumulate the
same crossing count while the left run remains inside that slab. -/
theorem streamingWorkBoundaryCrossingCountFrom_eq_of_sameOnWorkSlab
    (machine : DeterministicMachine) (input : List Bool)
    {base width : Nat} {left right : Configuration machine.State}
    (steps boundary : Nat)
    (hsame : SameOnWorkSlab base width left right)
    (hinside : ∀ time, time < steps →
      WorkCellInSlab base width
        (runFrom machine input left time).workHead) :
    streamingWorkBoundaryCrossingCountFrom machine input left
        steps boundary =
      streamingWorkBoundaryCrossingCountFrom machine input right
        steps boundary := by
  induction steps generalizing left right with
  | zero =>
      simp [streamingWorkBoundaryCrossingCountFrom]
  | succ steps ih =>
      have hinsideNow : WorkCellInSlab base width left.workHead := by
        simpa using hinside 0 (by omega)
      have hstep : SameOnWorkSlab base width
          (step machine input left) (step machine input right) := by
        apply step_sameOnWorkSlab machine hsame hinsideNow
        exact congrArg (readOnlySymbol input) hsame.2.1
      have hinsideTail : ∀ time, time < steps →
          WorkCellInSlab base width
            (runFrom machine input (step machine input left) time).workHead := by
        intro time htime
        simpa [runFrom] using hinside (time + 1) (by omega)
      have htail := ih (left := step machine input left)
        (right := step machine input right) hstep hinsideTail
      have hcross :
          CrossesWorkBoundary boundary left.workHead
              (step machine input left).workHead ↔
            CrossesWorkBoundary boundary right.workHead
              (step machine input right).workHead := by
        rw [hsame.2.2.1, hstep.2.2.1]
      simp only [streamingWorkBoundaryCrossingCountFrom]
      rw [if_congr hcross rfl rfl, htail]

/-- The crossing count produced by one accepted local visit equals that of
any concrete entry with the same advertised state, heads, and carried slab. -/
theorem fixedAlphaBlockVisitStreamingCrossingCount_eq_concrete
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (concreteEntry : Configuration machine.State)
    (hvalid : FixedAlphaBlockVisitValid
      machine input alpha block visit carried)
    (hentry : ConfigurationMatchesFixedAlphaEndpoint visit.entry concreteEntry)
    (hslab : restrictWorkSlab
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockWidth alpha.offsets block) concreteEntry.workTape =
      carried)
    (boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom machine input
        (fixedAlphaBlockVisitEntryConfiguration
          alpha block visit carried) visit.steps boundary =
      streamingWorkBoundaryCrossingCountFrom machine input concreteEntry
        visit.steps boundary := by
  let localEntry := fixedAlphaBlockVisitEntryConfiguration
    alpha block visit carried
  have hsame : SameOnWorkSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      localEntry concreteEntry := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [localEntry] using hentry.1
    · simpa [localEntry] using hentry.2.1
    · simpa [localEntry] using hentry.2.2
    · simpa [localEntry, fixedAlphaBlockVisitEntryConfiguration] using hslab.symm
  apply streamingWorkBoundaryCrossingCountFrom_eq_of_sameOnWorkSlab
    machine input visit.steps boundary hsame
  intro time htime
  exact hvalid.1 ⟨time, htime⟩

/-- Accumulate one boundary counter across the chronological advertised
visits.  Each visit is run only from its locally materialized endpoint and
the owning value in the finite slab store. -/
def fixedAlphaScheduledVisitsStreamingCrossingCount
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    FixedAlphaSlabStore alpha →
      List (TimedAlphaScheduledVisit machine.State T b) → Nat → Nat
  | _, [], _ => 0
  | store, scheduled :: rest, boundary =>
      streamingWorkBoundaryCrossingCountFrom machine input
          (fixedAlphaBlockVisitEntryConfiguration alpha scheduled.block
            scheduled.visit (store scheduled.block))
          scheduled.visit.steps boundary +
        fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha
          (updateFixedAlphaSlabStore machine input alpha store scheduled)
          rest boundary

/-- The complete locally replayed crossing-count profile. -/
def fixedAlphaScheduledVisitsStreamingCrossingProfile
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) :
    Fin T → Nat :=
  fun boundary =>
    fixedAlphaScheduledVisitsStreamingCrossingCount
      machine input alpha store visits boundary.val

/-- Project the replayed profile to the `b` candidate boundaries of one full
bucket.  This exposes `b` natural counters, without claiming a bit encoding
or a branching-program implementation. -/
def fixedAlphaScheduledVisitsBucketCrossingCounters
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (bucket : Fin (T / b)) : Fin b → Nat :=
  fun offset =>
    fixedAlphaScheduledVisitsStreamingCrossingProfile
      machine input alpha store visits
        (fullBucketBoundary bucket offset)

/-- Exact composition theorem.  Interleaved local acceptance keeps the slab
store synchronized with a supplied global configuration, while the existing
per-visit match relation supplies the chronological concrete entries.  The
sum of all local streaming counts is therefore the count of the concatenated
global run. -/
theorem fixedAlphaScheduledVisitsStreamingCrossingCount_eq_globalFrom
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (config : Configuration machine.State)
    (haccepted : AllScheduledVisitsReplayAccepted
      machine input alpha store visits)
    (hmatches : TimedAlphaScheduledVisitsMatchGlobalRunFrom
      machine input config visits)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target)
    (boundary : Nat) :
    fixedAlphaScheduledVisitsStreamingCrossingCount
        machine input alpha store visits boundary =
      streamingWorkBoundaryCrossingCountFrom machine input config
        (timedAlphaScheduledVisitsTotalSteps visits) boundary := by
  induction visits generalizing store config with
  | nil =>
      simp [fixedAlphaScheduledVisitsStreamingCrossingCount,
        timedAlphaScheduledVisitsTotalSteps,
        streamingWorkBoundaryCrossingCountFrom]
  | cons scheduled rest ih =>
      have hlocal := fixedAlphaBlockVisitStreamingCrossingCount_eq_concrete
        machine input alpha scheduled.block scheduled.visit
          (store scheduled.block) config haccepted.1 hmatches.1
          (hstore scheduled.block) boundary
      have hone := fixedAlphaAcceptedVisit_globalStep
        machine input alpha store scheduled config haccepted.1
          hmatches.1 hstore
      have htail := ih
        (store := updateFixedAlphaSlabStore
          machine input alpha store scheduled)
        (config := runFrom machine input config scheduled.visit.steps)
        haccepted.2 hmatches.2.2 hone.2
      simp only [fixedAlphaScheduledVisitsStreamingCrossingCount,
        timedAlphaScheduledVisitsTotalSteps]
      rw [hlocal, htail]
      exact (streamingWorkBoundaryCrossingCountFrom_add
        machine input config scheduled.visit.steps
          (timedAlphaScheduledVisitsTotalSteps rest) boundary).symm

/-- Accepted advertised visits, started from the all-blank slab store, compute
the actual blank-start crossing profile over the complete horizon. -/
theorem fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
        (blankFixedAlphaSlabStore alpha) visits =
      actualWorkBoundaryCrossingProfile machine input T := by
  have hcover := hschedule.coversHorizon machine
  obtain ⟨finalCursor, visitsSoFar, hfold, hfinish, hchained⟩ := hschedule.2
  cases visits with
  | nil =>
      funext boundary
      change T = 0 ∧
          alpha.terminal = initialFixedAlphaVisitEndpoint machine T at hcover
      have hlt := boundary.isLt
      have : False := by omega
      contradiction
  | cons first rest =>
      have hsequential :=
        allScheduledVisitsReplayAccepted_fromBlank_of_allBlockLists
          machine input alpha (first :: rest) haccepted
      have hmatches :=
        timedAlphaVisitScheduleValid_allBlockVisitsAccepted_matchesGlobalRun
          machine input alpha (first :: rest) hschedule haccepted
      have hblankStore : ∀ target,
          restrictWorkSlab
              (advertisedBlockLower alpha.offsets target)
              (advertisedBlockWidth alpha.offsets target)
              (initialConfiguration machine).workTape =
            (blankFixedAlphaSlabStore alpha) target := by
        intro target
        simp [blankFixedAlphaSlabStore, initialConfiguration]
      have hcounts :=
        fixedAlphaScheduledVisitsStreamingCrossingCount_eq_globalFrom
          machine input alpha (blankFixedAlphaSlabStore alpha)
            (first :: rest) (initialConfiguration machine)
            hsequential hmatches hblankStore
      change
        first.visit.entryTime.val = 0 ∧
          first.visit.entry = initialFixedAlphaVisitEndpoint machine T ∧
          (timedAlphaScheduledVisitsFinalExitTime first rest).val = T ∧
          timedAlphaScheduledVisitsFinalExit first rest = alpha.terminal
        at hcover
      have htelescopes :=
        timedAlphaScheduledVisits_entry_add_totalSteps_eq_finalExitTime
          first rest hchained
      have hsteps :
          timedAlphaScheduledVisitsTotalSteps (first :: rest) = T := by
        omega
      funext boundary
      calc
        fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
            (blankFixedAlphaSlabStore alpha) (first :: rest) boundary =
            fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha
              (blankFixedAlphaSlabStore alpha) (first :: rest) boundary.val :=
          rfl
        _ = streamingWorkBoundaryCrossingCountFrom machine input
              (initialConfiguration machine)
              (timedAlphaScheduledVisitsTotalSteps (first :: rest))
              boundary.val := hcounts boundary.val
        _ = streamingWorkBoundaryCrossingCountFrom machine input
              (initialConfiguration machine) T boundary.val := by rw [hsteps]
        _ = workBoundaryCrossingCountFrom machine input
              (initialConfiguration machine) T boundary.val :=
          streamingWorkBoundaryCrossingCountFrom_eq
            machine input (initialConfiguration machine) T boundary.val
        _ = actualWorkBoundaryCrossingProfile machine input T boundary := by
          rfl

/-- Boolean-checker form of the exact profile theorem. -/
theorem fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual_of_check
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true) :
    fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
        (blankFixedAlphaSlabStore alpha) visits =
      actualWorkBoundaryCrossingProfile machine input T := by
  have hreflect :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input alpha visits).1 hcheck
  exact fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual
    machine input alpha visits hreflect.1 hreflect.2

/-- Cut-minimality checker whose crossing profile is accumulated solely by
the locally replayed schedule. -/
def replayedTimedAlphaCutMinimalityCheck
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) : Bool :=
  advertisedCutOffsetsLeftmostMinimumCheck
    (fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
      (blankFixedAlphaSlabStore alpha) visits)
    alpha.offsets

/-- Under the executable schedule/replay checkpoint, the replayed checker is
extensionally the existing actual-run specification checker. -/
theorem replayedTimedAlphaCutMinimalityCheck_eq_actual_of_schedule_check
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true) :
    replayedTimedAlphaCutMinimalityCheck machine input alpha visits =
      advertisedTimedAlphaCutMinimalityCheck machine input alpha := by
  unfold replayedTimedAlphaCutMinimalityCheck
    advertisedTimedAlphaCutMinimalityCheck
  rw [fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual_of_check
    machine input alpha visits hcheck]

/-- Exact local-counter cut soundness: once the schedule/replay checkpoint
passes, the locally replayed leftmost-minimum check accepts exactly the
canonical cut vector. -/
theorem replayedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hscheduleCheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true) :
    replayedTimedAlphaCutMinimalityCheck machine input alpha visits = true ↔
      alpha.offsets = canonicalCutOffsets machine input T b hb := by
  rw [replayedTimedAlphaCutMinimalityCheck_eq_actual_of_schedule_check
    machine input alpha visits hscheduleCheck]
  exact advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
    machine input T b hb alpha

/-- For an accepted schedule, the `b` fixed-bucket counters are exactly the
actual counts at that bucket's candidate boundaries. -/
theorem fixedAlphaScheduledVisitsBucketCrossingCounters_eq_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (bucket : Fin (T / b)) :
    fixedAlphaScheduledVisitsBucketCrossingCounters machine input alpha
        (blankFixedAlphaSlabStore alpha) visits bucket =
      fun offset => actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary bucket offset) := by
  funext offset
  unfold fixedAlphaScheduledVisitsBucketCrossingCounters
  rw [fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual_of_check
    machine input alpha visits hcheck]

/-- Each of the `b` fixed-bucket counters is at most the run horizon.  This is
the numerical bound needed before a future bounded-bit representation; no
such representation is introduced here. -/
theorem fixedAlphaScheduledVisitsBucketCrossingCounter_le_horizon
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (bucket : Fin (T / b)) (offset : Fin b) :
    fixedAlphaScheduledVisitsBucketCrossingCounters machine input alpha
        (blankFixedAlphaSlabStore alpha) visits bucket offset ≤ T := by
  rw [fixedAlphaScheduledVisitsBucketCrossingCounters_eq_actual
    machine input alpha visits hcheck bucket]
  change workBoundaryCrossingCount machine input T
      (fullBucketBoundary bucket offset).val ≤ T
  calc
    workBoundaryCrossingCount machine input T
        (fullBucketBoundary bucket offset).val ≤
        ∑ boundary : Fin T,
          workBoundaryCrossingCount machine input T boundary.val := by
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun boundary : Fin T =>
          workBoundaryCrossingCount machine input T boundary.val)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (fullBucketBoundary bucket offset))
      simpa using hsingle
    _ ≤ T := sum_workBoundaryCrossingCount_le_steps machine input T

/-- One executable checkpoint for schedule validity, all blank-start block
replays, and leftmost-minimum cut selection from the counters accumulated by
those same local replays. -/
def timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) : Bool :=
  timedAlphaVisitScheduleAllBlockVisitsCheck machine input alpha visits &&
    replayedTimedAlphaCutMinimalityCheck machine input alpha visits

/-- Exact reflection of the combined locally replayed cut checkpoint. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) :
    timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
        machine input alpha visits = true ↔
      timedAlphaVisitScheduleAllBlockVisitsCheck
          machine input alpha visits = true ∧
        alpha.offsets = canonicalCutOffsets machine input T b hb := by
  constructor
  · intro hcombined
    rw [timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck,
      Bool.and_eq_true] at hcombined
    exact ⟨hcombined.1,
      (replayedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
        machine input T b hb alpha visits hcombined.1).1 hcombined.2⟩
  · rintro ⟨hschedule, hoffsets⟩
    rw [timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck,
      Bool.and_eq_true]
    exact ⟨hschedule,
      (replayedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
        machine input T b hb alpha visits hschedule).2 hoffsets⟩

/-- Completeness of the combined checkpoint for the actual canonical alpha. -/
theorem exists_actualTimedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    ∃ visits : List (TimedAlphaScheduledVisit machine.State T b),
      timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) visits = true := by
  obtain ⟨visits, hcheck, _⟩ :=
    exists_actualTimedAlphaVisitScheduleAllBlockVisitsCheck_eq_true
      machine input T b hb
  refine ⟨visits, ?_⟩
  apply
    (timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true_iff
      machine input T b hb
        (chronologicalTimedCanonicalAlpha machine input T b hb) visits).2
  exact ⟨hcheck, rfl⟩

end OneTapeMagnification
end Frontier
end Pnp4
