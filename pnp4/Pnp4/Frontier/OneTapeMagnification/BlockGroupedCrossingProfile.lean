import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.InPlaceTwoWindowBlockFold

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Block-grouped crossing profile

The chronological streaming counter carries a slab store through an
interleaved timed schedule.  The block-ordered fold instead filters the
schedule stably by block and starts each filtered fold from the corresponding
component of the same initial store.

Because `updateFixedAlphaSlabStore` changes only the owner of the current
visit, these two computations are algebraically identical after summing the
filtered folds over all blocks.  No acceptance hypothesis is needed for this
permutation/additivity theorem.  Schedule validity and all-block replay
acceptance enter only through the existing theorem identifying the
chronological profile with the actual blank-start run.
-/

/-- Chronological interleaving equals the sum of all stable filtered
per-block folds, with carried slabs matched exactly. -/
theorem fixedAlphaScheduledVisitsStreamingCrossingCount_eq_sum_blockLists
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (boundary : Nat) :
    fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha
        store visits boundary =
      ∑ block : Fin (T / b + 1),
        fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
          block boundary (store block) (timedAlphaBlockVisits block visits) := by
  induction visits generalizing store with
  | nil =>
      simp [fixedAlphaScheduledVisitsStreamingCrossingCount,
        fixedAlphaBlockVisitListStreamingCrossingCount,
        timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock]
  | cons scheduled rest ih =>
      let contribution :=
        streamingWorkBoundaryCrossingCountFrom machine input
          (fixedAlphaBlockVisitEntryConfiguration alpha scheduled.block
            scheduled.visit (store scheduled.block))
          scheduled.visit.steps boundary
      let updated := updateFixedAlphaSlabStore machine input alpha store scheduled
      let tail := fun block : Fin (T / b + 1) =>
        fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
          block boundary (updated block) (timedAlphaBlockVisits block rest)
      have hpointwise : forall block : Fin (T / b + 1),
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
              block boundary (store block)
              (timedAlphaBlockVisits block (scheduled :: rest)) =
            (if scheduled.block = block then contribution else 0) +
              tail block := by
        intro block
        by_cases howner : scheduled.block = block
        · subst block
          simp [timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
            fixedAlphaBlockVisitListStreamingCrossingCount, contribution,
            tail, updated]
        · simp [timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
            howner, contribution, tail, updated]
      simp only [fixedAlphaScheduledVisitsStreamingCrossingCount]
      rw [ih updated]
      calc
        contribution + ∑ block : Fin (T / b + 1), tail block =
            (∑ block : Fin (T / b + 1),
                if scheduled.block = block then contribution else 0) +
              ∑ block : Fin (T / b + 1), tail block := by
          simp
        _ = ∑ block : Fin (T / b + 1),
              ((if scheduled.block = block then contribution else 0) +
                tail block) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ block : Fin (T / b + 1),
              fixedAlphaBlockVisitListStreamingCrossingCount machine input
                alpha block boundary (store block)
                (timedAlphaBlockVisits block (scheduled :: rest)) := by
          apply Finset.sum_congr rfl
          intro block _
          exact (hpointwise block).symm

/-- Profile-valued form of the grouping theorem. -/
theorem fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_sum_blockLists
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) :
    fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
        store visits =
      fun boundary =>
        ∑ block : Fin (T / b + 1),
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block boundary.val (store block)
              (timedAlphaBlockVisits block visits) := by
  funext boundary
  exact fixedAlphaScheduledVisitsStreamingCrossingCount_eq_sum_blockLists
    machine input alpha store visits boundary.val

/-- The source-block sum used by the rolling fold is exactly the existing
chronological streaming profile when both start from blank slabs. -/
theorem sourceBlockSummedCrossingProfile_eq_scheduledStreamingProfile
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) :
    sourceBlockSummedCrossingProfile machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily visits) =
      fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
        (blankFixedAlphaSlabStore alpha) visits := by
  funext boundary
  symm
  simpa [sourceBlockSummedCrossingProfile,
    fixedAlphaSourceBlockCrossingContribution,
    timedScheduleBlankBlockSlabs, timedScheduleBlockVisitFamily,
    blankFixedAlphaSlabStore] using
    fixedAlphaScheduledVisitsStreamingCrossingCount_eq_sum_blockLists
      machine input alpha (blankFixedAlphaSlabStore alpha) visits boundary.val

/-- Under the existing valid-schedule/all-block hypotheses, the grouped sum,
the chronological streaming profile, and the actual run profile all agree. -/
theorem sourceBlockSummedCrossingProfile_eq_scheduled_eq_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    sourceBlockSummedCrossingProfile machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily visits) =
        fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
          (blankFixedAlphaSlabStore alpha) visits /\
      fixedAlphaScheduledVisitsStreamingCrossingProfile machine input alpha
          (blankFixedAlphaSlabStore alpha) visits =
        actualWorkBoundaryCrossingProfile machine input T := by
  exact ⟨sourceBlockSummedCrossingProfile_eq_scheduledStreamingProfile
      machine input alpha visits,
    fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual
      machine input alpha visits hschedule haccepted⟩

/-- Direct closure of premise (a): the block-grouped sum is the actual global
crossing profile. -/
theorem sourceBlockSummedCrossingProfile_eq_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    sourceBlockSummedCrossingProfile machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily visits) =
      actualWorkBoundaryCrossingProfile machine input T := by
  exact (sourceBlockSummedCrossingProfile_eq_scheduled_eq_actual
    machine input alpha visits hschedule haccepted).1.trans
      (sourceBlockSummedCrossingProfile_eq_scheduled_eq_actual
        machine input alpha visits hschedule haccepted).2

/-- After closing the grouping/permutation premise, the schedule-level
adjacent-source decomposition requires only nonadjacent-zero locality. -/
theorem timedScheduleAdjacentSourceDecomposesActual_of_locality
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits)
    (hlocality : forall (bucket : Fin (T / b)) (candidate : Fin b)
      (block : Fin (T / b + 1)),
      block ≠ leftSourceBlockOfBucket bucket ->
      block ≠ rightSourceBlockOfBucket bucket ->
      fixedAlphaSourceBlockCrossingContribution machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily visits) block
          (fullBucketBoundary bucket candidate) = 0) :
    TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha visits := by
  apply timedScheduleAdjacentSourceDecomposesActual_of_sum_and_locality
  · intro boundary
    exact congrFun (sourceBlockSummedCrossingProfile_eq_actual machine input
      alpha visits hschedule haccepted) boundary
  · exact hlocality

/-- Consequently the global in-place fold needs only locality beyond the
already established schedule and all-block hypotheses. -/
theorem timedSchedule_inPlaceTwoWindowBlockFold_combined_eq_true_iff_actualCuts_of_locality
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits)
    (hlocality : forall (bucket : Fin (T / b)) (candidate : Fin b)
      (block : Fin (T / b + 1)),
      block ≠ leftSourceBlockOfBucket bucket ->
      block ≠ rightSourceBlockOfBucket bucket ->
      fixedAlphaSourceBlockCrossingContribution machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily visits) block
          (fullBucketBoundary bucket candidate) = 0) :
    (((inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily visits)).allBlockVisitsValid &&
      (inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily visits)).allClosedCutsValid) =
        true <->
      forall bucket : Fin (T / b),
        AdvertisedCutOffsetIsLeftmostMinimum
          (actualWorkBoundaryCrossingProfile machine input T) bucket
          (alpha.offsets bucket)) := by
  exact timedSchedule_inPlaceTwoWindowBlockFold_combined_eq_true_iff_actualCuts
    machine input alpha visits hschedule haccepted
    (timedScheduleAdjacentSourceDecomposesActual_of_locality machine input
      alpha visits hschedule haccepted hlocality)

end OneTapeMagnification
end Frontier
end Pnp4
