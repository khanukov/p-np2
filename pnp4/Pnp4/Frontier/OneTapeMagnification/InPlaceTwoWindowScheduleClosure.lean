import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.BlockGroupedCrossingProfile
import Pnp4.Frontier.OneTapeMagnification.NonadjacentBlockCrossingZero

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Schedule closure for the in-place two-window fold

`BlockGroupedCrossingProfile` proves that the sum of the stable per-block
profiles is the actual global profile.  `NonadjacentBlockCrossingZero` proves
that only the two blocks adjacent to a bucket candidate can contribute.
Together they discharge the last decomposition premise of the rolling `2b`
counter fold.
-/

/-- Valid scheduling and simultaneous blank-start acceptance imply the exact
adjacent-source decomposition used by the rolling fold. -/
theorem timedScheduleAdjacentSourceDecomposesActual_of_validity
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled) :
    TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled := by
  apply timedScheduleAdjacentSourceDecomposesActual_of_locality machine input
    alpha scheduled hschedule haccepted
  intro bucket candidate block hneLeft hneRight
  exact timedAlphaBlockVisits_nonadjacent_crossingContribution_eq_zero
    machine input alpha scheduled haccepted bucket candidate block
    hneLeft hneRight

/-- With no extra locality or permutation premise, the global rolling fold
accepts exactly when every advertised offset is the actual-run leftmost
minimum in its full bucket. -/
theorem timedSchedule_inPlaceTwoWindowBlockFold_combined_eq_true_iff_actualCuts_of_validity
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled) :
    (((inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allBlockVisitsValid &&
      (inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allClosedCutsValid) =
        true <->
      forall bucket : Fin (T / b),
        AdvertisedCutOffsetIsLeftmostMinimum
          (actualWorkBoundaryCrossingProfile machine input T) bucket
          (alpha.offsets bucket)) := by
  exact timedSchedule_inPlaceTwoWindowBlockFold_combined_eq_true_iff_actualCuts
    machine input alpha scheduled hschedule haccepted
    (timedScheduleAdjacentSourceDecomposesActual_of_validity machine input
      alpha scheduled hschedule haccepted)

/-- The executable combined schedule/all-block checkpoint directly supplies
the exact adjacent-source decomposition. -/
theorem timedScheduleAdjacentSourceDecomposesActual_of_check
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha scheduled = true) :
    TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled := by
  have hreflect :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input alpha scheduled).1 hcheck
  exact timedScheduleAdjacentSourceDecomposesActual_of_validity machine input
    alpha scheduled hreflect.1 hreflect.2

/-- Executable corollary: once the existing schedule/all-block Boolean check
passes, the in-place `2b` fold is equivalent to actual cut minimality. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCheck_inPlaceTwoWindowFold_iff_actualCuts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha scheduled = true) :
    (((inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allBlockVisitsValid &&
      (inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allClosedCutsValid) =
        true <->
      forall bucket : Fin (T / b),
        AdvertisedCutOffsetIsLeftmostMinimum
          (actualWorkBoundaryCrossingProfile machine input T) bucket
          (alpha.offsets bucket)) := by
  have hreflect :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input alpha scheduled).1 hcheck
  exact
    timedSchedule_inPlaceTwoWindowBlockFold_combined_eq_true_iff_actualCuts_of_validity
      machine input alpha scheduled hreflect.1 hreflect.2

end OneTapeMagnification
end Frontier
end Pnp4
