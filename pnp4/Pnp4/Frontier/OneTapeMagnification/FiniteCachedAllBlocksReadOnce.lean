import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksOuterCompiler
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaInputPermutation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The exact cross-block read-once residual

The advertised schedule already supplies a duplicate-free *static* master
order: take the fresh input interval of every chronological visit, stably
group the intervals by work block, and clip the resulting natural positions
to `Fin n`.  The finite all-block outer compiler processes blocks in exactly
that stable grouped order.

What is not yet proved by the operational compiler is that every adaptive
trace is a sublist of this static master order.  This is stronger than
correctness on the one semantic input: `LayeredQueryProgram.IsReadOnce`
quantifies over every Boolean input.  On a rejecting input, a local replay can
follow a different transition path before its final endpoint check fails, so
query confinement to the advertised half-open input interval needs its own
proof.

This file states that residual exactly and proves that it is sufficient.  No
semantic run object, acceptance contract, or lower-bound consequence is
introduced.
-/

/-- The finite static variable order obtained from the advertised schedule.
It contains no dummy suffix because the adaptive outer verifier asks only
coordinates requested by a live local replay. -/
def finiteCachedTimedAlphaScheduleMasterQueryOrder
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    List (Fin n) :=
  timedAlphaFiniteInputVariableQueryOrder n scheduled hmonotone

/-- Exact operational residual for global read-once: on every input, the
adaptive outer trace must be a sublist of the schedule-fixed grouped order.

`Sublist` permits early rejection while forbidding both invented coordinates
and repeated or reordered coordinates. -/
def FiniteCachedTimedAlphaScheduleTraceRefinesGroupedOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) : Prop :=
  ∀ input : Fin n → Bool,
    List.Sublist
      ((compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
          machine alpha scheduled).queryTrace input)
      (finiteCachedTimedAlphaScheduleMasterQueryOrder
        scheduled hmonotone)

/-- Chaining and visit-wise input monotonicity make the clipped, stable
grouped master order duplicate-free, including the empty schedule. -/
theorem finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (finiteCachedTimedAlphaScheduleMasterQueryOrder
      (n := n) scheduled hmonotone).Nodup := by
  apply finiteInputVariableQueryOrder_nodup
  cases scheduled with
  | nil =>
      exact
        (stableGroupedCrossingScheduleInputOrder_perm
          ([] : List (CrossingScheduleSegment (T / b + 1)))).symm.nodup
          (by simp [chronologicalCrossingScheduleInputOrder])
  | cons first rest =>
      exact timedAlphaStableGroupedQueryOrder_nodup
        first rest hchained hmonotone

/-- Conditional global theorem.  Schedule geometry discharges duplicate-
freedom of the master order; the single remaining operational trace-refinement
statement then yields read-once for the complete cross-block program. -/
theorem compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_isReadOnce_of_traceRefines
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (hrefines : FiniteCachedTimedAlphaScheduleTraceRefinesGroupedOrder
      (n := n) machine alpha scheduled hmonotone) :
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      (n := n) machine alpha scheduled).IsReadOnce := by
  intro input
  have hmaster := finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
    (n := n) scheduled hchained hmonotone
  exact hmaster.sublist (hrefines input)

/-- Accepted schedule specialization.  Existing global glue supplies both
chaining and input monotonicity; only all-input operational trace refinement
remains as an explicit premise. -/
theorem compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_isReadOnce_of_accepted_of_traceRefines
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (semanticInput : List Bool) {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) semanticInput alpha scheduled)
    (hrefines :
      let hmonotone :=
        allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
          (cachedInputMachine machine) semanticInput alpha scheduled haccepted
      FiniteCachedTimedAlphaScheduleTraceRefinesGroupedOrder
        (n := n) machine alpha scheduled hmonotone) :
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      (n := n) machine alpha scheduled).IsReadOnce := by
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) semanticInput alpha scheduled haccepted
  obtain ⟨_syntactic, _finalCursor, _visitsSoFar, _hfold, _hfinish,
    hchained⟩ := hschedule
  apply
    compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_isReadOnce_of_traceRefines
      machine alpha scheduled hchained hmonotone
  simpa [hmonotone] using hrefines

end OneTapeMagnification
end Frontier
end Pnp4
