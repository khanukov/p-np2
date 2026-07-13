import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaCutCounterReplay
import Pnp4.Frontier.OneTapeMagnification.LocalBlockStateCount

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite state cost of one bucket's cut counters

`FixedAlphaCutCounterReplay` constructs, for one full bucket, exactly `b`
natural crossing counters and proves that every counter is at most the horizon
`T`.  This file packages those values in their honest finite carrier

`Fin b → Fin (T + 1)`

and computes its exact cardinality `(T + 1)^b`.  Pairing it with the already
formalized `LocalReplayState` multiplies that carrier's exact size by this
factor.  A constructor embeds the counters obtained from any schedule accepted
by the executable schedule/all-block replay checker.

These are carrier/cardinality facts only.  No update circuit, branching
program, input-read-once order, transition implementation, or width theorem is
constructed here.  In particular, the product cardinal is not by itself a
complete validator width bound.
-/

/-- Bounded crossing counters for all `b` candidates in one full bucket. -/
abbrev BucketCutCounterState (T b : Nat) :=
  Fin b → Fin (T + 1)

/-- The exact number of bounded counter vectors is `(T + 1)^b`. -/
theorem card_bucketCutCounterState (T b : Nat) :
    Fintype.card (BucketCutCounterState T b) = (T + 1) ^ b := by
  simp [BucketCutCounterState]

/-- The finite local replay carrier paired with one bucket's bounded crossing
counter vector. -/
abbrev LocalReplayCutCounterState
    (State : Type) (T w b : Nat) :=
  LocalReplayState State T w × BucketCutCounterState T b

/-- Exact cardinality of local replay state plus one bucket's counters. -/
theorem card_localReplayCutCounterState
    (machine : DeterministicMachine) (T w b : Nat) :
    letI := machine.stateFintype
    Fintype.card
        (LocalReplayCutCounterState machine.State T w b) =
      (Fintype.card machine.State * (T + 1) * w * 2 ^ w) *
        (T + 1) ^ b := by
  letI := machine.stateFintype
  change
    Fintype.card
        (LocalReplayState machine.State T w × BucketCutCounterState T b) = _
  rw [Fintype.card_prod, card_localReplayState,
    card_bucketCutCounterState]

/-- The preceding exact formula also gives the transparent product form. -/
theorem card_localReplayCutCounterState_product
    (machine : DeterministicMachine) (T w b : Nat) :
    letI := machine.stateFintype
    Fintype.card
        (LocalReplayCutCounterState machine.State T w b) =
      Fintype.card (LocalReplayState machine.State T w) *
        (T + 1) ^ b := by
  letI := machine.stateFintype
  change
    Fintype.card
        (LocalReplayState machine.State T w × BucketCutCounterState T b) = _
  rw [Fintype.card_prod, card_bucketCutCounterState]

/-- Product carrier for one canonical block and the `b` counters of one full
bucket. -/
abbrev CanonicalLocalReplayCutCounterState
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (machine : DeterministicMachine) (block : Fin (T / b + 1)) :=
  LocalReplayCutCounterState machine.State T
    (canonicalBlockWidth hb crossings block) b

/-- Honest ambient cardinal bound obtained by multiplying the proved local
slab-state bound by the exact counter-vector cardinality. -/
theorem canonicalLocalReplayCutCounterState_card_le
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (machine : DeterministicMachine) (block : Fin (T / b + 1)) :
    letI := machine.stateFintype
    Fintype.card
        (CanonicalLocalReplayCutCounterState hb crossings machine block) ≤
      (Fintype.card machine.State * (T + 1) * (2 * b) * 2 ^ (2 * b)) *
        (T + 1) ^ b := by
  letI := machine.stateFintype
  rw [card_localReplayCutCounterState_product]
  exact Nat.mul_le_mul_right ((T + 1) ^ b)
    (canonicalLocalReplayState_card_le hb crossings machine block)

/-- Turn the locally replayed natural crossing counts of an accepted schedule
into their bounded finite carrier.  The upper-bound proof is exactly the
previously established `counter ≤ T` theorem. -/
def bucketCutCounterStateOfAcceptedReplay
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (bucket : Fin (T / b)) : BucketCutCounterState T b :=
  fun offset =>
    ⟨fixedAlphaScheduledVisitsBucketCrossingCounters machine input alpha
        (blankFixedAlphaSlabStore alpha) visits bucket offset,
      by
        have hle :=
          fixedAlphaScheduledVisitsBucketCrossingCounter_le_horizon
            machine input alpha visits hcheck bucket offset
        omega⟩

/-- Coercing the bounded vector back to naturals recovers the exact locally
replayed counter. -/
@[simp]
theorem bucketCutCounterStateOfAcceptedReplay_apply_val
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (bucket : Fin (T / b)) (offset : Fin b) :
    (bucketCutCounterStateOfAcceptedReplay
      machine input alpha visits hcheck bucket offset).val =
      fixedAlphaScheduledVisitsBucketCrossingCounters machine input alpha
        (blankFixedAlphaSlabStore alpha) visits bucket offset :=
  rfl

/-- The bounded carrier produced from an accepted replay contains the actual
blank-start crossing counts at the bucket candidates. -/
theorem bucketCutCounterStateOfAcceptedReplay_apply_val_eq_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (bucket : Fin (T / b)) (offset : Fin b) :
    (bucketCutCounterStateOfAcceptedReplay
      machine input alpha visits hcheck bucket offset).val =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary bucket offset) := by
  change fixedAlphaScheduledVisitsBucketCrossingCounters machine input alpha
      (blankFixedAlphaSlabStore alpha) visits bucket offset = _
  exact congrFun
    (fixedAlphaScheduledVisitsBucketCrossingCounters_eq_actual
      machine input alpha visits hcheck bucket) offset

/-- Pair any supplied local replay state with the bounded counters extracted
from an accepted schedule.  This is a carrier constructor, not a transition
program. -/
def localReplayCutCounterStateOfAcceptedReplay
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b w : Nat}
    (localState : LocalReplayState machine.State T w)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (bucket : Fin (T / b)) :
    LocalReplayCutCounterState machine.State T w b :=
  (localState,
    bucketCutCounterStateOfAcceptedReplay
      machine input alpha visits hcheck bucket)

end OneTapeMagnification
end Frontier
end Pnp4
