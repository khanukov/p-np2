import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CutCounterStateCount
import Pnp4.Frontier.OneTapeMagnification.InputCacheNormalization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Honest padded live state for one full-block validator

A physical work block between canonical cuts can meet candidates from the tail
of one bucket and the prefix of the next.  Consequently a one-pass spatial
replay must in general keep two adjacent vectors of `b` crossing counters,
not the single vector counted in `CutCounterStateCount`.

This file records that correction in a finite carrier.  It also uses the
cached-input normalization, since only that machine makes stay transitions
independent of the next unread input bit.  The padded local slab has width
`2 * b`, and the live state has the exact size

`((1 + 3 * |Q|) * (H + 1) * (2 * b) * 2^(2*b)) * (H + 1)^(2*b)`.

Adding one reject sink contributes one further state.  Schedule descriptors,
alpha, visit indices, and the fixed query order are intended to be hardwired
in program layers, not stored in this live carrier.

These are exact carrier/cardinality theorems, not yet a transition system or
a read-once branching-program compilation.
-/

/-- Crossing counters for the two buckets adjacent to one physical block. -/
abbrev AdjacentBucketCutCounterState (H b : Nat) :=
  BucketCutCounterState H b × BucketCutCounterState H b

/-- Two vectors of `b` bounded counters have exactly `(H + 1)^(2*b)` states. -/
theorem card_adjacentBucketCutCounterState (H b : Nat) :
    Fintype.card (AdjacentBucketCutCounterState H b) =
      (H + 1) ^ (2 * b) := by
  rw [Fintype.card_prod, card_bucketCutCounterState]
  rw [show 2 * b = b + b by omega, pow_add]

/-- Padded local state for the cached-input machine together with both live
counter vectors. -/
abbrev CachedFullBlockReplayState
    (machine : DeterministicMachine) (H b : Nat) :=
  LocalReplayState (cachedInputMachine machine).State H (2 * b) ×
    AdjacentBucketCutCounterState H b

/-- Exact live-state count after input-cache normalization. -/
theorem card_cachedFullBlockReplayState
    (machine : DeterministicMachine) (H b : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card (CachedFullBlockReplayState machine H b) =
      ((1 + 3 * @Fintype.card machine.State machine.stateFintype) *
          (H + 1) * (2 * b) * 2 ^ (2 * b)) *
        (H + 1) ^ (2 * b) := by
  letI := (cachedInputMachine machine).stateFintype
  change Fintype.card
      (LocalReplayState (cachedInputMachine machine).State H (2 * b) ×
        AdjacentBucketCutCounterState H b) = _
  rw [Fintype.card_prod,
    card_localReplayState (cachedInputMachine machine) H (2 * b),
    card_adjacentBucketCutCounterState,
    cachedInputMachine_state_card]

/-- Add a permanent reject sink to the padded live carrier. -/
abbrev CachedFullBlockValidatorState
    (machine : DeterministicMachine) (H b : Nat) :=
  Unit ⊕ CachedFullBlockReplayState machine H b

/-- Exact padded validator carrier size, including its reject sink. -/
theorem card_cachedFullBlockValidatorState
    (machine : DeterministicMachine) (H b : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card (CachedFullBlockValidatorState machine H b) =
      1 +
        ((1 + 3 * @Fintype.card machine.State machine.stateFintype) *
            (H + 1) * (2 * b) * 2 ^ (2 * b)) *
          (H + 1) ^ (2 * b) := by
  letI := (cachedInputMachine machine).stateFintype
  change Fintype.card
      (Unit ⊕ CachedFullBlockReplayState machine H b) = _
  rw [Fintype.card_sum, Fintype.card_unit,
    card_cachedFullBlockReplayState]

/-- Package the already-proved accepted-replay counters for any two advertised
buckets in the corrected adjacent-bucket carrier. -/
def adjacentBucketCutCounterStateOfAcceptedReplay
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (left right : Fin (T / b)) : AdjacentBucketCutCounterState T b :=
  (bucketCutCounterStateOfAcceptedReplay
      machine input alpha visits hcheck left,
    bucketCutCounterStateOfAcceptedReplay
      machine input alpha visits hcheck right)

/-- The left vector recovers the exact actual crossing count coordinatewise. -/
theorem adjacentBucketCutCounterStateOfAcceptedReplay_left_val_eq_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (left right : Fin (T / b)) (offset : Fin b) :
    ((adjacentBucketCutCounterStateOfAcceptedReplay
      machine input alpha visits hcheck left right).1 offset).val =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary left offset) := by
  exact bucketCutCounterStateOfAcceptedReplay_apply_val_eq_actual
    machine input alpha visits hcheck left offset

/-- The right vector recovers the exact actual crossing count coordinatewise. -/
theorem adjacentBucketCutCounterStateOfAcceptedReplay_right_val_eq_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (left right : Fin (T / b)) (offset : Fin b) :
    ((adjacentBucketCutCounterStateOfAcceptedReplay
      machine input alpha visits hcheck left right).2 offset).val =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary right offset) := by
  exact bucketCutCounterStateOfAcceptedReplay_apply_val_eq_actual
    machine input alpha visits hcheck right offset

end OneTapeMagnification
end Frontier
end Pnp4
