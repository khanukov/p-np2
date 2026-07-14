import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.InPlaceTwoWindowBlockFold

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Nonadjacent advertised blocks contribute no bucket crossings

For a candidate boundary in full bucket `k`, only advertised blocks `k` and
`k + 1` can contribute a crossing.  Every pre-transition head of an accepted
visit stays inside its source slab.  A slab strictly to the left has every
such head below the candidate, while a slab strictly to the right has every
such head above the candidate's right cell.  This includes the last
transition of a visit: its post-head may exit the slab, but its pre-head is
still local, and one crossing names only the two cells adjacent to its
boundary.

The final theorems discharge the locality premise used by
`InPlaceTwoWindowBlockFold` for stable per-block lists of a timed schedule.
-/

/-- The lower endpoint of the bucket's left adjacent source block is no
greater than any candidate in that bucket. -/
theorem advertisedBlockLower_leftSource_le_fullBucketBoundary
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (bucket : Fin (T / b)) (candidate : Fin b) :
    advertisedBlockLower offsets (leftSourceBlockOfBucket bucket) ≤
      (fullBucketBoundary bucket candidate).val := by
  let left : Fin (T / b + 1) := leftSourceBlockOfBucket bucket
  by_cases hzero : bucket.val = 0
  · have hleftZero : left.val = 0 := by
      simp [left, leftSourceBlockOfBucket, hzero]
    rw [advertisedBlockLower_of_val_eq_zero offsets left hleftZero]
    omega
  · have hbucketPos : 0 < bucket.val := Nat.pos_of_ne_zero hzero
    have hleftPos : 0 < left.val := by
      simpa [left, leftSourceBlockOfBucket] using hbucketPos
    let previous : Fin (T / b) := ⟨bucket.val - 1, by omega⟩
    have hpreviousUpper :=
      fullBucketBoundary_upper previous (offsets previous)
    have hcandidateLower := fullBucketBoundary_lower bucket candidate
    have hindex : previous.val + 1 = bucket.val := by
      simp only [previous]
      omega
    rw [advertisedBlockLower_of_val_pos offsets left hleftPos]
    change
      (fullBucketBoundary
          (⟨left.val - 1, by omega⟩ : Fin (T / b))
          (offsets ⟨left.val - 1, by omega⟩)).val + 1 ≤
        (fullBucketBoundary bucket candidate).val
    have hprevEq :
        (⟨left.val - 1, by omega⟩ : Fin (T / b)) = previous := by
      apply Fin.ext
      simp [left, leftSourceBlockOfBucket, previous]
    rw [hprevEq]
    rw [hindex] at hpreviousUpper
    omega

/-- Every bucket candidate lies strictly before the exclusive endpoint of
the bucket's right adjacent source block. -/
theorem fullBucketBoundary_succ_lt_advertisedBlockUpper_rightSource
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (bucket : Fin (T / b)) (candidate : Fin b) :
    (fullBucketBoundary bucket candidate).val + 1 <
      advertisedBlockUpperExclusive offsets
        (rightSourceBlockOfBucket bucket) := by
  let right : Fin (T / b + 1) := rightSourceBlockOfBucket bucket
  by_cases hnext : right.val < T / b
  · let nextBucket : Fin (T / b) := ⟨right.val, hnext⟩
    have hcandidateUpper := fullBucketBoundary_upper bucket candidate
    have hnextLower := fullBucketBoundary_lower nextBucket (offsets nextBucket)
    have hindex : bucket.val + 1 = nextBucket.val := by
      simp [right, rightSourceBlockOfBucket, nextBucket]
    rw [advertisedBlockUpperExclusive_of_val_lt offsets right hnext]
    change (fullBucketBoundary bucket candidate).val + 1 <
      (fullBucketBoundary nextBucket (offsets nextBucket)).val + 1
    rw [hindex] at hcandidateUpper
    omega
  · rw [advertisedBlockUpperExclusive_of_not_val_lt offsets right hnext]
    exact Nat.add_lt_add_right (fullBucketBoundary bucket candidate).isLt 1

/-- A block not equal to either adjacent source block is entirely separated
from the candidate boundary: it ends on the left, or starts strictly beyond
the boundary's right cell. -/
theorem nonadjacentAdvertisedBlock_separated_from_fullBucketBoundary
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (bucket : Fin (T / b)) (candidate : Fin b)
    (block : Fin (T / b + 1))
    (hneLeft : block ≠ leftSourceBlockOfBucket bucket)
    (hneRight : block ≠ rightSourceBlockOfBucket bucket) :
    advertisedBlockLower offsets block + advertisedBlockWidth offsets block ≤
        (fullBucketBoundary bucket candidate).val ∨
      (fullBucketBoundary bucket candidate).val + 1 <
        advertisedBlockLower offsets block := by
  let left : Fin (T / b + 1) := leftSourceBlockOfBucket bucket
  let right : Fin (T / b + 1) := rightSourceBlockOfBucket bucket
  have hleftVal : left.val = bucket.val := rfl
  have hrightVal : right.val = bucket.val + 1 := rfl
  have hblockNeLeftVal : block.val ≠ left.val := by
    intro hval
    exact hneLeft (Fin.ext hval)
  have hblockNeRightVal : block.val ≠ right.val := by
    intro hval
    exact hneRight (Fin.ext hval)
  have horder : block < left ∨ right < block := by
    omega
  rcases horder with hbefore | hafter
  · left
    have hblocks := advertisedBlockUpperExclusive_le_lower_of_lt
      offsets hbefore
    have hcandidate :=
      advertisedBlockLower_leftSource_le_fullBucketBoundary
        offsets bucket candidate
    have hendpoint :=
      advertisedBlockLower_add_width_eq_upperExclusive offsets block
    simpa [left] using hendpoint.trans_le (hblocks.trans hcandidate)
  · right
    have hblocks := advertisedBlockUpperExclusive_le_lower_of_lt
      offsets hafter
    have hcandidate :=
      fullBucketBoundary_succ_lt_advertisedBlockUpper_rightSource
        offsets bucket candidate
    exact hcandidate.trans_le (by simpa [right] using hblocks)

/-- If every pre-transition head stays in a slab separated from a boundary,
the recursive streaming counter is zero.  The final transition is covered
because its source head is among the quantified pre-heads. -/
theorem streamingWorkBoundaryCrossingCountFrom_eq_zero_of_inside_separated
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps boundary base width : Nat)
    (hinside : ∀ time : Fin steps,
      WorkCellInSlab base width
        (runFrom machine input config time.val).workHead)
    (hseparated : base + width ≤ boundary ∨ boundary + 1 < base) :
    streamingWorkBoundaryCrossingCountFrom machine input config
      steps boundary = 0 := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      have hcurrent := hinside ⟨0, by omega⟩
      have hsourceAway : config.workHead ≠ boundary ∧
          config.workHead ≠ boundary + 1 := by
        have hrunZero :
            (runFrom machine input config 0).workHead = config.workHead := rfl
        rw [hrunZero] at hcurrent
        unfold WorkCellInSlab at hcurrent
        rcases hseparated with hleft | hright
        · constructor <;> omega
        · constructor <;> omega
      have hnotCrosses : ¬ CrossesWorkBoundary boundary config.workHead
          (step machine input config).workHead := by
        intro hcross
        rcases hcross with hcross | hcross <;>
          rcases hcross with ⟨hfrom, _⟩
        · exact hsourceAway.1 hfrom
        · exact hsourceAway.2 hfrom
      simp only [streamingWorkBoundaryCrossingCountFrom, hnotCrosses,
        if_false, Nat.zero_add]
      apply ih
      intro time
      have htail := hinside ⟨time.val + 1, by omega⟩
      simpa only [runFrom_succ] using htail

/-- One locally valid visit of a nonadjacent source block contributes zero
to every candidate boundary of the bucket. -/
theorem fixedAlphaBlockVisitStreamingCrossingCount_eq_zero_of_nonadjacent
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (bucket : Fin (T / b)) (candidate : Fin b)
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hvalid : FixedAlphaBlockVisitValid
      machine input alpha block visit carried)
    (hneLeft : block ≠ leftSourceBlockOfBucket bucket)
    (hneRight : block ≠ rightSourceBlockOfBucket bucket) :
    streamingWorkBoundaryCrossingCountFrom machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps (fullBucketBoundary bucket candidate).val = 0 := by
  apply streamingWorkBoundaryCrossingCountFrom_eq_zero_of_inside_separated
    machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps (fullBucketBoundary bucket candidate).val
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block)
  · exact hvalid.1
  · exact nonadjacentAdvertisedBlock_separated_from_fullBucketBoundary
      alpha.offsets bucket candidate block hneLeft hneRight

/-- The zero contribution persists through the slab-threaded recursive
replay relation for an arbitrary fixed block visit list. -/
theorem fixedAlphaBlockVisitListStreamingCrossingCount_eq_zero_of_nonadjacent
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (bucket : Fin (T / b)) (candidate : Fin b)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      machine input alpha block carried visits)
    (hneLeft : block ≠ leftSourceBlockOfBucket bucket)
    (hneRight : block ≠ rightSourceBlockOfBucket bucket) :
    fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
      (fullBucketBoundary bucket candidate).val carried visits = 0 := by
  induction visits generalizing carried with
  | nil => rfl
  | cons visit rest ih =>
      have hvisit :=
        fixedAlphaBlockVisitStreamingCrossingCount_eq_zero_of_nonadjacent
          machine input alpha block bucket candidate visit carried
          haccepted.1 hneLeft hneRight
      simp only [fixedAlphaBlockVisitListStreamingCrossingCount]
      rw [hvisit, Nat.zero_add]
      exact ih
        (fixedAlphaBlockVisitOutputSlab
          machine input alpha block visit carried)
        haccepted.2

/-- Public valid-list version of the recursive zero theorem. -/
theorem fixedAlphaBlockVisitListAccepted_crossingCount_eq_zero_of_nonadjacent
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (bucket : Fin (T / b)) (candidate : Fin b)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (haccepted : FixedAlphaBlockVisitListAccepted
      machine input alpha block initialSlab visits)
    (hneLeft : block ≠ leftSourceBlockOfBucket bucket)
    (hneRight : block ≠ rightSourceBlockOfBucket bucket) :
    fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
      (fullBucketBoundary bucket candidate).val initialSlab visits = 0 := by
  exact fixedAlphaBlockVisitListStreamingCrossingCount_eq_zero_of_nonadjacent
    machine input alpha block bucket candidate initialSlab visits
    haccepted.2 hneLeft hneRight

/-- Simultaneous blank-start acceptance of all stable block sublists
discharges the nonadjacent-zero premise used by the rolling two-window fold. -/
theorem timedAlphaBlockVisits_nonadjacent_crossingContribution_eq_zero
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hall : ∀ target : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        machine input alpha target (timedAlphaBlockVisits target scheduled))
    (bucket : Fin (T / b)) (candidate : Fin b)
    (block : Fin (T / b + 1))
    (hneLeft : block ≠ leftSourceBlockOfBucket bucket)
    (hneRight : block ≠ rightSourceBlockOfBucket bucket) :
    fixedAlphaSourceBlockCrossingContribution machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) block
        (fullBucketBoundary bucket candidate) = 0 := by
  unfold fixedAlphaSourceBlockCrossingContribution
  apply fixedAlphaBlockVisitListAccepted_crossingCount_eq_zero_of_nonadjacent
    machine input alpha block bucket candidate
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (timedAlphaBlockVisits block scheduled)
  · exact hall block
  · exact hneLeft
  · exact hneRight

/-- The executable all-block checker therefore implies nonadjacent locality
for every full bucket and candidate, including all edge cases. -/
theorem timedAlphaAllBlockVisitsCheckFromBlank_nonadjacent_zero
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaAllBlockVisitsCheckFromBlank
      machine input alpha scheduled = true) :
    ∀ (bucket : Fin (T / b)) (candidate : Fin b)
      (block : Fin (T / b + 1)),
      block ≠ leftSourceBlockOfBucket bucket →
      block ≠ rightSourceBlockOfBucket bucket →
      fixedAlphaSourceBlockCrossingContribution machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) block
        (fullBucketBoundary bucket candidate) = 0 := by
  have hall :=
    (timedAlphaAllBlockVisitsCheckFromBlank_eq_true_iff
      machine input alpha scheduled).1 hcheck
  intro bucket candidate block hneLeft hneRight
  exact timedAlphaBlockVisits_nonadjacent_crossingContribution_eq_zero
    machine input alpha scheduled hall bucket candidate block
    hneLeft hneRight

/-- The combined schedule/all-block checkpoint exposes the same locality
fact directly. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCheck_nonadjacent_zero
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha scheduled = true) :
    ∀ (bucket : Fin (T / b)) (candidate : Fin b)
      (block : Fin (T / b + 1)),
      block ≠ leftSourceBlockOfBucket bucket →
      block ≠ rightSourceBlockOfBucket bucket →
      fixedAlphaSourceBlockCrossingContribution machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) block
        (fullBucketBoundary bucket candidate) = 0 := by
  have hall :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input alpha scheduled).1 hcheck |>.2
  intro bucket candidate block hneLeft hneRight
  exact timedAlphaBlockVisits_nonadjacent_crossingContribution_eq_zero
    machine input alpha scheduled hall bucket candidate block
    hneLeft hneRight

/-- Thus, once the independent all-source sum identity is supplied, the
executable all-block check is enough to derive the exact adjacent-source
decomposition.  The former nonadjacent-locality premise is no longer exposed
to callers. -/
theorem timedScheduleAdjacentSourceDecomposesActual_of_sum_and_allBlockCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hsum : ∀ boundary : Fin T,
      sourceBlockSummedCrossingProfile machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled) boundary =
        actualWorkBoundaryCrossingProfile machine input T boundary)
    (hcheck : timedAlphaAllBlockVisitsCheckFromBlank
      machine input alpha scheduled = true) :
    TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled := by
  apply timedScheduleAdjacentSourceDecomposesActual_of_sum_and_locality
    machine input alpha scheduled hsum
  exact timedAlphaAllBlockVisitsCheckFromBlank_nonadjacent_zero
    machine input alpha scheduled hcheck

end OneTapeMagnification
end Frontier
end Pnp4
