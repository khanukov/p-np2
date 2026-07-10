import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped List

/-!
# A fixed crossing schedule determines a read-once input order

This file isolates the input-order consequence of fixing a finite crossing
schedule `alpha`.  A chronological segment names its work block and the
half-open interval of fresh input coordinates consumed while that segment is
replayed.  The indexed chaining predicate says exactly that consecutive
segments share endpoints.

Under this chaining condition, chronological concatenation is one half-open
interval and is therefore duplicate-free.  Stable grouping by work block is
a permutation of that chronological concatenation, so its complete query
order is duplicate-free too.  Unlike an input-by-input block classifier, the
order here is a function only of the fixed schedule value.

The remaining machine-level obligation is deliberately outside this module:
one must prove that every actual block replay assigned to `alpha` consumes
exactly the endpoints recorded in these segments.  No replay theorem,
branching-program width bound, or transcript-count bound is claimed here.
-/

/-- One chronological segment of a fixed crossing schedule.  It consumes
the fresh input coordinates in `[startPosition, stopPosition)`. -/
structure CrossingScheduleSegment (blockCount : Nat) where
  workBlock : Fin blockCount
  startPosition : Nat
  stopPosition : Nat
  start_le_stop : startPosition ≤ stopPosition
deriving DecidableEq, Repr

/-- Fresh coordinates consumed by one segment, in chronological order. -/
def CrossingScheduleSegment.freshQueries {blockCount : Nat}
    (segment : CrossingScheduleSegment blockCount) : List Nat :=
  List.range' segment.startPosition
    (segment.stopPosition - segment.startPosition)

@[simp]
theorem CrossingScheduleSegment.freshQueries_length {blockCount : Nat}
    (segment : CrossingScheduleSegment blockCount) :
    segment.freshQueries.length =
      segment.stopPosition - segment.startPosition := by
  simp [CrossingScheduleSegment.freshQueries]

/-- Indexed adjacent-endpoint chaining.  The indices expose the first and
final input positions.  In the `cons` constructor, the tail starts exactly at
the current segment's stop, so adjacent endpoints agree definitionally. -/
inductive ChainedCrossingSchedule {blockCount : Nat} :
    Nat → Nat → List (CrossingScheduleSegment blockCount) → Prop
  | nil (position : Nat) :
      ChainedCrossingSchedule position position []
  | cons (segment : CrossingScheduleSegment blockCount)
      {finalPosition : Nat}
      {tail : List (CrossingScheduleSegment blockCount)}
      (hTail : ChainedCrossingSchedule
        segment.stopPosition finalPosition tail) :
      ChainedCrossingSchedule
        segment.startPosition finalPosition (segment :: tail)

/-- The ordinary adjacent-pair view of endpoint chaining. -/
def HasAdjacentCrossingEndpoints {blockCount : Nat}
    (segments : List (CrossingScheduleSegment blockCount)) : Prop :=
  segments.Chain' fun earlier later =>
    earlier.stopPosition = later.startPosition

/-- The exposed start index of a nonempty chain is the head segment's start. -/
theorem ChainedCrossingSchedule.start_eq_head
    {blockCount : Nat} {startPosition stopPosition : Nat}
    {head : CrossingScheduleSegment blockCount}
    {tail : List (CrossingScheduleSegment blockCount)}
    (hChain : ChainedCrossingSchedule
      startPosition stopPosition (head :: tail)) :
    startPosition = head.startPosition := by
  cases hChain
  rfl

/-- The indexed schedule relation really does enforce equality at every
adjacent pair of segment endpoints. -/
theorem ChainedCrossingSchedule.hasAdjacentCrossingEndpoints
    {blockCount : Nat} {startPosition stopPosition : Nat}
    {segments : List (CrossingScheduleSegment blockCount)}
    (hChain : ChainedCrossingSchedule
      startPosition stopPosition segments) :
    HasAdjacentCrossingEndpoints segments := by
  induction hChain with
  | nil => simp [HasAdjacentCrossingEndpoints]
  | @cons segment finalPosition tail hTail ih =>
      cases tail with
      | nil => simp [HasAdjacentCrossingEndpoints]
      | cons next rest =>
          have hAdjacent :
              segment.stopPosition = next.startPosition :=
            hTail.start_eq_head
          simpa [HasAdjacentCrossingEndpoints, hAdjacent] using ih

/-- Chaining and the per-segment endpoint inequalities imply monotonicity of
the overall schedule endpoints. -/
theorem ChainedCrossingSchedule.start_le_stop {blockCount : Nat}
    {startPosition stopPosition : Nat}
    {segments : List (CrossingScheduleSegment blockCount)}
    (hChain : ChainedCrossingSchedule
      startPosition stopPosition segments) :
    startPosition ≤ stopPosition := by
  induction hChain with
  | nil => exact Nat.le_refl _
  | cons segment hTail ih =>
      exact segment.start_le_stop.trans ih

/-- A fixed finite crossing schedule, including its exposed overall input
endpoints and the proof that all adjacent segment endpoints chain. -/
structure FixedCrossingSchedule (blockCount : Nat) where
  startPosition : Nat
  stopPosition : Nat
  segments : List (CrossingScheduleSegment blockCount)
  chained : ChainedCrossingSchedule startPosition stopPosition segments

/-- Chronological concatenation of every segment's fresh coordinates. -/
def chronologicalCrossingScheduleInputOrder {blockCount : Nat}
    (segments : List (CrossingScheduleSegment blockCount)) : List Nat :=
  segments.flatMap CrossingScheduleSegment.freshQueries

/-- Adjacent half-open intervals concatenate to their combined half-open
interval. -/
theorem range'_sub_append_range'_sub {start middle stop : Nat}
    (hStartMiddle : start ≤ middle) (hMiddleStop : middle ≤ stop) :
    List.range' start (middle - start) ++
        List.range' middle (stop - middle) =
      List.range' start (stop - start) := by
  have hMiddle : start + (middle - start) = middle := by omega
  have hLength :
      (middle - start) + (stop - middle) = stop - start := by omega
  simpa [hMiddle, hLength] using
    (List.range'_append
      (s := start) (m := middle - start) (n := stop - middle)
      (step := 1))

/-- A chained chronological concatenation is exactly one half-open interval. -/
theorem chronologicalCrossingScheduleInputOrder_eq_range'
    {blockCount : Nat} {startPosition stopPosition : Nat}
    {segments : List (CrossingScheduleSegment blockCount)}
    (hChain : ChainedCrossingSchedule
      startPosition stopPosition segments) :
    chronologicalCrossingScheduleInputOrder segments =
      List.range' startPosition (stopPosition - startPosition) := by
  induction hChain with
  | nil => simp [chronologicalCrossingScheduleInputOrder]
  | cons segment hTail ih =>
      change segment.freshQueries ++
          chronologicalCrossingScheduleInputOrder _ = _
      rw [ih]
      simpa [CrossingScheduleSegment.freshQueries] using
        (range'_sub_append_range'_sub segment.start_le_stop
          hTail.start_le_stop)

/-- Therefore the complete chronological query order is duplicate-free. -/
theorem chronologicalCrossingScheduleInputOrder_nodup
    {blockCount : Nat} {startPosition stopPosition : Nat}
    {segments : List (CrossingScheduleSegment blockCount)}
    (hChain : ChainedCrossingSchedule
      startPosition stopPosition segments) :
    (chronologicalCrossingScheduleInputOrder segments).Nodup := by
  rw [chronologicalCrossingScheduleInputOrder_eq_range' hChain]
  exact List.nodup_range'

/-- Stable grouping of segments by every work-block label.  Empty block
groups are retained; they contribute no queries. -/
def stableGroupedCrossingScheduleSegments {blockCount : Nat}
    (segments : List (CrossingScheduleSegment blockCount)) :
    List (CrossingScheduleSegment blockCount) :=
  (List.finRange blockCount).flatMap fun block =>
    segments.filter fun segment => segment.workBlock == block

/-- Stable grouping preserves the exact segment multiset, including the
multiplicity of structurally identical segments. -/
theorem stableGroupedCrossingScheduleSegments_perm {blockCount : Nat}
    (segments : List (CrossingScheduleSegment blockCount)) :
    stableGroupedCrossingScheduleSegments segments ~ segments := by
  rw [List.perm_iff_count]
  intro segment
  unfold stableGroupedCrossingScheduleSegments
  simp only [List.count_flatMap]
  rw [← List.sum_toFinset _ (List.nodup_finRange blockCount),
    List.toFinset_finRange]
  rw [Finset.sum_eq_single segment.workBlock]
  · exact List.count_filter (by simp)
  · intro block _ hNe
    apply List.count_eq_zero.mpr
    intro hFiltered
    have hEq : segment.workBlock = block := by
      simpa using (List.mem_filter.mp hFiltered).2
    exact hNe hEq.symm
  · simp

/-- Query order obtained by replaying all segments in stable work-block
order.  It is computed solely from the supplied schedule segments. -/
def stableGroupedCrossingScheduleInputOrder {blockCount : Nat}
    (segments : List (CrossingScheduleSegment blockCount)) : List Nat :=
  (stableGroupedCrossingScheduleSegments segments).flatMap
    CrossingScheduleSegment.freshQueries

/-- Stable work-block grouping permutes, but neither drops nor duplicates,
the complete chronological query order. -/
theorem stableGroupedCrossingScheduleInputOrder_perm {blockCount : Nat}
    (segments : List (CrossingScheduleSegment blockCount)) :
    stableGroupedCrossingScheduleInputOrder segments ~
      chronologicalCrossingScheduleInputOrder segments := by
  unfold stableGroupedCrossingScheduleInputOrder
    chronologicalCrossingScheduleInputOrder
  exact (stableGroupedCrossingScheduleSegments_perm segments).flatMap
    (fun _ _ => List.Perm.rfl)

/-- Stable grouping of a chained schedule is a trace-wide read-once order. -/
theorem stableGroupedCrossingScheduleInputOrder_nodup
    {blockCount : Nat} {startPosition stopPosition : Nat}
    {segments : List (CrossingScheduleSegment blockCount)}
    (hChain : ChainedCrossingSchedule
      startPosition stopPosition segments) :
    (stableGroupedCrossingScheduleInputOrder segments).Nodup := by
  exact (stableGroupedCrossingScheduleInputOrder_perm segments).symm.nodup
    (chronologicalCrossingScheduleInputOrder_nodup hChain)

/-- The fixed grouped query order exposed by a schedule value `alpha`. -/
def FixedCrossingSchedule.readOnceInputOrder {blockCount : Nat}
    (alpha : FixedCrossingSchedule blockCount) : List Nat :=
  stableGroupedCrossingScheduleInputOrder alpha.segments

/-- The order determined by one fixed schedule value is duplicate-free. -/
theorem FixedCrossingSchedule.readOnceInputOrder_nodup {blockCount : Nat}
    (alpha : FixedCrossingSchedule blockCount) :
    alpha.readOnceInputOrder.Nodup :=
  stableGroupedCrossingScheduleInputOrder_nodup alpha.chained

/-- The fixed grouped order contains exactly the same query occurrences as
the single chronological interval exposed by the schedule endpoints. -/
theorem FixedCrossingSchedule.readOnceInputOrder_perm_range'
    {blockCount : Nat} (alpha : FixedCrossingSchedule blockCount) :
    alpha.readOnceInputOrder ~
      List.range' alpha.startPosition
        (alpha.stopPosition - alpha.startPosition) := by
  exact (stableGroupedCrossingScheduleInputOrder_perm alpha.segments).trans
    (List.Perm.of_eq
      (chronologicalCrossingScheduleInputOrder_eq_range' alpha.chained))

end OneTapeMagnification
end Frontier
end Pnp4
