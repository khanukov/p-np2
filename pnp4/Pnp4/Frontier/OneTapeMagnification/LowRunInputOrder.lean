import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Pairwise

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Low-run input orders from stable work-block grouping

This file isolates an order-theoretic fact behind path/transcript
decompositions.  A finite trace records, in chronological order, the current
input-head position and the work block responsible for the transition.
`advances = false` represents a stay transition: after the input-cache
normalization it does not query a new input symbol and is therefore omitted
from the branching-program query order.

Stable grouping means filtering the trace once for each occupied work block,
in block-number order, and concatenating the filters.  Each filter preserves
the chronological order.  Consequently:

* all input-head positions form nondecreasing runs when the one-way input head
  is allowed to stay;
* after stay transitions are omitted, fresh query positions form strictly
  increasing runs under the cache-normalized freshness hypothesis; and
* the number of runs is at most the number of occupied blocks, hence at most
  the total number of blocks (in particular, `K + 1`).

The final definition states the additional uniformity needed for an
*oblivious read-once* branching program: one fixed, duplicate-free query list
must serve every input in the family.  A low-run decomposition of individual
traces does not by itself prove that uniformity, and no Viola simulation is
claimed here.
-/

/-- One transition in a chronological one-way-input trace.

`inputPosition` may be repeated by stay transitions.  The Boolean
`advances` records exactly whether the transition exposes a fresh input
coordinate after input-cache normalization. -/
structure InputReadEvent (blockCount : Nat) where
  chronologicalPosition : Nat
  workBlock : Fin blockCount
  inputPosition : Nat
  advances : Bool
deriving DecidableEq, Repr

/-- Events assigned to one work block, in their original (stable) order. -/
def inputEventsInBlock {blockCount : Nat} (block : Fin blockCount)
    (events : List (InputReadEvent blockCount)) :
    List (InputReadEvent blockCount) :=
  events.filter fun event => event.workBlock == block

/-- Stay transitions are ignored by the normalized branching-program query
order.  They remain present in the raw chronological trace. -/
def advancingInputEvents {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    List (InputReadEvent blockCount) :=
  events.filter fun event => event.advances

/-- Raw input-head positions, including duplicates caused by stays. -/
def rawInputPositions {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) : List Nat :=
  events.map InputReadEvent.inputPosition

/-- Query positions after ignored stay transitions have been removed. -/
def freshInputPositions {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) : List Nat :=
  (advancingInputEvents events).map InputReadEvent.inputPosition

/-- Explicit optional-query view of an event: a stay transition contributes
`none`, while an advancing transition contributes its fresh coordinate. -/
def freshInputQuery? {blockCount : Nat}
    (event : InputReadEvent blockCount) : Option Nat :=
  if event.advances then some event.inputPosition else none

/-- Filtering ignored stays and then mapping positions is exactly the same as
`filterMap` with the optional-query view. -/
theorem freshInputPositions_eq_filterMap {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    freshInputPositions events = events.filterMap freshInputQuery? := by
  unfold freshInputPositions advancingInputEvents
  rw [← List.filterMap_eq_map']
  simpa only [freshInputQuery?] using
    (List.filterMap_filter
      (p := fun event : InputReadEvent blockCount => event.advances)
      (f := fun event => some event.inputPosition) (l := events))

/-- Removing stays deletes occurrences but does not reorder or alter the
remaining input positions.  In particular, this theorem does not silently
deduplicate two advancing events at the same coordinate. -/
theorem freshInputPositions_sublist_rawInputPositions {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    List.Sublist (freshInputPositions events) (rawInputPositions events) := by
  unfold freshInputPositions rawInputPositions advancingInputEvents
  exact (List.filter_sublist.map InputReadEvent.inputPosition)

/-- One-way monotonicity of the raw head positions descends to the fresh
queries.  Strictness is deliberately absent: it requires the separate
cache-normalized freshness condition used below. -/
theorem freshInputPositions_pairwise_le_of_raw
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hOneWay : (rawInputPositions events).Pairwise (· ≤ ·)) :
    (freshInputPositions events).Pairwise (· ≤ ·) :=
  hOneWay.sublist (freshInputPositions_sublist_rawInputPositions events)

/-- Blocks which occur in the trace, listed in increasing block-number order.
The use of `filter` makes the subsequent grouping stable inside every block. -/
def occupiedInputBlocks {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) : List (Fin blockCount) :=
  (List.finRange blockCount).filter fun block =>
    events.any fun event => event.workBlock == block

/-- Stable block segments of an arbitrary event projection. -/
def stableInputBlockSegments {blockCount : Nat} {α : Type}
    (project : InputReadEvent blockCount → α)
    (events : List (InputReadEvent blockCount)) : List (List α) :=
  (occupiedInputBlocks events).map fun block =>
    (inputEventsInBlock block events).map project

/-- The stable block-grouped order of an arbitrary projection. -/
def stableGroupedInputOrder {blockCount : Nat} {α : Type}
    (project : InputReadEvent blockCount → α)
    (events : List (InputReadEvent blockCount)) : List α :=
  (stableInputBlockSegments project events).flatten

/-- Stable block-grouped raw input positions.  Equal adjacent values within a
run are permitted because a raw trace still contains stays. -/
def stableGroupedRawInputPositions {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) : List Nat :=
  stableGroupedInputOrder InputReadEvent.inputPosition events

/-- Stable block-grouped fresh query positions. -/
def stableGroupedFreshInputPositions {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) : List Nat :=
  stableGroupedInputOrder InputReadEvent.inputPosition
    (advancingInputEvents events)

/-- A list is a concatenation of at most `bound` runs satisfying `relation`.
Empty runs are harmless, although the concrete occupied-block construction
does not intentionally introduce them. -/
def HasAtMostInputRuns (relation : Nat → Nat → Prop) (bound : Nat)
    (order : List Nat) : Prop :=
  ∃ runs : List (List Nat),
    runs.length ≤ bound ∧
      (∀ run ∈ runs, run.Pairwise relation) ∧
      runs.flatten = order

/-- Increasing the run budget preserves a run decomposition. -/
theorem HasAtMostInputRuns.mono {relation : Nat → Nat → Prop}
    {smaller larger : Nat} {order : List Nat}
    (hRuns : HasAtMostInputRuns relation smaller order)
    (hBudget : smaller ≤ larger) :
    HasAtMostInputRuns relation larger order := by
  obtain ⟨runs, hLength, hPairwise, hFlatten⟩ := hRuns
  exact ⟨runs, hLength.trans hBudget, hPairwise, hFlatten⟩

/-- There cannot be more occupied blocks than blocks. -/
theorem occupiedInputBlocks_length_le {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    (occupiedInputBlocks events).length ≤ blockCount := by
  calc
    (occupiedInputBlocks events).length ≤ (List.finRange blockCount).length := by
      exact List.length_filter_le _ _
    _ = blockCount := by simp

/-- A stable block filter preserves every pairwise order property of a
projection.  This is the generic core used for chronology and query indices. -/
theorem inputEventsInBlock_projection_pairwise
    {blockCount : Nat} {α : Type}
    (project : InputReadEvent blockCount → α) (relation : α → α → Prop)
    (events : List (InputReadEvent blockCount)) (block : Fin blockCount)
    (hPairwise : (events.map project).Pairwise relation) :
    ((inputEventsInBlock block events).map project).Pairwise relation := by
  apply List.pairwise_map.mpr
  exact (List.pairwise_map.mp hPairwise).filter _

/-- Every segment produced by stable grouping inherits the pairwise order of
the original projected trace. -/
theorem stableInputBlockSegments_pairwise
    {blockCount : Nat} {α : Type}
    (project : InputReadEvent blockCount → α) (relation : α → α → Prop)
    (events : List (InputReadEvent blockCount))
    (hPairwise : (events.map project).Pairwise relation) :
    ∀ segment ∈ stableInputBlockSegments project events,
      segment.Pairwise relation := by
  intro segment hSegment
  simp only [stableInputBlockSegments, List.mem_map] at hSegment
  obtain ⟨block, -, rfl⟩ := hSegment
  exact inputEventsInBlock_projection_pairwise
    project relation events block hPairwise

/-- Strict chronology is split into at most one strict run per occupied work
block.  Grouping changes the order between blocks but not inside a block. -/
theorem stableGroupedChronology_has_occupied_strict_runs
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hChronological :
      (events.map InputReadEvent.chronologicalPosition).Pairwise (· < ·)) :
    HasAtMostInputRuns (· < ·) (occupiedInputBlocks events).length
      (stableGroupedInputOrder InputReadEvent.chronologicalPosition events) := by
  refine ⟨stableInputBlockSegments InputReadEvent.chronologicalPosition events,
    ?_, ?_, rfl⟩
  · simp [stableInputBlockSegments]
  · exact stableInputBlockSegments_pairwise
      InputReadEvent.chronologicalPosition (· < ·) events hChronological

/-- With a one-way input head, raw positions (including duplicate positions
from stays) split into nondecreasing stable block runs. -/
theorem stableGroupedRawInputPositions_has_occupied_nondecreasing_runs
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hOneWay : (rawInputPositions events).Pairwise (· ≤ ·)) :
    HasAtMostInputRuns (· ≤ ·) (occupiedInputBlocks events).length
      (stableGroupedRawInputPositions events) := by
  refine ⟨stableInputBlockSegments InputReadEvent.inputPosition events,
    ?_, ?_, rfl⟩
  · simp [stableInputBlockSegments]
  · exact stableInputBlockSegments_pairwise
      InputReadEvent.inputPosition (· ≤ ·) events hOneWay

/-- After cache normalization, only advancing events query fresh positions.
If those positions are strictly increasing in chronological order, stable
grouping yields strictly increasing query runs, one per occupied advancing
block. -/
theorem stableGroupedFreshInputPositions_has_occupied_strict_runs
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hFresh : (freshInputPositions events).Pairwise (· < ·)) :
    HasAtMostInputRuns (· < ·)
      (occupiedInputBlocks (advancingInputEvents events)).length
      (stableGroupedFreshInputPositions events) := by
  refine ⟨stableInputBlockSegments InputReadEvent.inputPosition
      (advancingInputEvents events), ?_, ?_, rfl⟩
  · simp [stableInputBlockSegments]
  · exact stableInputBlockSegments_pairwise
      InputReadEvent.inputPosition (· < ·) (advancingInputEvents events) hFresh

/-- The strict chronology result with the coarse but often convenient
`blockCount` bound. -/
theorem stableGroupedChronology_has_at_most_blockCount_strict_runs
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hChronological :
      (events.map InputReadEvent.chronologicalPosition).Pairwise (· < ·)) :
    HasAtMostInputRuns (· < ·) blockCount
      (stableGroupedInputOrder InputReadEvent.chronologicalPosition events) :=
  (stableGroupedChronology_has_occupied_strict_runs events hChronological).mono
    (occupiedInputBlocks_length_le events)

/-- The raw one-way query order has at most `blockCount` nondecreasing runs. -/
theorem stableGroupedRawInputPositions_has_at_most_blockCount_runs
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hOneWay : (rawInputPositions events).Pairwise (· ≤ ·)) :
    HasAtMostInputRuns (· ≤ ·) blockCount
      (stableGroupedRawInputPositions events) :=
  (stableGroupedRawInputPositions_has_occupied_nondecreasing_runs events hOneWay).mono
    (occupiedInputBlocks_length_le events)

/-- The normalized fresh query order has at most `blockCount` strict runs. -/
theorem stableGroupedFreshInputPositions_has_at_most_blockCount_strict_runs
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hFresh : (freshInputPositions events).Pairwise (· < ·)) :
    HasAtMostInputRuns (· < ·) blockCount
      (stableGroupedFreshInputPositions events) :=
  (stableGroupedFreshInputPositions_has_occupied_strict_runs events hFresh).mono
    (occupiedInputBlocks_length_le (advancingInputEvents events))

/-- The `K + 1` form used when `K` separators induce `K + 1` work blocks. -/
theorem stableGroupedFreshInputPositions_has_at_most_K_add_one_strict_runs
    {K : Nat} (events : List (InputReadEvent (K + 1)))
    (hFresh : (freshInputPositions events).Pairwise (· < ·)) :
    HasAtMostInputRuns (· < ·) (K + 1)
      (stableGroupedFreshInputPositions events) :=
  stableGroupedFreshInputPositions_has_at_most_blockCount_strict_runs
    events hFresh

/-- Strictly increasing fresh coordinates are duplicate-free, hence form a
read-once order for this single trace. -/
theorem freshInputPositions_nodup_of_strict
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hFresh : (freshInputPositions events).Pairwise (· < ·)) :
    (freshInputPositions events).Nodup :=
  hFresh.imp fun hLess => Nat.ne_of_lt hLess

/-- The right semantic obligation for an oblivious read-once branching
program over a family of inputs: all inputs use one fixed query order, and
that common order has no repeated coordinate.

The function `queryOrder` may be instantiated by a stable grouped order only
after proving it is input-independent.  The low-run theorems above do not
establish that extra fact. -/
def HasObliviousReadOnceInputOrder {inputIndex : Type}
    (queryOrder : inputIndex → List Nat) : Prop :=
  ∃ fixedOrder : List Nat,
    fixedOrder.Nodup ∧ ∀ input, queryOrder input = fixedOrder

end OneTapeMagnification
end Frontier
end Pnp4
