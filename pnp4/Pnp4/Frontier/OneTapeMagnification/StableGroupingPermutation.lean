import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualRunInputOrder

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped List

/-!
# Stable block grouping is a permutation

`LowRunInputOrder` groups a chronological event list by its occupied work
blocks.  The grouping changes the order between blocks, but it neither drops
nor duplicates events.  This file records that exact multiset statement and
its consequence for the fresh input-coordinate projection.

In particular, strictly increasing advancing coordinates are duplicate-free
before grouping, so the complete block-grouped query list is duplicate-free
as well.  This is a trace-local read-once statement.  The block classifier,
and therefore the resulting permutation, may still depend on the input.  An
oblivious branching-program simulation still has to prove that a fixed path
transcript determines one common order; no such input-independence is claimed
here.
-/

/-- The event list itself, stably grouped by its occupied work blocks. -/
def stableGroupedInputEvents {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    List (InputReadEvent blockCount) :=
  stableGroupedInputOrder id events

/-- Stable grouping over all block labels, including unoccupied labels. -/
def stableGroupedInputEventsAllBlocks {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    List (InputReadEvent blockCount) :=
  (List.finRange blockCount).flatMap fun block =>
    inputEventsInBlock block events

/-- Filtering out unoccupied labels does not change the flattened grouping. -/
theorem stableGroupedInputEvents_eq_allBlocks {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    stableGroupedInputEvents events =
      stableGroupedInputEventsAllBlocks events := by
  unfold stableGroupedInputEvents stableGroupedInputOrder
    stableInputBlockSegments stableGroupedInputEventsAllBlocks
    occupiedInputBlocks
  induction List.finRange blockCount with
  | nil => simp
  | cons block blocks ih =>
      have ih' :
          (List.map (fun block => inputEventsInBlock block events)
            (List.filter
              (fun block => events.any fun event => event.workBlock == block)
              blocks)).flatten =
            List.flatMap (fun block => inputEventsInBlock block events) blocks := by
        simpa using ih
      by_cases hOccupied : events.any fun event => event.workBlock == block
      · simp [hOccupied, ih']
      · have hEmpty : inputEventsInBlock block events = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro event hEvent
          have hInEvents : event ∈ events :=
            (List.mem_filter.mp hEvent).1
          have hBlock : event.workBlock == block :=
            (List.mem_filter.mp hEvent).2
          have : events.any (fun candidate => candidate.workBlock == block) = true :=
            List.any_eq_true.mpr ⟨event, hInEvents, hBlock⟩
          exact hOccupied this
        simp [hOccupied, hEmpty, ih']

/-- Grouping by every finite block label preserves the event multiset. -/
theorem stableGroupedInputEventsAllBlocks_perm {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    stableGroupedInputEventsAllBlocks events ~ events := by
  rw [List.perm_iff_count]
  intro event
  unfold stableGroupedInputEventsAllBlocks inputEventsInBlock
  simp only [List.count_flatMap]
  rw [← List.sum_toFinset _ (List.nodup_finRange blockCount),
    List.toFinset_finRange]
  rw [Finset.sum_eq_single event.workBlock]
  · exact List.count_filter (by simp)
  · intro block _ hNe
    apply List.count_eq_zero.mpr
    intro hFiltered
    have hEq : event.workBlock = block := by
      simpa using (List.mem_filter.mp hFiltered).2
    exact hNe hEq.symm
  · simp

/-- Stable grouping by occupied blocks is a permutation of the original
event list.  Duplicate event structures, when present, keep their exact
multiplicity. -/
theorem stableGroupedInputEvents_perm {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    stableGroupedInputEvents events ~ events := by
  rw [stableGroupedInputEvents_eq_allBlocks]
  exact stableGroupedInputEventsAllBlocks_perm events

/-- Every projected stable grouping is a permutation of the chronological
projection.  The projection need not be injective. -/
theorem stableGroupedInputOrder_perm {blockCount : Nat} {α : Type}
    (project : InputReadEvent blockCount → α)
    (events : List (InputReadEvent blockCount)) :
    stableGroupedInputOrder project events ~ events.map project := by
  have hEvents := (stableGroupedInputEvents_perm events).map project
  simpa [stableGroupedInputEvents, stableGroupedInputOrder,
    stableInputBlockSegments, List.map_flatten] using hEvents

/-- Stable grouping preserves the length of every projection. -/
theorem stableGroupedInputOrder_length {blockCount : Nat} {α : Type}
    (project : InputReadEvent blockCount → α)
    (events : List (InputReadEvent blockCount)) :
    (stableGroupedInputOrder project events).length = events.length := by
  simpa using (stableGroupedInputOrder_perm project events).length_eq

/-- Stable grouping preserves duplicate-freeness of every projection. -/
theorem stableGroupedInputOrder_nodup_iff {blockCount : Nat} {α : Type}
    (project : InputReadEvent blockCount → α)
    (events : List (InputReadEvent blockCount)) :
    (stableGroupedInputOrder project events).Nodup ↔
      (events.map project).Nodup :=
  (stableGroupedInputOrder_perm project events).nodup_iff

/-- The grouped fresh-coordinate list is a permutation of the original
fresh-coordinate list. -/
theorem stableGroupedFreshInputPositions_perm {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    stableGroupedFreshInputPositions events ~ freshInputPositions events := by
  exact stableGroupedInputOrder_perm InputReadEvent.inputPosition
    (advancingInputEvents events)

/-- Consequently, stable grouping preserves the number of fresh queries. -/
theorem stableGroupedFreshInputPositions_length {blockCount : Nat}
    (events : List (InputReadEvent blockCount)) :
    (stableGroupedFreshInputPositions events).length =
      (freshInputPositions events).length :=
  (stableGroupedFreshInputPositions_perm events).length_eq

/-- A strict chronological fresh order remains globally duplicate-free after
block grouping, even though the grouped list need not remain increasing. -/
theorem stableGroupedFreshInputPositions_nodup_of_strict
    {blockCount : Nat} (events : List (InputReadEvent blockCount))
    (hFresh : (freshInputPositions events).Pairwise (· < ·)) :
    (stableGroupedFreshInputPositions events).Nodup := by
  exact (stableGroupedFreshInputPositions_perm events).symm.nodup
    (freshInputPositions_nodup_of_strict events hFresh)

/-- The complete grouped fresh-query order of an actual run is read-once for
that trace, for any supplied work-block classifier. -/
theorem actualRun_stableGroupedFreshInputPositions_nodup
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    (stableGroupedFreshInputPositions
      (actualRunInputEvents machine input steps workBlockAt)).Nodup :=
  stableGroupedFreshInputPositions_nodup_of_strict _
    (actualRunInputEvents_fresh_positions_pairwise_lt
      machine input steps workBlockAt)

/-- The cached-input normalization is a concrete instance of the same
trace-local read-once theorem.  This statement still does not assert that
different inputs induce the same block classifier or grouped order. -/
theorem cachedRun_stableGroupedFreshInputPositions_nodup
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    (stableGroupedFreshInputPositions
      (actualRunInputEvents (cachedInputMachine machine) input steps
        workBlockAt)).Nodup :=
  actualRun_stableGroupedFreshInputPositions_nodup
    (cachedInputMachine machine) input steps workBlockAt

end OneTapeMagnification
end Frontier
end Pnp4
