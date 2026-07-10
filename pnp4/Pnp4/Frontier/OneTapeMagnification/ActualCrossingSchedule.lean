import Mathlib.Data.List.SplitBy
import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualRunInputOrder
import Pnp4.Frontier.OneTapeMagnification.CanonicalWorkBlocks
import Pnp4.Frontier.OneTapeMagnification.CrossingScheduleInputOrder

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The crossing schedule of an actual run

This file extracts the schedule which was deliberately left abstract in
`CrossingScheduleInputOrder`.  A selected crossing time is an actual
transition `time < steps` at which the canonical work-block label changes.
The list is chronological because it is a filter of `List.finRange steps`.

The transition times are also split into maximal consecutive runs with the
same canonical work-block label.  A run of `m` transitions starting at time
`s` records the actual input-head interval between configurations `s` and
`s + m`.  Building these intervals by cumulative run lengths makes adjacent
input endpoints agree definitionally.  Input-head monotonicity supplies every
per-segment `startPosition <= stopPosition` proof.

The result is a concrete, input-dependent `FixedCrossingSchedule`.  It is not
an input-independent advice string, a local replay theorem, or a branching-
program width bound.
-/

/-- Actual canonical counts, named to keep the specializations below short. -/
def actualWorkBoundaryCounts (machine : DeterministicMachine)
    (input : List Bool) (steps : Nat) : Fin steps -> Nat :=
  fun boundary =>
    workBoundaryCrossingCount machine input steps boundary.val

/-- Specialization of the exact block-change criterion to the canonical
boundaries selected from the actual run's own crossing counts. -/
theorem actualCanonicalWorkBlockAtTime_change_iff_selectedCrossing
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) (time : Nat) :
    actualCanonicalWorkBlockAtTime machine input steps b hb time ≠
        actualCanonicalWorkBlockAtTime machine input steps b hb (time + 1) ↔
      exists boundary : Fin (steps / b),
        WorkBoundaryCrossingAt machine input time
          (canonicalBoundary hb
            (actualWorkBoundaryCounts machine input steps) boundary).val := by
  simpa [actualCanonicalWorkBlockAtTime, actualWorkBoundaryCounts] using
    (canonicalWorkBlockAtTime_change_iff_selectedCrossing
      (crossings := actualWorkBoundaryCounts machine input steps)
      hb machine input time)

/-- The actual selected-boundary crossing times among transitions
`0, ..., steps - 1`, in chronological order. -/
noncomputable def actualSelectedBoundaryCrossingTimes
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) : List (Fin steps) :=
  (List.finRange steps).filter fun time =>
    decide (actualCanonicalWorkBlockAtTime machine input steps b hb time.val ≠
      actualCanonicalWorkBlockAtTime machine input steps b hb (time.val + 1))

@[simp]
theorem mem_actualSelectedBoundaryCrossingTimes_iff
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) (time : Fin steps) :
    time ∈ actualSelectedBoundaryCrossingTimes machine input steps b hb ↔
      exists boundary : Fin (steps / b),
        WorkBoundaryCrossingAt machine input time.val
          (canonicalBoundary hb
            (actualWorkBoundaryCounts machine input steps) boundary).val := by
  rw [actualSelectedBoundaryCrossingTimes, List.mem_filter]
  simp only [List.mem_finRange, true_and, decide_eq_true_eq]
  exact actualCanonicalWorkBlockAtTime_change_iff_selectedCrossing
    machine input steps b hb time.val

/-- No transition time is listed twice. -/
theorem actualSelectedBoundaryCrossingTimes_nodup
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualSelectedBoundaryCrossingTimes machine input steps b hb).Nodup := by
  unfold actualSelectedBoundaryCrossingTimes
  exact (List.nodup_finRange steps).filter _

/-- The extracted crossing times are strictly chronological. -/
theorem actualSelectedBoundaryCrossingTimes_pairwise_lt
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualSelectedBoundaryCrossingTimes machine input steps b hb).Pairwise
      (fun earlier later => earlier < later) := by
  unfold actualSelectedBoundaryCrossingTimes
  exact (List.pairwise_lt_finRange steps).filter _

/-- The number of actual selected-boundary changes is at most `steps / b`.
This is the time-indexed form of the canonical crossing charging bound. -/
theorem length_actualSelectedBoundaryCrossingTimes_le_div
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualSelectedBoundaryCrossingTimes machine input steps b hb).length <=
      steps / b := by
  classical
  let times := actualSelectedBoundaryCrossingTimes machine input steps b hb
  have hNodup : times.Nodup :=
    actualSelectedBoundaryCrossingTimes_nodup machine input steps b hb
  have hPointwise (time : Fin steps) :
      (if time ∈ times then 1 else 0) <=
        ∑ boundary : Fin (steps / b),
          if WorkBoundaryCrossingAt machine input time.val
              (canonicalBoundary hb
                (actualWorkBoundaryCounts machine input steps) boundary).val
            then 1 else 0 := by
    by_cases hTime : time ∈ times
    . obtain ⟨boundary, hCrossing⟩ :=
        (mem_actualSelectedBoundaryCrossingTimes_iff
          machine input steps b hb time).mp hTime
      simp only [hTime, if_pos]
      calc
        1 = if WorkBoundaryCrossingAt machine input time.val
              (canonicalBoundary hb
                (actualWorkBoundaryCounts machine input steps) boundary).val
            then 1 else 0 := by rw [if_pos hCrossing]
        _ <= ∑ candidate : Fin (steps / b),
              if WorkBoundaryCrossingAt machine input time.val
                  (canonicalBoundary hb
                    (actualWorkBoundaryCounts machine input steps) candidate).val
                then 1 else 0 := by
          exact Finset.single_le_sum
            (fun candidate _ => Nat.zero_le
              (if WorkBoundaryCrossingAt machine input time.val
                  (canonicalBoundary hb
                    (actualWorkBoundaryCounts machine input steps) candidate).val
                then 1 else 0))
            (Finset.mem_univ boundary)
    . simp [hTime]
  calc
    times.length = times.toFinset.card := by
      exact (List.toFinset_card_of_nodup hNodup).symm
    _ = ∑ time : Fin steps, if time ∈ times then 1 else 0 := by
      rw [← Finset.sum_filter]
      have hSet :
          Finset.univ.filter (fun time : Fin steps => time ∈ times) =
            times.toFinset := by
        ext time
        simp
      rw [hSet]
      simp
    _ <= ∑ time : Fin steps,
          ∑ boundary : Fin (steps / b),
            if WorkBoundaryCrossingAt machine input time.val
                (canonicalBoundary hb
                  (actualWorkBoundaryCounts machine input steps) boundary).val
              then 1 else 0 := by
      exact Finset.sum_le_sum fun time _ => hPointwise time
    _ = ∑ boundary : Fin (steps / b),
          workBoundaryCrossingCount machine input steps
            (canonicalBoundary hb
              (actualWorkBoundaryCounts machine input steps) boundary).val := by
      simp only [workBoundaryCrossingCount,
        workBoundaryCrossingCountFrom, WorkBoundaryCrossingAt]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro boundary _
      apply Finset.sum_congr rfl
      intro time _
      by_cases hCrossing :
          WorkBoundaryCrossingAtFrom machine input
            (initialConfiguration machine) time.val
            (canonicalBoundary hb
              (actualWorkBoundaryCounts machine input steps) boundary).val
      · simp
      · simp
    _ <= steps / b := by
      simpa [actualWorkBoundaryCounts] using
        (sum_canonicalWorkBoundaryCrossings_le_div
          machine input steps b hb)

/-- Count the failed adjacency tests encountered after a current element.
This is the exact number of new groups created by `List.splitBy`. -/
private def adjacentBreakCount {α : Type*} (relation : α → α → Bool) :
    α → List α → Nat
  | _, [] => 0
  | earlier, later :: rest =>
      (if relation earlier later then 0 else 1) +
        adjacentBreakCount relation later rest

private theorem length_splitByLoop_eq
    {α : Type*} (relation : α → α → Bool) (remaining : List α)
    (current : α) (group : List α) (groups : List (List α)) :
    (List.splitBy.loop relation remaining current group groups).length =
      groups.length + adjacentBreakCount relation current remaining + 1 := by
  induction remaining generalizing current group groups with
  | nil => simp [List.splitBy.loop, adjacentBreakCount]
  | cons later rest ih =>
      simp only [List.splitBy.loop]
      by_cases hRelated : relation current later = true
      · rw [hRelated]
        simp [adjacentBreakCount, hRelated, ih]
      · have hFalse : relation current later = false :=
          Bool.eq_false_of_not_eq_true hRelated
        rw [hFalse]
        simp [adjacentBreakCount, hFalse, ih, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]

private theorem length_splitBy_cons_eq
    {α : Type*} (relation : α → α → Bool) (head : α) (tail : List α) :
    ((head :: tail).splitBy relation).length =
      adjacentBreakCount relation head tail + 1 := by
  simp only [List.splitBy]
  simpa using length_splitByLoop_eq relation tail head [] []

private theorem adjacentBreakCount_le_filter_length
    {α : Type*} (relation : α → α → Bool) (isBreak : α → Bool)
    (head : α) (tail : List α)
    (hChain : (head :: tail).Chain' fun earlier later =>
      relation earlier later = false → isBreak earlier = true) :
    adjacentBreakCount relation head tail ≤
      ((head :: tail).filter isBreak).length := by
  induction tail generalizing head with
  | nil => simp [adjacentBreakCount]
  | cons later rest ih =>
      rw [List.chain'_cons] at hChain
      have hHead := hChain.1
      have hTail := hChain.2
      have hRec := ih later hTail
      by_cases hRelated : relation head later = true
      · simp only [adjacentBreakCount, hRelated, if_pos, zero_add]
        by_cases hBreak : isBreak head = true
        · simp [hBreak]
          omega
        · have hBreakFalse : isBreak head = false :=
            Bool.eq_false_of_not_eq_true hBreak
          simpa [hBreakFalse] using hRec
      · have hFalse : relation head later = false :=
          Bool.eq_false_of_not_eq_true hRelated
        have hBreak : isBreak head = true := hHead hFalse
        simp [adjacentBreakCount, hFalse, hBreak]
        omega

/-- A split has at most one more group than the number of marked failed
adjacency tests. -/
private theorem length_splitBy_le_filter_length_add_one
    {α : Type*} (relation : α → α → Bool) (isBreak : α → Bool)
    (list : List α)
    (hChain : list.Chain' fun earlier later =>
      relation earlier later = false → isBreak earlier = true) :
    (list.splitBy relation).length ≤ (list.filter isBreak).length + 1 := by
  cases list with
  | nil => simp
  | cons head tail =>
      rw [length_splitBy_cons_eq]
      exact Nat.add_le_add_right
        (adjacentBreakCount_le_filter_length
          relation isBreak head tail hChain) 1

/-- Maximal consecutive transition-time runs with one canonical work-block
label.  `List.splitBy` keeps adjacent times together exactly while their
pre-transition labels agree. -/
noncomputable def actualCanonicalWorkBlockRuns
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) : List (List (Fin steps)) :=
  (List.finRange steps).splitBy fun earlier later =>
    decide (actualCanonicalWorkBlockAtTime machine input steps b hb earlier.val =
      actualCanonicalWorkBlockAtTime machine input steps b hb later.val)

/-- There is at most one maximal work-block run beyond the number of actual
selected-boundary changes.  Charging those changes gives the quantitative
`steps / b + 1` schedule bound. -/
theorem length_actualCanonicalWorkBlockRuns_le_div_add_one
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualCanonicalWorkBlockRuns machine input steps b hb).length ≤
      steps / b + 1 := by
  let label := actualCanonicalWorkBlockAtTime machine input steps b hb
  have hConsecutive : (List.finRange steps).Chain'
      (fun earlier later => later.val = earlier.val + 1) := by
    rw [List.chain'_iff_get]
    intro i hi
    simp only [List.length_finRange] at hi
    simp [List.get_eq_getElem]
  have hBreaks : (List.finRange steps).Chain' fun earlier later =>
      decide (label earlier.val = label later.val) = false →
        decide (label earlier.val ≠ label (earlier.val + 1)) = true :=
    hConsecutive.imp fun earlier later hNext hFalse => by
      apply decide_eq_true
      have hNe : label earlier.val ≠ label later.val :=
        decide_eq_false_iff_not.mp hFalse
      simpa [hNext] using hNe
  have hRunsToChanges :
      (actualCanonicalWorkBlockRuns machine input steps b hb).length ≤
        (actualSelectedBoundaryCrossingTimes machine input steps b hb).length + 1 := by
    simpa [actualCanonicalWorkBlockRuns,
      actualSelectedBoundaryCrossingTimes, label] using
      (length_splitBy_le_filter_length_add_one
        (fun earlier later : Fin steps =>
          decide (label earlier.val = label later.val))
        (fun time : Fin steps =>
          decide (label time.val ≠ label (time.val + 1)))
        (List.finRange steps) hBreaks)
  exact hRunsToChanges.trans
    (Nat.add_le_add_right
      (length_actualSelectedBoundaryCrossingTimes_le_div
        machine input steps b hb) 1)

/-- The maximal runs partition all transition times, without reordering or
dropping a time. -/
theorem flatten_actualCanonicalWorkBlockRuns
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualCanonicalWorkBlockRuns machine input steps b hb).flatten =
      List.finRange steps := by
  simp [actualCanonicalWorkBlockRuns]

/-- Every extracted run is nonempty. -/
theorem actualCanonicalWorkBlockRuns_nonempty
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    {group : List (Fin steps)}
    (hGroup : group ∈ actualCanonicalWorkBlockRuns machine input steps b hb) :
    group ≠ [] := by
  unfold actualCanonicalWorkBlockRuns at hGroup
  exact List.ne_nil_of_mem_splitBy _ hGroup

/-- Inside each run, every adjacent pair has the same canonical work-block
label. -/
theorem actualCanonicalWorkBlockRuns_chain_same
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    {group : List (Fin steps)}
    (hGroup : group ∈ actualCanonicalWorkBlockRuns machine input steps b hb) :
    group.Chain' fun earlier later =>
      actualCanonicalWorkBlockAtTime machine input steps b hb earlier.val =
        actualCanonicalWorkBlockAtTime machine input steps b hb later.val := by
  unfold actualCanonicalWorkBlockRuns at hGroup
  simpa using (List.chain'_of_mem_splitBy hGroup)

/-- Hence any two chronologically ordered times in one run have the same
label, not merely adjacent times. -/
theorem actualCanonicalWorkBlockRuns_pairwise_same
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    {group : List (Fin steps)}
    (hGroup : group ∈ actualCanonicalWorkBlockRuns machine input steps b hb) :
    group.Pairwise fun earlier later =>
      actualCanonicalWorkBlockAtTime machine input steps b hb earlier.val =
        actualCanonicalWorkBlockAtTime machine input steps b hb later.val := by
  letI : IsTrans (Fin steps) (fun earlier later =>
      actualCanonicalWorkBlockAtTime machine input steps b hb earlier.val =
        actualCanonicalWorkBlockAtTime machine input steps b hb later.val) :=
    ⟨fun _ _ _ hEarlier hLater => hEarlier.trans hLater⟩
  exact List.chain'_iff_pairwise.mp
    (actualCanonicalWorkBlockRuns_chain_same
      machine input steps b hb hGroup)

/-- Consecutive runs have different labels at their touching ends.  Together
with `actualCanonicalWorkBlockRuns_chain_same`, this is the maximality
certificate for the split. -/
theorem actualCanonicalWorkBlockRuns_adjacent_differ
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualCanonicalWorkBlockRuns machine input steps b hb).Chain'
      fun earlier later =>
        exists (hEarlier : earlier ≠ []) (hLater : later ≠ []),
          actualCanonicalWorkBlockAtTime machine input steps b hb
              (earlier.getLast hEarlier).val ≠
            actualCanonicalWorkBlockAtTime machine input steps b hb
              (later.head hLater).val := by
  unfold actualCanonicalWorkBlockRuns
  simpa using
    (List.chain'_getLast_head_splitBy
      (fun earlier later : Fin steps =>
        decide (actualCanonicalWorkBlockAtTime machine input steps b hb
              earlier.val =
          actualCanonicalWorkBlockAtTime machine input steps b hb later.val))
      (List.finRange steps))

/-- Convert maximal time groups into concrete input intervals.  The recursive
`startTime` is the sum of preceding group lengths. -/
noncomputable def actualCrossingScheduleSegmentsFromGroups
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    List (List (Fin steps)) -> Nat ->
      List (CrossingScheduleSegment (steps / b + 1))
  | [], _ => []
  | group :: groups, startTime =>
      { workBlock :=
          actualCanonicalWorkBlockAtTime machine input steps b hb startTime
        startPosition := (run machine input startTime).inputHead
        stopPosition :=
          (run machine input (startTime + group.length)).inputHead
        start_le_stop :=
          inputHead_run_mono machine input (Nat.le_add_right _ _) } ::
        actualCrossingScheduleSegmentsFromGroups machine input steps b hb
          groups (startTime + group.length)

/-- There is exactly one concrete schedule segment for every maximal time
run. -/
@[simp]
theorem actualCrossingScheduleSegmentsFromGroups_length
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (groups : List (List (Fin steps))) (startTime : Nat) :
    (actualCrossingScheduleSegmentsFromGroups
      machine input steps b hb groups startTime).length = groups.length := by
  induction groups generalizing startTime with
  | nil => rfl
  | cons group groups ih =>
      simp [actualCrossingScheduleSegmentsFromGroups, ih]

/-- Cumulative construction makes all actual input-head endpoints chain. -/
theorem actualCrossingScheduleSegmentsFromGroups_chained
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (groups : List (List (Fin steps))) (startTime : Nat) :
    ChainedCrossingSchedule
      (run machine input startTime).inputHead
      (run machine input
        (startTime + (groups.map List.length).sum)).inputHead
      (actualCrossingScheduleSegmentsFromGroups
        machine input steps b hb groups startTime) := by
  induction groups generalizing startTime with
  | nil =>
      simpa [actualCrossingScheduleSegmentsFromGroups] using
        (ChainedCrossingSchedule.nil
          (blockCount := steps / b + 1)
          (run machine input startTime).inputHead)
  | cons group groups ih =>
      simp only [actualCrossingScheduleSegmentsFromGroups, List.map_cons,
        List.sum_cons]
      let segment : CrossingScheduleSegment (steps / b + 1) :=
        { workBlock :=
            actualCanonicalWorkBlockAtTime machine input steps b hb startTime
          startPosition := (run machine input startTime).inputHead
          stopPosition :=
            (run machine input (startTime + group.length)).inputHead
          start_le_stop :=
            inputHead_run_mono machine input (Nat.le_add_right _ _) }
      change ChainedCrossingSchedule segment.startPosition
        (run machine input
          (startTime + (group.length + (groups.map List.length).sum))).inputHead
        (segment :: actualCrossingScheduleSegmentsFromGroups
          machine input steps b hb groups (startTime + group.length))
      refine ChainedCrossingSchedule.cons segment ?_
      simpa [Nat.add_assoc] using
        (ih (startTime := startTime + group.length))

/-- Concrete segments of the actual run, beginning at transition time zero. -/
noncomputable def actualCrossingScheduleSegments
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    List (CrossingScheduleSegment (steps / b + 1)) :=
  actualCrossingScheduleSegmentsFromGroups machine input steps b hb
    (actualCanonicalWorkBlockRuns machine input steps b hb) 0

@[simp]
theorem actualCrossingScheduleSegments_length
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualCrossingScheduleSegments machine input steps b hb).length =
      (actualCanonicalWorkBlockRuns machine input steps b hb).length := by
  simp [actualCrossingScheduleSegments]

/-- The concrete schedule inherits the same quantitative segment bound as
its maximal work-block run decomposition. -/
theorem length_actualCrossingScheduleSegments_le_div_add_one
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualCrossingScheduleSegments machine input steps b hb).length ≤
      steps / b + 1 := by
  rw [actualCrossingScheduleSegments_length]
  exact length_actualCanonicalWorkBlockRuns_le_div_add_one
    machine input steps b hb

/-- The actual maximal-run decomposition as a `FixedCrossingSchedule`.
Its exposed endpoints are the actual input-head positions at times `0` and
`steps`. -/
noncomputable def actualFixedCrossingSchedule
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    FixedCrossingSchedule (steps / b + 1) where
  startPosition := (run machine input 0).inputHead
  stopPosition := (run machine input steps).inputHead
  segments := actualCrossingScheduleSegments machine input steps b hb
  chained := by
    have hChain := actualCrossingScheduleSegmentsFromGroups_chained
      machine input steps b hb
      (actualCanonicalWorkBlockRuns machine input steps b hb) 0
    have hLength :
        ((actualCanonicalWorkBlockRuns machine input steps b hb).map
          List.length).sum = steps := by
      rw [<- List.length_flatten,
        flatten_actualCanonicalWorkBlockRuns machine input steps b hb]
      simp
    simpa [actualCrossingScheduleSegments, hLength] using hChain

@[simp]
theorem actualFixedCrossingSchedule_startPosition
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualFixedCrossingSchedule machine input steps b hb).startPosition = 0 := by
  rfl

@[simp]
theorem actualFixedCrossingSchedule_stopPosition
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (actualFixedCrossingSchedule machine input steps b hb).stopPosition =
      (run machine input steps).inputHead := by
  rfl

/-- Extending the concrete event trace by one transition appends exactly the
event at the previous final time. -/
theorem actualRunInputEvents_succ_eq_append
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    actualRunInputEvents machine input (steps + 1) workBlockAt =
      actualRunInputEvents machine input steps workBlockAt ++
        [actualRunInputEvent machine input workBlockAt steps] := by
  unfold actualRunInputEvents
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  congr 1

/-- Fresh positions obey the same append recurrence: a right move contributes
the pre-transition input-head coordinate, while a stay contributes nothing. -/
theorem freshInputPositions_actualRunInputEvents_succ
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    freshInputPositions
        (actualRunInputEvents machine input (steps + 1) workBlockAt) =
      freshInputPositions
          (actualRunInputEvents machine input steps workBlockAt) ++
        if inputHeadAdvancesAt machine input steps then
          [(run machine input steps).inputHead]
        else [] := by
  rw [actualRunInputEvents_succ_eq_append]
  by_cases hAdvance :
      (run machine input (steps + 1)).inputHead =
        (run machine input steps).inputHead + 1
  · simp [freshInputPositions, advancingInputEvents,
      actualRunInputEvent, inputHeadAdvancesAt, hAdvance]
  · simp [freshInputPositions, advancingInputEvents,
      actualRunInputEvent, inputHeadAdvancesAt, hAdvance]

/-- Advancing events of a one-way run query exactly the initial interval
`0, ..., finalInputHead - 1`, once each and in chronological order. -/
theorem freshInputPositions_actualRunInputEvents_eq_range
    {blockCount : Nat} (machine : DeterministicMachine) (input : List Bool)
    (steps : Nat) (workBlockAt : Nat → Fin blockCount) :
    freshInputPositions
        (actualRunInputEvents machine input steps workBlockAt) =
      List.range (run machine input steps).inputHead := by
  induction steps with
  | zero =>
      simp [actualRunInputEvents, freshInputPositions,
        advancingInputEvents, run_zero, initialConfiguration]
  | succ steps ih =>
      rw [freshInputPositions_actualRunInputEvents_succ, ih]
      have hStepCases :
          (run machine input (steps + 1)).inputHead =
              (run machine input steps).inputHead ∨
            (run machine input (steps + 1)).inputHead =
              (run machine input steps).inputHead + 1 := by
        simpa only [run, runFrom_succ_eq_step_runFrom] using
          (inputHead_step_cases machine input (run machine input steps))
      rcases hStepCases with hStay | hRight
      · simp [inputHeadAdvancesAt, hStay]
      · simp [inputHeadAdvancesAt, hRight, List.range_succ]

/-- The chronological interval recorded by the actual fixed schedule is
exactly the actual advancing-position list. -/
theorem chronological_actualCrossingScheduleInputOrder_eq_fresh
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    chronologicalCrossingScheduleInputOrder
        (actualCrossingScheduleSegments machine input steps b hb) =
      freshInputPositions
        (actualRunInputEvents machine input steps
          (actualCanonicalWorkBlockAtTime machine input steps b hb)) := by
  change chronologicalCrossingScheduleInputOrder
      (actualFixedCrossingSchedule machine input steps b hb).segments = _
  rw [chronologicalCrossingScheduleInputOrder_eq_range'
      (actualFixedCrossingSchedule machine input steps b hb).chained,
    freshInputPositions_actualRunInputEvents_eq_range]
  exact List.range_eq_range'.symm

/-- Stable replay by work block only permutes the actual fresh queries.  This
is the promised schedule-level read-once order; it remains input-dependent. -/
theorem actualFixedCrossingSchedule_readOnceInputOrder_perm_fresh
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    List.Perm
      (actualFixedCrossingSchedule machine input steps b hb).readOnceInputOrder
      (freshInputPositions
          (actualRunInputEvents machine input steps
            (actualCanonicalWorkBlockAtTime machine input steps b hb))) := by
  change List.Perm
    (stableGroupedCrossingScheduleInputOrder
      (actualCrossingScheduleSegments machine input steps b hb)) _
  exact
    (stableGroupedCrossingScheduleInputOrder_perm
      (actualCrossingScheduleSegments machine input steps b hb)).trans
      (List.Perm.of_eq
        (chronological_actualCrossingScheduleInputOrder_eq_fresh
          machine input steps b hb))

end OneTapeMagnification
end Frontier
end Pnp4
