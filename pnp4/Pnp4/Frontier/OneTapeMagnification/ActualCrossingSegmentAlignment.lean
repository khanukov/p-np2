import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualSegmentSlabReplay
import Pnp4.Frontier.OneTapeMagnification.ChronologicalCanonicalAlpha

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Alignment of actual crossing records and maximal segments

This file relates two extractions from the same concrete run.  Maximal groups
partition the pre-transition times `0, ..., T - 1`; chronological crossing
entries record transitions whose canonical block changes.  A proper group
stop `stop < T` is therefore exactly a crossing post-time `time + 1`.

There is one endpoint convention at `T`: a selected crossing on transition
`T - 1` has a chronological record with post-time `T`, but it creates no new
nonempty transition group.  If the final transition does not cross a selected
boundary, the terminal endpoint has no crossing record.

All results concern one actual, input-dependent run.  Times are retained in
`ChronologicalCanonicalCrossingEntry`; no claim is made that the erased padded
alpha determines this schedule or validates a replay.
-/

/-- Exact interval membership for a maximal actual group. -/
theorem mem_actualCanonicalWorkBlockGroup_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) (time : Fin T) :
    time ∈ group ↔
      timeGroupsLength before ≤ time.val ∧
        time.val < timeGroupsLength before + group.length := by
  have hmap := actualCanonicalWorkBlockGroup_map_val_eq_range'
    machine input T b hb before after group hsplit
  constructor
  · intro htime
    have hval : time.val ∈ group.map Fin.val :=
      List.mem_map_of_mem htime
    rw [hmap] at hval
    simpa using hval
  · intro hbounds
    have hval : time.val ∈
        List.range' (timeGroupsLength before) group.length := by
      simpa using hbounds
    rw [← hmap] at hval
    obtain ⟨candidate, hcandidate, hvalue⟩ := List.mem_map.mp hval
    have : candidate = time := Fin.ext hvalue
    simpa [this] using hcandidate

/-- A cumulative stop which has a following nonempty maximal group. -/
def IsActualProperGroupStop
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (stop : Nat) : Prop :=
  ∃ before group next after,
    actualCanonicalWorkBlockRuns machine input T b hb =
        before ++ group :: next :: after ∧
      stop = timeGroupsLength before + group.length

/-- A selected crossing post-time which is strictly before the terminal
configuration time `T`. -/
def IsActualProperSelectedCrossingPostTime
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (stop : Nat) : Prop :=
  ∃ time : Fin T,
    time ∈ actualSelectedBoundaryCrossingTimes machine input T b hb ∧
      stop = time.val + 1 ∧ stop < T

private theorem timeGroupsLength_actualCanonicalWorkBlockRuns
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    timeGroupsLength
      (actualCanonicalWorkBlockRuns machine input T b hb) = T := by
  unfold timeGroupsLength
  rw [← List.length_flatten,
    flatten_actualCanonicalWorkBlockRuns machine input T b hb]
  simp

/-- Every proper maximal-group stop is a selected crossing post-time. -/
theorem isActualProperGroupStop_imp_selectedCrossingPostTime
    (machine : DeterministicMachine) (input : List Bool)
    (T b stop : Nat) (hb : 0 < b)
    (hstop : IsActualProperGroupStop machine input T b hb stop) :
    IsActualProperSelectedCrossingPostTime machine input T b hb stop := by
  rcases hstop with ⟨before, group, next, after, hsplit, rfl⟩
  let start := timeGroupsLength before
  let stop := start + group.length
  have hgroupNonempty := actualCanonicalWorkBlockGroup_nonempty
    machine input T b hb before (next :: after) group hsplit
  have hnextSplit :
      actualCanonicalWorkBlockRuns machine input T b hb =
        (before ++ [group]) ++ next :: after := by
    simpa [List.append_assoc] using hsplit
  have hnextNonempty := actualCanonicalWorkBlockGroup_nonempty
    machine input T b hb (before ++ [group]) after next hnextSplit
  have hnextEnd := actualCanonicalWorkBlockGroup_end_le_steps
    machine input T b hb (before ++ [group]) after next hnextSplit
  have hstartNext : timeGroupsLength (before ++ [group]) = stop := by
    simp [stop, start]
  rw [hstartNext] at hnextEnd
  have hstopLt : stop < T := by
    have hnextPos : 0 < next.length := List.length_pos_iff.mpr hnextNonempty
    omega
  have hgroupLastLabel := actualCanonicalWorkBlockGroup_label_eq_initial
    machine input T b hb before (next :: after) group hsplit
      (group.getLast hgroupNonempty) (List.getLast_mem hgroupNonempty)
  have hnextHeadLabel := actualCanonicalWorkBlockGroup_label_eq_initial
    machine input T b hb (before ++ [group]) after next hnextSplit
      (next.head hnextNonempty) (List.head_mem hnextNonempty)
  rw [hstartNext] at hnextHeadLabel
  have hchain := actualCanonicalWorkBlockRuns_adjacent_differ
    machine input T b hb
  have hadjacent :=
    (List.chain'_iff_forall_rel_of_append_cons_cons.mp hchain)
      (show actualCanonicalWorkBlockRuns machine input T b hb =
          before ++ group :: next :: after from hsplit)
  rcases hadjacent with ⟨hgroup', hnext', hdifferent⟩
  have hdifferent' :
      actualCanonicalWorkBlockAtTime machine input T b hb
          (group.getLast hgroupNonempty).val ≠
        actualCanonicalWorkBlockAtTime machine input T b hb
          (next.head hnextNonempty).val := by
    simpa using hdifferent
  have hinitialDifferent :
      actualCanonicalWorkBlockAtTime machine input T b hb start ≠
        actualCanonicalWorkBlockAtTime machine input T b hb stop := by
    intro heq
    apply hdifferent'
    rw [hgroupLastLabel, hnextHeadLabel, heq]
  have hgroupPos : 0 < group.length := List.length_pos_iff.mpr hgroupNonempty
  have hlastLabel := actualCanonicalWorkBlockGroup_label_constant
    machine input T b hb before (next :: after) group hsplit
      (group.length - 1) (by omega)
  have hlastTime : start + (group.length - 1) = stop - 1 := by
    dsimp only [start, stop]
    omega
  rw [hlastTime] at hlastLabel
  have hchange :
      actualCanonicalWorkBlockAtTime machine input T b hb (stop - 1) ≠
        actualCanonicalWorkBlockAtTime machine input T b hb stop := by
    intro heq
    exact hinitialDifferent (hlastLabel.symm.trans heq)
  have hstopPos : 0 < stop := by
    dsimp only [stop, start]
    omega
  let crossingTime : Fin T := ⟨stop - 1, by omega⟩
  have hcrossingTime : crossingTime.val + 1 = stop := by
    dsimp only [crossingTime]
    omega
  have hselected : crossingTime ∈
      actualSelectedBoundaryCrossingTimes machine input T b hb := by
    rw [actualSelectedBoundaryCrossingTimes, List.mem_filter]
    simp only [List.mem_finRange, true_and, decide_eq_true_eq]
    simpa [hcrossingTime] using hchange
  exact ⟨crossingTime, hselected, hcrossingTime.symm, hstopLt⟩

/-- Conversely, every selected crossing whose post-time is before `T` is the
stop of a maximal group with a following group. -/
theorem isActualProperSelectedCrossingPostTime_imp_groupStop
    (machine : DeterministicMachine) (input : List Bool)
    (T b stop : Nat) (hb : 0 < b)
    (hstop : IsActualProperSelectedCrossingPostTime
      machine input T b hb stop) :
    IsActualProperGroupStop machine input T b hb stop := by
  rcases hstop with ⟨time, hselected, rfl, hproper⟩
  let groups := actualCanonicalWorkBlockRuns machine input T b hb
  have htimeFlatten : time ∈ groups.flatten := by
    dsimp only [groups]
    rw [flatten_actualCanonicalWorkBlockRuns machine input T b hb]
    simp
  rcases List.mem_flatten.mp htimeFlatten with
    ⟨group, hgroupMem, htimeGroup⟩
  rcases List.mem_iff_append.mp hgroupMem with
    ⟨before, after, hsplit⟩
  have hsplit' : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after := by
    simpa [groups] using hsplit
  have hbounds := (mem_actualCanonicalWorkBlockGroup_iff
    machine input T b hb before after group hsplit' time).mp htimeGroup
  let start := timeGroupsLength before
  let groupStop := start + group.length
  have hpostLeStop : time.val + 1 ≤ groupStop := by
    dsimp only [groupStop, start]
    omega
  have hcrossing :=
    (mem_actualSelectedBoundaryCrossingTimes_iff
      machine input T b hb time).mp hselected
  have hchange :=
    (actualCanonicalWorkBlockAtTime_change_iff_selectedCrossing
      machine input T b hb time.val).mpr hcrossing
  have hpostEqStop : time.val + 1 = groupStop := by
    by_contra hne
    have hpostLtStop : time.val + 1 < groupStop := by omega
    let nextTime : Fin T := ⟨time.val + 1, hproper⟩
    have hnextBounds :
        timeGroupsLength before ≤ nextTime.val ∧
          nextTime.val < timeGroupsLength before + group.length := by
      dsimp only [nextTime, groupStop, start] at hpostLtStop ⊢
      omega
    have hnextGroup := (mem_actualCanonicalWorkBlockGroup_iff
      machine input T b hb before after group hsplit' nextTime).mpr hnextBounds
    have htimeLabel := actualCanonicalWorkBlockGroup_label_eq_initial
      machine input T b hb before after group hsplit' time htimeGroup
    have hnextLabel := actualCanonicalWorkBlockGroup_label_eq_initial
      machine input T b hb before after group hsplit' nextTime hnextGroup
    apply hchange
    exact htimeLabel.trans hnextLabel.symm
  have hafterNonempty : after ≠ [] := by
    intro hnil
    subst after
    have htotal := timeGroupsLength_actualCanonicalWorkBlockRuns
      machine input T b hb
    rw [hsplit', timeGroupsLength_append, timeGroupsLength_cons] at htotal
    simp only [timeGroupsLength_nil, Nat.add_zero] at htotal
    dsimp only [groupStop, start] at hpostEqStop
    omega
  cases after with
  | nil => exact False.elim (hafterNonempty rfl)
  | cons next rest =>
      exact ⟨before, group, next, rest, hsplit', hpostEqStop⟩

/-- Set-level exact correspondence between cumulative proper group stops and
proper chronological selected-crossing post-times. -/
theorem isActualProperGroupStop_iff_selectedCrossingPostTime
    (machine : DeterministicMachine) (input : List Bool)
    (T b stop : Nat) (hb : 0 < b) :
    IsActualProperGroupStop machine input T b hb stop ↔
      IsActualProperSelectedCrossingPostTime machine input T b hb stop := by
  constructor
  · exact isActualProperGroupStop_imp_selectedCrossingPostTime
      machine input T b stop hb
  · exact isActualProperSelectedCrossingPostTime_imp_groupStop
      machine input T b stop hb

/-- The same proper post-time predicate stated using timed chronological
entries rather than the source crossing-time list. -/
def IsChronologicalProperCrossingPostTime
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (stop : Nat) : Prop :=
  ∃ entry : ChronologicalCanonicalCrossingEntry machine.State T b,
    entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb ∧
      stop = entry.time.val + 1 ∧ stop < T

theorem isChronologicalProperCrossingPostTime_iff_selected
    (machine : DeterministicMachine) (input : List Bool)
    (T b stop : Nat) (hb : 0 < b) :
    IsChronologicalProperCrossingPostTime machine input T b hb stop ↔
      IsActualProperSelectedCrossingPostTime machine input T b hb stop := by
  constructor
  · rintro ⟨entry, hentry, rfl, hproper⟩
    refine ⟨entry.time, ?_, rfl, hproper⟩
    have htime : entry.time ∈
        (chronologicalCanonicalCrossingEntries machine input T b hb).map
          ChronologicalCanonicalCrossingEntry.time :=
      List.mem_map_of_mem hentry
    rwa [map_time_chronologicalCanonicalCrossingEntries] at htime
  · rintro ⟨time, htime, rfl, hproper⟩
    have htime' : time ∈
        (chronologicalCanonicalCrossingEntries machine input T b hb).map
          ChronologicalCanonicalCrossingEntry.time := by
      rwa [map_time_chronologicalCanonicalCrossingEntries]
    obtain ⟨entry, hentry, hentryTime⟩ := List.mem_map.mp htime'
    refine ⟨entry, hentry, ?_, ?_⟩
    · simp [hentryTime]
    · simpa [hentryTime] using hproper

/-- Exact set-level alignment phrased directly with chronological entries. -/
theorem isActualProperGroupStop_iff_chronologicalCrossingPostTime
    (machine : DeterministicMachine) (input : List Bool)
    (T b stop : Nat) (hb : 0 < b) :
    IsActualProperGroupStop machine input T b hb stop ↔
      IsChronologicalProperCrossingPostTime machine input T b hb stop := by
  rw [isChronologicalProperCrossingPostTime_iff_selected]
  exact isActualProperGroupStop_iff_selectedCrossingPostTime
    machine input T b stop hb

/-- At time bound zero there are no transition groups. -/
@[simp]
theorem actualCanonicalWorkBlockRuns_zero
    (machine : DeterministicMachine) (input : List Bool)
    (b : Nat) (hb : 0 < b) :
    actualCanonicalWorkBlockRuns machine input 0 b hb = [] := by
  simp [actualCanonicalWorkBlockRuns]

/-- At time bound zero there are no selected crossing times. -/
@[simp]
theorem actualSelectedBoundaryCrossingTimes_zero
    (machine : DeterministicMachine) (input : List Bool)
    (b : Nat) (hb : 0 < b) :
    actualSelectedBoundaryCrossingTimes machine input 0 b hb = [] := by
  simp [actualSelectedBoundaryCrossingTimes]

/-- Consequently the chronological entry list is empty at `T = 0`. -/
@[simp]
theorem chronologicalCanonicalCrossingEntries_zero
    (machine : DeterministicMachine) (input : List Bool)
    (b : Nat) (hb : 0 < b) :
    chronologicalCanonicalCrossingEntries machine input 0 b hb = [] := by
  simp [chronologicalCanonicalCrossingEntries]

/-- The actual fixed schedule also has no segments at `T = 0`. -/
@[simp]
theorem actualCrossingScheduleSegments_zero
    (machine : DeterministicMachine) (input : List Bool)
    (b : Nat) (hb : 0 < b) :
    actualCrossingScheduleSegments machine input 0 b hb = [] := by
  simp [actualCrossingScheduleSegments,
    actualCrossingScheduleSegmentsFromGroups]

/-- The final transition is listed exactly when it changes the canonical
block.  Such a record has terminal post-time `T` but creates no new nonempty
transition group. -/
theorem lastTransition_mem_selectedCrossingTimes_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (hT : 0 < T) :
    (⟨T - 1, by omega⟩ : Fin T) ∈
        actualSelectedBoundaryCrossingTimes machine input T b hb ↔
      actualCanonicalWorkBlockAtTime machine input T b hb (T - 1) ≠
        actualCanonicalWorkBlockAtTime machine input T b hb T := by
  rw [actualSelectedBoundaryCrossingTimes, List.mem_filter]
  simp only [List.mem_finRange, true_and, decide_eq_true_eq]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ T)]

/-- Timed chronological entries retain the same exact last-transition
convention. -/
theorem exists_chronologicalEntry_at_lastTransition_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (hT : 0 < T) :
    (∃ entry : ChronologicalCanonicalCrossingEntry machine.State T b,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb ∧
        entry.time = ⟨T - 1, by omega⟩) ↔
      actualCanonicalWorkBlockAtTime machine input T b hb (T - 1) ≠
        actualCanonicalWorkBlockAtTime machine input T b hb T := by
  rw [← lastTransition_mem_selectedCrossingTimes_iff
    machine input T b hb hT,
    ← map_time_chronologicalCanonicalCrossingEntries]
  simp

/-- Direction extraction is exactly the left-to-right endpoint pattern. -/
theorem workCrossingDirectionOf_eq_leftToRight_iff
    {cut fromHead toHead : Nat}
    (hcross : CrossesWorkBoundary cut fromHead toHead) :
    workCrossingDirectionOf hcross = .leftToRight ↔
      fromHead = cut ∧ toHead = cut + 1 := by
  rcases hcross with hcross | hcross
  · rcases hcross with ⟨rfl, rfl⟩
    simp [workCrossingDirectionOf]
  · rcases hcross with ⟨rfl, rfl⟩
    simp [workCrossingDirectionOf]

/-- Direction extraction is exactly the right-to-left endpoint pattern. -/
theorem workCrossingDirectionOf_eq_rightToLeft_iff
    {cut fromHead toHead : Nat}
    (hcross : CrossesWorkBoundary cut fromHead toHead) :
    workCrossingDirectionOf hcross = .rightToLeft ↔
      fromHead = cut + 1 ∧ toHead = cut := by
  rcases hcross with hcross | hcross
  · rcases hcross with ⟨rfl, rfl⟩
    simp [workCrossingDirectionOf]
  · rcases hcross with ⟨rfl, rfl⟩
    simp [workCrossingDirectionOf]

/-- At a selected canonical cut, left-to-right direction is equivalently the
adjacent left-to-right block-label change. -/
theorem workCrossingDirectionOf_eq_leftToRight_iff_workBlocks
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (boundary : Fin (T / b)) {fromHead toHead : Nat}
    (hcross : CrossesWorkBoundary
      (canonicalBoundary hb crossings boundary).val fromHead toHead) :
    workCrossingDirectionOf hcross = .leftToRight ↔
      workBlockAt hb crossings fromHead = Fin.castSucc boundary ∧
        workBlockAt hb crossings toHead = Fin.succ boundary := by
  rcases hcross with hcross | hcross
  · rcases hcross with ⟨rfl, rfl⟩
    constructor
    · intro _
      exact ⟨workBlockAt_canonicalBoundary hb crossings boundary,
        workBlockAt_canonicalBoundary_succ hb crossings boundary⟩
    · intro _
      simp [workCrossingDirectionOf]
  · rcases hcross with ⟨rfl, rfl⟩
    constructor
    · intro hdirection
      simp [workCrossingDirectionOf] at hdirection
    · intro hblocks
      have hval := congrArg Fin.val hblocks.1
      rw [workBlockAt_canonicalBoundary_succ] at hval
      change boundary.val + 1 = boundary.val at hval
      omega

/-- At a selected canonical cut, right-to-left direction is equivalently the
adjacent right-to-left block-label change. -/
theorem workCrossingDirectionOf_eq_rightToLeft_iff_workBlocks
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (boundary : Fin (T / b)) {fromHead toHead : Nat}
    (hcross : CrossesWorkBoundary
      (canonicalBoundary hb crossings boundary).val fromHead toHead) :
    workCrossingDirectionOf hcross = .rightToLeft ↔
      workBlockAt hb crossings fromHead = Fin.succ boundary ∧
        workBlockAt hb crossings toHead = Fin.castSucc boundary := by
  rcases hcross with hcross | hcross
  · rcases hcross with ⟨rfl, rfl⟩
    constructor
    · intro hdirection
      simp [workCrossingDirectionOf] at hdirection
    · intro hblocks
      have hval := congrArg Fin.val hblocks.1
      rw [workBlockAt_canonicalBoundary] at hval
      change boundary.val = boundary.val + 1 at hval
      omega
  · rcases hcross with ⟨rfl, rfl⟩
    constructor
    · intro _
      exact ⟨workBlockAt_canonicalBoundary_succ hb crossings boundary,
        workBlockAt_canonicalBoundary hb crossings boundary⟩
    · intro _
      simp [workCrossingDirectionOf]

@[simp]
theorem chronologicalCanonicalCrossingRecord_selectedCut
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    (chronologicalCanonicalCrossingRecordOfOccurrence
      machine input T b hb occurrence).selectedCut =
        chronologicalSelectedBoundaryOfOccurrence
          machine input T b hb occurrence := by
  rfl

@[simp]
theorem chronologicalCanonicalCrossingRecord_physicalCut
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    (chronologicalCanonicalCrossingRecordOfOccurrence
      machine input T b hb occurrence).physicalCut =
        canonicalBoundary hb (actualWorkBoundaryCounts machine input T)
          (chronologicalSelectedBoundaryOfOccurrence
            machine input T b hb occurrence) := by
  rfl

@[simp]
theorem chronologicalCanonicalCrossingRecord_postState
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    (chronologicalCanonicalCrossingRecordOfOccurrence
      machine input T b hb occurrence).payload.postState =
        (run machine input (occurrence.val.val + 1)).state := by
  rfl

@[simp]
theorem chronologicalCanonicalCrossingRecord_postInputHead
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    (chronologicalCanonicalCrossingRecordOfOccurrence
      machine input T b hb occurrence).payload.postInputHead.val =
        (run machine input (occurrence.val.val + 1)).inputHead := by
  rfl

@[simp]
theorem chronologicalCanonicalCrossingRecord_direction
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    (chronologicalCanonicalCrossingRecordOfOccurrence
      machine input T b hb occurrence).payload.direction =
        workCrossingDirectionOf
          (chronologicalSelectedBoundaryOfOccurrence_crossing
            machine input T b hb occurrence) := by
  rfl

/-- Every timed chronological entry exposes the exact crossing endpoint and
post-transition payload of its source transition. -/
theorem mem_chronologicalCanonicalCrossingEntries_endpoint_data
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    entry.record.physicalCut =
        canonicalBoundary hb (actualWorkBoundaryCounts machine input T)
          entry.record.selectedCut ∧
      WorkBoundaryCrossingAt machine input entry.time.val
        entry.record.physicalCut.val ∧
      entry.record.payload.postState =
        (run machine input (entry.time.val + 1)).state ∧
      entry.record.payload.postInputHead.val =
        (run machine input (entry.time.val + 1)).inputHead ∧
      (entry.record.payload.direction = .leftToRight ↔
        (run machine input entry.time.val).workHead =
            entry.record.physicalCut.val ∧
          (run machine input (entry.time.val + 1)).workHead =
            entry.record.physicalCut.val + 1) ∧
      (entry.record.payload.direction = .rightToLeft ↔
        (run machine input entry.time.val).workHead =
            entry.record.physicalCut.val + 1 ∧
          (run machine input (entry.time.val + 1)).workHead =
            entry.record.physicalCut.val) := by
  rw [chronologicalCanonicalCrossingEntries] at hentry
  obtain ⟨occurrence, -, rfl⟩ := List.mem_map.mp hentry
  let hcross := chronologicalSelectedBoundaryOfOccurrence_crossing
    machine input T b hb occurrence
  constructor
  · rfl
  constructor
  · exact hcross
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · change workCrossingDirectionOf hcross = .leftToRight ↔ _
    exact workCrossingDirectionOf_eq_leftToRight_iff hcross
  · change workCrossingDirectionOf hcross = .rightToLeft ↔ _
    exact workCrossingDirectionOf_eq_rightToLeft_iff hcross

/-- The concrete schedule segment associated with one group after a given
prefix. -/
noncomputable def actualCrossingScheduleSegmentForGroup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) (group : List (Fin T)) :
    CrossingScheduleSegment (T / b + 1) where
  workBlock := actualCanonicalWorkBlockAtTime machine input T b hb
    (timeGroupsLength before)
  startPosition :=
    (run machine input (timeGroupsLength before)).inputHead
  stopPosition :=
    (run machine input
      (timeGroupsLength before + group.length)).inputHead
  start_le_stop := inputHead_run_mono machine input (Nat.le_add_right _ _)

@[simp]
theorem actualCrossingScheduleSegmentForGroup_workBlock
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) (group : List (Fin T)) :
    (actualCrossingScheduleSegmentForGroup
      machine input T b hb before group).workBlock =
        actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength before) := by
  rfl

@[simp]
theorem actualCrossingScheduleSegmentForGroup_startPosition
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) (group : List (Fin T)) :
    (actualCrossingScheduleSegmentForGroup
      machine input T b hb before group).startPosition =
        (run machine input (timeGroupsLength before)).inputHead := by
  rfl

@[simp]
theorem actualCrossingScheduleSegmentForGroup_stopPosition
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) (group : List (Fin T)) :
    (actualCrossingScheduleSegmentForGroup
      machine input T b hb before group).stopPosition =
        (run machine input
          (timeGroupsLength before + group.length)).inputHead := by
  rfl

/-- The cumulative segment builder distributes over a group-list append. -/
theorem actualCrossingScheduleSegmentsFromGroups_append
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (left right : List (List (Fin T))) (startTime : Nat) :
    actualCrossingScheduleSegmentsFromGroups machine input T b hb
        (left ++ right) startTime =
      actualCrossingScheduleSegmentsFromGroups machine input T b hb
          left startTime ++
        actualCrossingScheduleSegmentsFromGroups machine input T b hb
          right (startTime + timeGroupsLength left) := by
  induction left generalizing startTime with
  | nil => simp [actualCrossingScheduleSegmentsFromGroups]
  | cons group groups ih =>
      simp [actualCrossingScheduleSegmentsFromGroups, ih,
        Nat.add_assoc]

/-- A prefix decomposition of the actual groups induces the matching prefix
decomposition of the actual schedule segments. -/
theorem actualCrossingScheduleSegments_eq_append_group
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    actualCrossingScheduleSegments machine input T b hb =
      actualCrossingScheduleSegmentsFromGroups machine input T b hb before 0 ++
        actualCrossingScheduleSegmentForGroup
          machine input T b hb before group ::
        actualCrossingScheduleSegmentsFromGroups machine input T b hb after
          (timeGroupsLength before + group.length) := by
  unfold actualCrossingScheduleSegments
  rw [hsplit, actualCrossingScheduleSegmentsFromGroups_append]
  simp [actualCrossingScheduleSegmentsFromGroups,
    actualCrossingScheduleSegmentForGroup]

/-- Consecutive group segments share the actual input-head endpoint. -/
theorem actualCrossingScheduleSegmentForGroup_stop_eq_next_start
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) (group next : List (Fin T)) :
    (actualCrossingScheduleSegmentForGroup
      machine input T b hb before group).stopPosition =
      (actualCrossingScheduleSegmentForGroup
        machine input T b hb (before ++ [group]) next).startPosition := by
  simp [actualCrossingScheduleSegmentForGroup]

/-- For a timed entry aligned with a proper group stop, the record's
post-input-head is exactly the exiting segment's recorded stop endpoint. -/
theorem chronologicalEntry_postInputHead_eq_groupSegmentStop
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) (group : List (Fin T))
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (hstop : entry.time.val + 1 =
      timeGroupsLength before + group.length) :
    entry.record.payload.postInputHead.val =
      (actualCrossingScheduleSegmentForGroup
        machine input T b hb before group).stopPosition := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  rw [hdata.2.2.2.1, actualCrossingScheduleSegmentForGroup_stopPosition,
    hstop]

/-- The same aligned entry stores the actual state at the segment exit. -/
theorem chronologicalEntry_postState_eq_groupExit
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T))) (group : List (Fin T))
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (hstop : entry.time.val + 1 =
      timeGroupsLength before + group.length) :
    entry.record.payload.postState =
      (run machine input
        (timeGroupsLength before + group.length)).state := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  rw [hdata.2.2.1, hstop]

/-- The fixed schedule exposes the known initial input endpoint and the
actual terminal input endpoint, independently of whether the last transition
has a crossing record. -/
theorem actualFixedCrossingSchedule_initial_terminal_endpoints
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualFixedCrossingSchedule machine input T b hb).startPosition = 0 ∧
      (actualFixedCrossingSchedule machine input T b hb).stopPosition =
        (run machine input T).inputHead := by
  exact ⟨actualFixedCrossingSchedule_startPosition
      machine input T b hb,
    actualFixedCrossingSchedule_stopPosition machine input T b hb⟩

/-- If a chronological entry is on the last transition, its post-input-head
is exactly the terminal fixed-schedule endpoint. -/
theorem lastChronologicalEntry_postInputHead_eq_scheduleStop
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (hT : 0 < T)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (htime : entry.time.val = T - 1) :
    entry.record.payload.postInputHead.val =
      (actualFixedCrossingSchedule machine input T b hb).stopPosition := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  rw [hdata.2.2.2.1,
    actualFixedCrossingSchedule_stopPosition, htime]
  congr 2
  omega

/-- The post-state of a last-transition entry is the terminal machine state. -/
theorem lastChronologicalEntry_postState_eq_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (hT : 0 < T)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (htime : entry.time.val = T - 1) :
    entry.record.payload.postState = (run machine input T).state := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  rw [hdata.2.2.1, htime]
  congr 2
  omega

end OneTapeMagnification
end Frontier
end Pnp4
