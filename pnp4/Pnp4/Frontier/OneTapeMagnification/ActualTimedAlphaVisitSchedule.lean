import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualAdvertisedCrossingEndpoints
import Pnp4.Frontier.OneTapeMagnification.ActualGroupFixedAlphaVisit
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaVisitSchedule

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Actual timed-alpha visit schedules

This file relates the strictly chronological crossing-token word extracted
from one concrete run to the cumulative stop times of its actual maximal
work-block groups.  The first layer is deliberately list-theoretic: two
strictly increasing lists with the same members are equal, so the existing
set-level group-stop/crossing theorem upgrades to ordered equality.

The later layer turns that equality into the exact token fold used
by `TimedAlphaVisitScheduleValid`.  No correspondence premise is inserted into
the advertised predicate, and no terminal visit of length zero is created.
-/

/-- Strict order plus set-level equality determines a finite list exactly. -/
theorem list_eq_of_pairwise_lt_of_mem_iff
    {α : Type*} [LinearOrder α]
    (left right : List α)
    (hleft : left.Pairwise (· < ·))
    (hright : right.Pairwise (· < ·))
    (hmem : ∀ item, item ∈ left ↔ item ∈ right) :
    left = right := by
  apply List.eq_of_perm_of_sorted (r := (· < ·))
  · exact (List.perm_ext_iff_of_nodup hleft.nodup hright.nodup).2 hmem
  · exact hleft
  · exact hright

/-- Fieldwise extensionality helpers for the two advertised cursor records. -/
theorem fixedAlphaVisitEndpoint_ext
    {State : Type} {T : Nat}
    {left right : FixedAlphaVisitEndpoint State T}
    (hstate : left.state = right.state)
    (hinput : left.inputHead = right.inputHead)
    (hwork : left.workHead = right.workHead) :
    left = right := by
  cases left
  cases right
  simp_all

theorem timedAlphaVisitCursor_ext
    {State : Type} {T b : Nat}
    {left right : TimedAlphaVisitCursor State T b}
    (htime : left.time = right.time)
    (hendpoint : left.endpoint = right.endpoint)
    (hblock : left.block = right.block) :
    left = right := by
  cases left
  cases right
  simp_all

theorem fixedAlphaBlockVisit_ext
    {State : Type} {T : Nat}
    {left right : FixedAlphaBlockVisit State T}
    (hentryTime : left.entryTime = right.entryTime)
    (hexitTime : left.exitTime = right.exitTime)
    (hentry : left.entry = right.entry)
    (hexit : left.exit = right.exit) :
    left = right := by
  cases left
  cases right
  simp_all

theorem timedAlphaScheduledVisit_ext
    {State : Type} {T b : Nat}
    {left right : TimedAlphaScheduledVisit State T b}
    (hblock : left.block = right.block)
    (hvisit : left.visit = right.visit) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Proper cumulative stops, enumerated in the unique increasing order below
`T`.  The predicate itself is the concrete maximal-group decomposition from
`ActualCrossingSegmentAlignment`. -/
noncomputable def actualProperGroupStopTimes
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : List Nat := by
  classical
  exact (List.range T).filter fun stop =>
    decide (IsActualProperGroupStop machine input T b hb stop)

/-- Proper selected-crossing post-times in their unique increasing order. -/
noncomputable def actualProperSelectedCrossingPostTimes
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : List Nat := by
  classical
  exact (List.range T).filter fun stop =>
    decide (IsActualProperSelectedCrossingPostTime
      machine input T b hb stop)

@[simp]
theorem mem_actualProperGroupStopTimes_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (stop : Nat) :
    stop ∈ actualProperGroupStopTimes machine input T b hb ↔
      IsActualProperGroupStop machine input T b hb stop := by
  rw [actualProperGroupStopTimes, List.mem_filter]
  simp only [List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hstop
    have hcrossing :=
      isActualProperGroupStop_imp_selectedCrossingPostTime
        machine input T b stop hb hstop
    rcases hcrossing with ⟨time, htime, heq, hproper⟩
    exact ⟨hproper, hstop⟩

@[simp]
theorem mem_actualProperSelectedCrossingPostTimes_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (stop : Nat) :
    stop ∈ actualProperSelectedCrossingPostTimes machine input T b hb ↔
      IsActualProperSelectedCrossingPostTime machine input T b hb stop := by
  rw [actualProperSelectedCrossingPostTimes, List.mem_filter]
  simp only [List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hstop
    rcases hstop with ⟨time, htime, heq, hproper⟩
    exact ⟨hproper, ⟨time, htime, heq, hproper⟩⟩

/-- Both concrete stop enumerations are strictly chronological. -/
theorem actualProperGroupStopTimes_pairwise_lt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperGroupStopTimes machine input T b hb).Pairwise (· < ·) := by
  unfold actualProperGroupStopTimes
  exact List.pairwise_lt_range.filter _

theorem actualProperSelectedCrossingPostTimes_pairwise_lt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperSelectedCrossingPostTimes machine input T b hb).Pairwise
      (· < ·) := by
  unfold actualProperSelectedCrossingPostTimes
  exact List.pairwise_lt_range.filter _

theorem actualProperGroupStopTimes_nodup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperGroupStopTimes machine input T b hb).Nodup :=
  (actualProperGroupStopTimes_pairwise_lt machine input T b hb).nodup

theorem actualProperSelectedCrossingPostTimes_nodup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperSelectedCrossingPostTimes machine input T b hb).Nodup :=
  (actualProperSelectedCrossingPostTimes_pairwise_lt
    machine input T b hb).nodup

/-- The existing set-level alignment upgrades to exact ordered-list equality;
there is no hidden permutation between group stops and crossing post-times. -/
theorem actualProperGroupStopTimes_eq_selectedCrossingPostTimes
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    actualProperGroupStopTimes machine input T b hb =
      actualProperSelectedCrossingPostTimes machine input T b hb := by
  apply list_eq_of_pairwise_lt_of_mem_iff
  · exact actualProperGroupStopTimes_pairwise_lt machine input T b hb
  · exact actualProperSelectedCrossingPostTimes_pairwise_lt
      machine input T b hb
  · intro stop
    rw [mem_actualProperGroupStopTimes_iff,
      mem_actualProperSelectedCrossingPostTimes_iff]
    exact isActualProperGroupStop_iff_selectedCrossingPostTime
      machine input T b stop hb

/-- The concrete chronological source-time list with the optional terminal
crossing removed, then shifted to post-times. -/
noncomputable def actualProperCrossingPostTimesFromSources
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : List Nat :=
  ((actualSelectedBoundaryCrossingTimes machine input T b hb).filter
      fun time => decide (time.val + 1 < T)).map
    fun time => time.val + 1

theorem actualProperCrossingPostTimesFromSources_pairwise_lt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperCrossingPostTimesFromSources machine input T b hb).Pairwise
      (· < ·) := by
  unfold actualProperCrossingPostTimesFromSources
  rw [List.pairwise_map]
  have htimes := actualSelectedBoundaryCrossingTimes_pairwise_lt
    machine input T b hb
  exact (htimes.filter _).imp fun hlt => by omega

@[simp]
theorem mem_actualProperCrossingPostTimesFromSources_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (stop : Nat) :
    stop ∈ actualProperCrossingPostTimesFromSources machine input T b hb ↔
      IsActualProperSelectedCrossingPostTime
        machine input T b hb stop := by
  constructor
  · intro hstop
    obtain ⟨time, htime, rfl⟩ := List.mem_map.mp hstop
    have hfiltered := List.mem_filter.mp htime
    exact ⟨time, hfiltered.1, rfl,
      of_decide_eq_true hfiltered.2⟩
  · rintro ⟨time, htime, rfl, hproper⟩
    apply List.mem_map_of_mem
    exact List.mem_filter.mpr ⟨htime, decide_eq_true hproper⟩

/-- Thus the abstractly characterized ordered post-time list is literally the
chronological list obtained from the run's selected crossing sources. -/
theorem actualProperSelectedCrossingPostTimes_eq_fromSources
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    actualProperSelectedCrossingPostTimes machine input T b hb =
      actualProperCrossingPostTimesFromSources machine input T b hb := by
  apply list_eq_of_pairwise_lt_of_mem_iff
  · exact actualProperSelectedCrossingPostTimes_pairwise_lt
      machine input T b hb
  · exact actualProperCrossingPostTimesFromSources_pairwise_lt
      machine input T b hb
  · intro stop
    rw [mem_actualProperSelectedCrossingPostTimes_iff,
      mem_actualProperCrossingPostTimesFromSources_iff]

/-- Ordered proper group stops are exactly the shifted chronological selected
source times, not merely a permutation of them. -/
theorem actualProperGroupStopTimes_eq_fromSources
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    actualProperGroupStopTimes machine input T b hb =
      actualProperCrossingPostTimesFromSources machine input T b hb :=
  (actualProperGroupStopTimes_eq_selectedCrossingPostTimes
    machine input T b hb).trans
      (actualProperSelectedCrossingPostTimes_eq_fromSources
        machine input T b hb)

/-- The proper prefix of the actual timed token list.  At most one token is
removed: a crossing on transition `T - 1`, whose post-time is exactly `T`. -/
noncomputable def actualProperTimedCrossingTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (TimedCanonicalCrossingToken machine.State T b) :=
  (chronologicalTimedCanonicalCrossingTokens machine input T b hb).filter
    fun token => decide (token.sourceTime.val + 1 < T)

/-- Post-times carried by the proper timed-token prefix. -/
noncomputable def actualProperTimedCrossingTokenPostTimes
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : List Nat :=
  (actualProperTimedCrossingTokens machine input T b hb).map
    fun token => token.sourceTime.val + 1

theorem actualProperTimedCrossingTokenPostTimes_pairwise_lt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperTimedCrossingTokenPostTimes machine input T b hb).Pairwise
      (· < ·) := by
  have htokens :
      (chronologicalTimedCanonicalCrossingTokens
        machine input T b hb).Pairwise
        (fun earlier later => earlier.sourceTime < later.sourceTime) := by
    simpa only [List.pairwise_map] using
      (chronologicalTimedCanonicalCrossingTokens_times_pairwise_lt
        machine input T b hb)
  unfold actualProperTimedCrossingTokenPostTimes
    actualProperTimedCrossingTokens
  rw [List.pairwise_map]
  exact (htokens.filter _).imp fun hlt => by omega

@[simp]
theorem mem_actualProperTimedCrossingTokenPostTimes_iff
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (stop : Nat) :
    stop ∈ actualProperTimedCrossingTokenPostTimes machine input T b hb ↔
      IsActualProperSelectedCrossingPostTime
        machine input T b hb stop := by
  constructor
  · intro hstop
    obtain ⟨token, htoken, rfl⟩ := List.mem_map.mp hstop
    have hfiltered := List.mem_filter.mp htoken
    have hsource : token.sourceTime ∈
        actualSelectedBoundaryCrossingTimes machine input T b hb := by
      rw [← map_sourceTime_chronologicalTimedCanonicalCrossingTokens]
      exact List.mem_map_of_mem hfiltered.1
    exact ⟨token.sourceTime, hsource, rfl,
      of_decide_eq_true hfiltered.2⟩
  · rintro ⟨time, htime, rfl, hproper⟩
    have htime' : time ∈
        (chronologicalTimedCanonicalCrossingTokens
          machine input T b hb).map
            TimedCanonicalCrossingToken.sourceTime := by
      rwa [map_sourceTime_chronologicalTimedCanonicalCrossingTokens]
    obtain ⟨token, htoken, hsource⟩ := List.mem_map.mp htime'
    have hsourceVal : token.sourceTime.val = time.val := by
      exact congrArg Fin.val hsource
    apply List.mem_map.mpr
    refine ⟨token, List.mem_filter.mpr ⟨htoken, ?_⟩, ?_⟩
    · exact decide_eq_true (by simpa [hsourceVal] using hproper)
    · simp [hsourceVal]

/-- The group-stop order therefore agrees exactly with the actual timed-token
order after deleting the optional terminal token. -/
theorem actualProperGroupStopTimes_eq_timedTokenPostTimes
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    actualProperGroupStopTimes machine input T b hb =
      actualProperTimedCrossingTokenPostTimes machine input T b hb := by
  apply list_eq_of_pairwise_lt_of_mem_iff
  · exact actualProperGroupStopTimes_pairwise_lt machine input T b hb
  · exact actualProperTimedCrossingTokenPostTimes_pairwise_lt
      machine input T b hb
  · intro stop
    rw [mem_actualProperGroupStopTimes_iff,
      mem_actualProperTimedCrossingTokenPostTimes_iff]
    exact isActualProperGroupStop_iff_selectedCrossingPostTime
      machine input T b stop hb

/-- Cumulative stops of every group except the last, starting from an arbitrary
elapsed time.  This executable list is the form used by the group/token fold. -/
def properGroupStopTimesFrom {T : Nat} :
    Nat → List (List (Fin T)) → List Nat
  | _, [] => []
  | _, [_] => []
  | start, group :: next :: rest =>
      (start + group.length) ::
        properGroupStopTimesFrom (start + group.length) (next :: rest)

/-- Exact decomposition characterization of the recursive cumulative stops. -/
theorem mem_properGroupStopTimesFrom_iff
    {T : Nat} (start stop : Nat) (groups : List (List (Fin T))) :
    stop ∈ properGroupStopTimesFrom start groups ↔
      ∃ before group next after,
        groups = before ++ group :: next :: after ∧
          stop = start + timeGroupsLength before + group.length := by
  induction groups generalizing start with
  | nil => simp [properGroupStopTimesFrom]
  | cons first tail ih =>
      cases tail with
      | nil =>
          constructor
          · intro hstop
            simp [properGroupStopTimesFrom] at hstop
          · rintro ⟨before, group, next, after, hsplit, _⟩
            have hlength := congrArg List.length hsplit
            simp at hlength
            omega
      | cons second rest =>
          simp only [properGroupStopTimesFrom, List.mem_cons]
          constructor
          · intro hstop
            rcases hstop with hhead | htail
            · refine ⟨[], first, second, rest, rfl, ?_⟩
              simpa [timeGroupsLength] using hhead
            · obtain ⟨before, group, next, after, hsplit, htime⟩ :=
                (ih (start + first.length)).mp htail
              refine ⟨first :: before, group, next, after, ?_, ?_⟩
              · simp [hsplit]
              · simp only [timeGroupsLength_cons]
                omega
          · rintro ⟨before, group, next, after, hsplit, htime⟩
            cases before with
            | nil =>
                simp only [List.nil_append] at hsplit
                injection hsplit with hfirst htail
                injection htail with hsecond hrest
                subst group
                subst next
                subst after
                left
                simp only [timeGroupsLength_nil, Nat.add_zero] at htime
                omega
            | cons beforeHead beforeTail =>
                simp only [List.cons_append] at hsplit
                injection hsplit with hhead htail
                subst beforeHead
                right
                apply (ih (start + first.length)).mpr
                refine ⟨beforeTail, group, next, after, htail, ?_⟩
                simp only [timeGroupsLength_cons] at htime
                omega

/-- Every recursive stop is strictly after its supplied start when all listed
groups are nonempty. -/
theorem start_lt_of_mem_properGroupStopTimesFrom
    {T : Nat} (start stop : Nat) (groups : List (List (Fin T)))
    (hnonempty : ∀ group, group ∈ groups → group ≠ [])
    (hstop : stop ∈ properGroupStopTimesFrom start groups) :
    start < stop := by
  obtain ⟨before, group, next, after, hsplit, htime⟩ :=
    (mem_properGroupStopTimesFrom_iff start stop groups).mp hstop
  have hgroupMem : group ∈ groups := by
    rw [hsplit]
    simp
  have hpositive : 0 < group.length :=
    List.length_pos_iff.mpr (hnonempty group hgroupMem)
  omega

/-- Recursive cumulative stops are strictly increasing when all groups are
nonempty. -/
theorem properGroupStopTimesFrom_pairwise_lt
    {T : Nat} (start : Nat) (groups : List (List (Fin T)))
    (hnonempty : ∀ group, group ∈ groups → group ≠ []) :
    (properGroupStopTimesFrom start groups).Pairwise (· < ·) := by
  induction groups generalizing start with
  | nil => simp [properGroupStopTimesFrom]
  | cons first tail ih =>
      cases tail with
      | nil => simp [properGroupStopTimesFrom]
      | cons second rest =>
          rw [properGroupStopTimesFrom, List.pairwise_cons]
          constructor
          · intro stop hstop
            exact start_lt_of_mem_properGroupStopTimesFrom
              (start + first.length) stop (second :: rest)
              (fun group hgroup => hnonempty group (by simp [hgroup])) hstop
          · exact ih (start + first.length)
              (fun group hgroup => hnonempty group (by simp [hgroup]))

/-- Every group in the concrete maximal decomposition is nonempty. -/
theorem actualCanonicalWorkBlockRuns_all_nonempty
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    ∀ group,
      group ∈ actualCanonicalWorkBlockRuns machine input T b hb →
        group ≠ [] := by
  intro group hgroup
  exact actualCanonicalWorkBlockRuns_nonempty
    machine input T b hb hgroup

/-- The executable cumulative-stop list is exactly the earlier canonical
increasing enumeration of actual proper group stops. -/
theorem properGroupStopTimesFrom_actualRuns_eq
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    properGroupStopTimesFrom 0
        (actualCanonicalWorkBlockRuns machine input T b hb) =
      actualProperGroupStopTimes machine input T b hb := by
  apply list_eq_of_pairwise_lt_of_mem_iff
  · exact properGroupStopTimesFrom_pairwise_lt 0 _
      (actualCanonicalWorkBlockRuns_all_nonempty machine input T b hb)
  · exact actualProperGroupStopTimes_pairwise_lt machine input T b hb
  · intro stop
    rw [mem_properGroupStopTimesFrom_iff,
      mem_actualProperGroupStopTimes_iff]
    simp only [IsActualProperGroupStop, Nat.zero_add]

/-- Proper chronological entries themselves, retaining the full record needed
for the per-crossing endpoint and block bridges. -/
noncomputable def actualProperChronologicalCrossingEntries
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (ChronologicalCanonicalCrossingEntry machine.State T b) :=
  (chronologicalCanonicalCrossingEntries machine input T b hb).filter
    fun entry => decide (entry.time.val + 1 < T)

/-- Filtering actual entries and then erasing to tokens is exactly the proper
token prefix defined above. -/
theorem map_actualProperEntries_eq_actualProperTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperChronologicalCrossingEntries machine input T b hb).map
        timedCanonicalCrossingTokenOfEntry =
      actualProperTimedCrossingTokens machine input T b hb := by
  simp only [actualProperChronologicalCrossingEntries,
    actualProperTimedCrossingTokens,
    chronologicalTimedCanonicalCrossingTokens]
  induction chronologicalCanonicalCrossingEntries
      machine input T b hb with
  | nil => rfl
  | cons entry entries ih =>
      by_cases hproper : entry.time.val + 1 < T
      · simp [hproper, timedCanonicalCrossingTokenOfEntry, ih]
      · simp [hproper, timedCanonicalCrossingTokenOfEntry, ih]

/-- Mapping proper entries to post-times agrees with the proper timed-token
post-time list. -/
theorem map_postTime_actualProperEntries
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (actualProperChronologicalCrossingEntries machine input T b hb).map
        (fun entry => entry.time.val + 1) =
      actualProperTimedCrossingTokenPostTimes machine input T b hb := by
  unfold actualProperTimedCrossingTokenPostTimes
  rw [← map_actualProperEntries_eq_actualProperTokens]
  simp [List.map_map, timedCanonicalCrossingTokenOfEntry]

/-- Executable group stops and retained proper entries are aligned position by
position through their exact post-times. -/
theorem properGroupStops_eq_map_actualProperEntryPostTimes
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    properGroupStopTimesFrom 0
        (actualCanonicalWorkBlockRuns machine input T b hb) =
      (actualProperChronologicalCrossingEntries machine input T b hb).map
        (fun entry => entry.time.val + 1) := by
  rw [properGroupStopTimesFrom_actualRuns_eq,
    actualProperGroupStopTimes_eq_timedTokenPostTimes,
    map_postTime_actualProperEntries]

/-- For an actual chronological entry, the advertised source label is exactly
the run's canonical block before the crossing transition. -/
theorem actualTimedEntry_advertisedSourceBlock
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    advertisedTimedCrossingSourceBlock
        (timedCanonicalCrossingTokenOfEntry entry) =
      actualCanonicalWorkBlockAtTime machine input T b hb entry.time.val := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  have hcut := hdata.1
  cases hdirection : entry.record.payload.direction
  · have hheads := hdata.2.2.2.2.1.mp hdirection
    simp only [advertisedTimedCrossingSourceBlock,
      timedCanonicalCrossingTokenOfEntry, canonicalCrossingTokenOfRecord,
      hdirection]
    change Fin.castSucc entry.record.selectedCut =
      workBlockAt hb (actualWorkBoundaryCounts machine input T)
        (run machine input entry.time.val).workHead
    rw [hheads.1, hcut]
    exact (workBlockAt_canonicalBoundary hb
      (actualWorkBoundaryCounts machine input T)
      entry.record.selectedCut).symm
  · have hheads := hdata.2.2.2.2.2.mp hdirection
    simp only [advertisedTimedCrossingSourceBlock,
      timedCanonicalCrossingTokenOfEntry, canonicalCrossingTokenOfRecord,
      hdirection]
    change Fin.succ entry.record.selectedCut =
      workBlockAt hb (actualWorkBoundaryCounts machine input T)
        (run machine input entry.time.val).workHead
    rw [hheads.1, hcut]
    exact (workBlockAt_canonicalBoundary_succ hb
      (actualWorkBoundaryCounts machine input T)
      entry.record.selectedCut).symm

/-- Dually, the advertised destination label is the actual block after the
crossing transition. -/
theorem actualTimedEntry_advertisedDestinationBlock
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    advertisedTimedCrossingDestinationBlock
        (timedCanonicalCrossingTokenOfEntry entry) =
      actualCanonicalWorkBlockAtTime machine input T b hb
        (entry.time.val + 1) := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  have hcut := hdata.1
  cases hdirection : entry.record.payload.direction
  · have hheads := hdata.2.2.2.2.1.mp hdirection
    simp only [advertisedTimedCrossingDestinationBlock,
      timedCanonicalCrossingTokenOfEntry, canonicalCrossingTokenOfRecord,
      hdirection]
    change Fin.succ entry.record.selectedCut =
      workBlockAt hb (actualWorkBoundaryCounts machine input T)
        (run machine input (entry.time.val + 1)).workHead
    rw [hheads.2, hcut]
    exact (workBlockAt_canonicalBoundary_succ hb
      (actualWorkBoundaryCounts machine input T)
      entry.record.selectedCut).symm
  · have hheads := hdata.2.2.2.2.2.mp hdirection
    simp only [advertisedTimedCrossingDestinationBlock,
      timedCanonicalCrossingTokenOfEntry, canonicalCrossingTokenOfRecord,
      hdirection]
    change Fin.castSucc entry.record.selectedCut =
      workBlockAt hb (actualWorkBoundaryCounts machine input T)
        (run machine input (entry.time.val + 1)).workHead
    rw [hheads.2, hcut]
    exact (workBlockAt_canonicalBoundary hb
      (actualWorkBoundaryCounts machine input T)
      entry.record.selectedCut).symm

/-- The advertised post endpoint is not merely compatible with the concrete
configuration: for the actual alpha it is the exact bounded run endpoint. -/
theorem actualTimedEntry_advertisedPostEndpoint_eq_runEndpoint
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    advertisedTimedCrossingPostEndpoint
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (timedCanonicalCrossingTokenOfEntry entry) =
      fixedAlphaVisitEndpointAtRunTime machine input T
        (entry.time.val + 1) (by omega) := by
  have hmatches := actualTimedEntry_advertisedPostEndpoint_matches
    machine input T b hb entry hentry
  apply fixedAlphaVisitEndpoint_ext
  · simpa using hmatches.1
  · apply Fin.ext
    simpa using hmatches.2.1
  · apply Fin.ext
    simpa using hmatches.2.2

/-- Actual cursor at any represented configuration time. -/
noncomputable def actualTimedAlphaVisitCursorAt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (time : Nat) (htime : time ≤ T) :
    TimedAlphaVisitCursor machine.State T b :=
  { time := ⟨time, by omega⟩
    endpoint := fixedAlphaVisitEndpointAtRunTime
      machine input T time htime
    block := actualCanonicalWorkBlockAtTime
      machine input T b hb time }

@[simp]
theorem actualCanonicalWorkBlockAtTime_zero
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    actualCanonicalWorkBlockAtTime machine input T b hb 0 =
      (⟨0, Nat.succ_pos _⟩ : Fin (T / b + 1)) := by
  apply Fin.ext
  simp [actualCanonicalWorkBlockAtTime, canonicalWorkBlockAtTime,
    workHeadTrajectory, workHeadTrajectoryFrom, workBlockAt,
    selectedCanonicalBoundariesBelow, initialConfiguration]

/-- The advertised initial cursor is the actual time-zero cursor. -/
theorem initialTimedAlphaVisitCursor_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    initialTimedAlphaVisitCursor machine T b =
      actualTimedAlphaVisitCursorAt machine input T b hb 0 (Nat.zero_le T) := by
  apply timedAlphaVisitCursor_ext
  · rfl
  · apply fixedAlphaVisitEndpoint_ext <;> rfl
  · exact (actualCanonicalWorkBlockAtTime_zero
      machine input T b hb).symm

/-- Folding an actual token advances to the exact concrete post-time cursor. -/
theorem timedAlphaVisitCursorAfter_actualEntry
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    timedAlphaVisitCursorAfterCrossing
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (timedCanonicalCrossingTokenOfEntry entry) =
      actualTimedAlphaVisitCursorAt machine input T b hb
        (entry.time.val + 1) (by omega) := by
  apply timedAlphaVisitCursor_ext
  · apply Fin.ext
    rfl
  · exact actualTimedEntry_advertisedPostEndpoint_eq_runEndpoint
      machine input T b hb entry hentry
  · exact actualTimedEntry_advertisedDestinationBlock
      machine input T b hb entry hentry

/-- The terminal metadata of the extracted alpha is the exact bounded actual
endpoint at time `T`. -/
theorem chronologicalTimedCanonicalAlpha_terminal_eq_runEndpoint
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalTimedCanonicalAlpha machine input T b hb).terminal =
      fixedAlphaVisitEndpointAtRunTime machine input T T (Nat.le_refl T) := by
  apply fixedAlphaVisitEndpoint_ext <;> rfl

/-- The scheduled visit attached to one actual maximal group. -/
noncomputable def actualTimedAlphaScheduledVisitForGroup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after) :
    TimedAlphaScheduledVisit machine.State T b :=
  { block := actualCanonicalWorkBlockGroupLabel
      machine input T b hb before
    visit := actualCanonicalWorkBlockGroupVisit
      machine input T b hb before after group hsplit }

/-- At a token closing an actual group, the token's source label is the label
of that entire maximal group. -/
theorem actualTimedEntry_sourceBlock_eq_groupLabel
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (hstop : entry.time.val + 1 =
      timeGroupsLength before + group.length) :
    advertisedTimedCrossingSourceBlock
        (timedCanonicalCrossingTokenOfEntry entry) =
      actualCanonicalWorkBlockGroupLabel machine input T b hb before := by
  have hnonempty := actualCanonicalWorkBlockGroup_nonempty
    machine input T b hb before after group hsplit
  have hlength : 0 < group.length := List.length_pos_iff.mpr hnonempty
  have htime : entry.time.val =
      timeGroupsLength before + (group.length - 1) := by
    omega
  rw [actualTimedEntry_advertisedSourceBlock
    machine input T b hb entry hentry]
  unfold actualCanonicalWorkBlockGroupLabel
  rw [htime]
  exact actualCanonicalWorkBlockGroup_label_constant
    machine input T b hb before after group hsplit
      (group.length - 1) (by omega)

/-- At a proper group stop, the same token's destination label is the label of
the following maximal group. -/
theorem actualTimedEntry_destinationBlock_eq_nextGroupLabel
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T)))
    (group next : List (Fin T))
    (_hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: next :: after)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (hstop : entry.time.val + 1 =
      timeGroupsLength before + group.length) :
    advertisedTimedCrossingDestinationBlock
        (timedCanonicalCrossingTokenOfEntry entry) =
      actualCanonicalWorkBlockGroupLabel
        machine input T b hb (before ++ [group]) := by
  rw [actualTimedEntry_advertisedDestinationBlock
    machine input T b hb entry hentry]
  unfold actualCanonicalWorkBlockGroupLabel
  simp only [timeGroupsLength_append, timeGroupsLength_cons,
    timeGroupsLength_nil, Nat.add_zero]
  rw [hstop]

/-- The visit emitted by the advertised fold at an aligned group stop is
exactly the concrete maximal-group visit. -/
theorem timedAlphaScheduledVisitAt_actualGroup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (hstop : entry.time.val + 1 =
      timeGroupsLength before + group.length)
    (hstart : timeGroupsLength before ≤ T)
    (htime :
      (actualTimedAlphaVisitCursorAt machine input T b hb
        (timeGroupsLength before) hstart).time.val ≤ entry.time.val) :
    timedAlphaScheduledVisitAtCrossing
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (actualTimedAlphaVisitCursorAt machine input T b hb
          (timeGroupsLength before) hstart)
        (timedCanonicalCrossingTokenOfEntry entry) htime =
      actualTimedAlphaScheduledVisitForGroup
        machine input T b hb before after group hsplit := by
  apply timedAlphaScheduledVisit_ext
  · rfl
  · apply fixedAlphaBlockVisit_ext
    · rfl
    · apply Fin.ext
      exact hstop
    · rfl
    · change advertisedTimedCrossingPostEndpoint
          (chronologicalTimedCanonicalAlpha machine input T b hb)
          (timedCanonicalCrossingTokenOfEntry entry) =
        (actualCanonicalWorkBlockGroupVisit
          machine input T b hb before after group hsplit).exit
      rw [actualTimedEntry_advertisedPostEndpoint_eq_runEndpoint
        machine input T b hb entry hentry]
      apply fixedAlphaVisitEndpoint_ext <;>
        simp [actualCanonicalWorkBlockGroupVisit, hstop]

/-- Start time of the final group after consuming every proper group stop. -/
def finalGroupStartFrom {T : Nat} :
    Nat → List (List (Fin T)) → Nat
  | start, [] => start
  | start, [_] => start
  | start, group :: next :: rest =>
      finalGroupStartFrom (start + group.length) (next :: rest)

/-- A folded cursor exposes the exact concrete finite interface at a named run
time; the work tape itself is intentionally absent. -/
def TimedAlphaVisitCursorMatchesActualRunAt
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (hb : 0 < b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (time : Nat) : Prop :=
  cursor.time.val = time ∧
    cursor.endpoint.state = (run machine input time).state ∧
    cursor.endpoint.inputHead.val = (run machine input time).inputHead ∧
    cursor.endpoint.workHead.val = (run machine input time).workHead ∧
    cursor.block =
      actualCanonicalWorkBlockAtTime machine input T b hb time

theorem actualTimedAlphaVisitCursorAt_matches
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (time : Nat) (htime : time ≤ T) :
    TimedAlphaVisitCursorMatchesActualRunAt machine input hb
      (actualTimedAlphaVisitCursorAt machine input T b hb time htime) time := by
  simp [TimedAlphaVisitCursorMatchesActualRunAt,
    actualTimedAlphaVisitCursorAt, fixedAlphaVisitEndpointAtRunTime]

/-- Exact proper-token fold driven by the aligned maximal-group list.

The hypotheses expose only facts already proved for the concrete run: the
groups are a suffix after `beforeGroups`, every retained entry belongs to the actual
chronological list, and their post-times equal the recursive group stops. -/
theorem actualProperEntryTokenFold_from_groups
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (beforeGroups groups : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      beforeGroups ++ groups)
    (entries :
      List (ChronologicalCanonicalCrossingEntry machine.State T b))
    (hentries : ∀ entry, entry ∈ entries → entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (hstops : properGroupStopTimesFrom (timeGroupsLength beforeGroups) groups =
      entries.map (fun entry => entry.time.val + 1))
    (hstart : timeGroupsLength beforeGroups ≤ T) :
    ∃ visits finalCursor,
      TimedAlphaTokenVisitFold
          (chronologicalTimedCanonicalAlpha machine input T b hb)
          (actualTimedAlphaVisitCursorAt machine input T b hb
            (timeGroupsLength beforeGroups) hstart)
          (entries.map timedCanonicalCrossingTokenOfEntry)
          visits finalCursor ∧
        TimedAlphaVisitCursorMatchesActualRunAt machine input hb finalCursor
          (finalGroupStartFrom (timeGroupsLength beforeGroups) groups) := by
  induction groups generalizing beforeGroups entries with
  | nil =>
      have hnil : entries = [] := by
        simpa [properGroupStopTimesFrom] using hstops.symm
      subst entries
      refine ⟨[], actualTimedAlphaVisitCursorAt machine input T b hb
        (timeGroupsLength beforeGroups) hstart, ?_, ?_⟩
      · exact TimedAlphaTokenVisitFold.nil _
      · simpa [finalGroupStartFrom] using
          (actualTimedAlphaVisitCursorAt_matches
            machine input T b hb (timeGroupsLength beforeGroups) hstart)
  | cons group tail ih =>
      cases tail with
      | nil =>
          have hnil : entries = [] := by
            simpa [properGroupStopTimesFrom] using hstops.symm
          subst entries
          refine ⟨[], actualTimedAlphaVisitCursorAt machine input T b hb
            (timeGroupsLength beforeGroups) hstart, ?_, ?_⟩
          · exact TimedAlphaTokenVisitFold.nil _
          · simpa [finalGroupStartFrom] using
              (actualTimedAlphaVisitCursorAt_matches
                machine input T b hb (timeGroupsLength beforeGroups) hstart)
      | cons next rest =>
          cases entries with
          | nil => simp [properGroupStopTimesFrom] at hstops
          | cons entry remaining =>
              simp only [properGroupStopTimesFrom, List.map_cons,
                List.cons.injEq] at hstops
              have hstop : entry.time.val + 1 =
                  timeGroupsLength beforeGroups + group.length := hstops.1.symm
              have hentry : entry ∈
                  chronologicalCanonicalCrossingEntries
                    machine input T b hb := hentries entry (by simp)
              have hgroupNonempty := actualCanonicalWorkBlockGroup_nonempty
                machine input T b hb beforeGroups (next :: rest) group hsplit
              have hgroupPositive : 0 < group.length :=
                List.length_pos_iff.mpr hgroupNonempty
              have htime :
                  (actualTimedAlphaVisitCursorAt machine input T b hb
                    (timeGroupsLength beforeGroups) hstart).time.val ≤
                      entry.time.val := by
                change timeGroupsLength beforeGroups ≤ entry.time.val
                omega
              have hsourceActual :=
                actualTimedEntry_sourceBlock_eq_groupLabel
                  machine input T b hb beforeGroups (next :: rest) group hsplit
                    entry hentry hstop
              have hsource :
                  (actualTimedAlphaVisitCursorAt machine input T b hb
                    (timeGroupsLength beforeGroups) hstart).block =
                      advertisedTimedCrossingSourceBlock
                        (timedCanonicalCrossingTokenOfEntry entry) := by
                change actualCanonicalWorkBlockAtTime machine input T b hb
                    (timeGroupsLength beforeGroups) =
                  advertisedTimedCrossingSourceBlock
                    (timedCanonicalCrossingTokenOfEntry entry)
                exact hsourceActual.symm
              have hnextSplit :
                  actualCanonicalWorkBlockRuns machine input T b hb =
                    (beforeGroups ++ [group]) ++ next :: rest := by
                simpa [List.append_assoc] using hsplit
              have hnextStart : timeGroupsLength (beforeGroups ++ [group]) ≤ T := by
                simpa [timeGroupsLength_append] using
                  (actualCanonicalWorkBlockGroup_end_le_steps
                    machine input T b hb beforeGroups (next :: rest) group hsplit)
              have hremainingEntries : ∀ candidate,
                  candidate ∈ remaining → candidate ∈
                    chronologicalCanonicalCrossingEntries
                      machine input T b hb := by
                intro candidate hcandidate
                exact hentries candidate (by simp [hcandidate])
              have hremainingStops :
                  properGroupStopTimesFrom
                      (timeGroupsLength (beforeGroups ++ [group])) (next :: rest) =
                    remaining.map (fun candidate =>
                      candidate.time.val + 1) := by
                simpa [timeGroupsLength_append] using hstops.2
              obtain ⟨visits, finalCursor, htailFold, hfinalMatches⟩ :=
                ih (beforeGroups ++ [group]) hnextSplit remaining
                  hremainingEntries hremainingStops hnextStart
              have hafter :
                  timedAlphaVisitCursorAfterCrossing
                      (chronologicalTimedCanonicalAlpha machine input T b hb)
                      (timedCanonicalCrossingTokenOfEntry entry) =
                    actualTimedAlphaVisitCursorAt machine input T b hb
                      (timeGroupsLength (beforeGroups ++ [group])) hnextStart := by
                rw [timedAlphaVisitCursorAfter_actualEntry
                  machine input T b hb entry hentry]
                apply timedAlphaVisitCursor_ext
                · apply Fin.ext
                  simp [actualTimedAlphaVisitCursorAt,
                    timeGroupsLength_append]
                  omega
                · apply fixedAlphaVisitEndpoint_ext <;>
                    simp [actualTimedAlphaVisitCursorAt,
                      fixedAlphaVisitEndpointAtRunTime,
                      timeGroupsLength_append, hstop]
                · simp [actualTimedAlphaVisitCursorAt,
                    timeGroupsLength_append, hstop]
              refine ⟨timedAlphaScheduledVisitAtCrossing
                    (chronologicalTimedCanonicalAlpha machine input T b hb)
                    (actualTimedAlphaVisitCursorAt machine input T b hb
                      (timeGroupsLength beforeGroups) hstart)
                    (timedCanonicalCrossingTokenOfEntry entry) htime :: visits,
                  finalCursor, ?_, ?_⟩
              · apply TimedAlphaTokenVisitFold.cons
                  (htime := htime) (hsource := hsource)
                rw [hafter]
                exact htailFold
              · simpa [finalGroupStartFrom, timeGroupsLength_append] using
                  hfinalMatches

/-- Every exact token fold already chains all visits emitted by tokens. -/
theorem timedAlphaTokenVisitFold_chained
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {initialCursor finalCursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    (hfold : TimedAlphaTokenVisitFold alpha initialCursor tokens
      visits finalCursor) :
    TimedAlphaScheduledVisitsChained visits := by
  induction hfold with
  | nil => simp [TimedAlphaScheduledVisitsChained]
  | @cons cursor crossing rest tailVisits finalCursor
      htime hsource htail ih =>
      unfold TimedAlphaScheduledVisitsChained at ih ⊢
      cases htail with
      | nil tailCursor => simp
      | @cons tailCursor nextCrossing nextRest nextVisits nextFinal
          hnextTime hnextSource hnextTail =>
          rw [List.chain'_cons]
          constructor
          · refine ⟨rfl, rfl, ?_⟩
            change cursor.block ≠
              advertisedTimedCrossingDestinationBlock crossing
            rw [hsource]
            exact advertisedTimedCrossing_sourceBlock_ne_destinationBlock
              crossing
          · exact ih

/-- The final token-emitted visit, when one exists, ends at the returned cursor
and its source block differs from that cursor's destination block. -/
def TimedAlphaScheduledVisitEndsAtCursor
    {State : Type} {T b : Nat}
    (visit : TimedAlphaScheduledVisit State T b)
    (cursor : TimedAlphaVisitCursor State T b) : Prop :=
  visit.visit.exitTime = cursor.time ∧
    visit.visit.exit = cursor.endpoint ∧
    visit.block ≠ cursor.block

theorem timedAlphaTokenVisitFold_last_endsAtCursor
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {initialCursor finalCursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    (hfold : TimedAlphaTokenVisitFold alpha initialCursor tokens
      visits finalCursor) :
    visits = [] ∨
      ∃ before lastVisit,
        visits = before ++ [lastVisit] ∧
          TimedAlphaScheduledVisitEndsAtCursor lastVisit finalCursor := by
  induction hfold with
  | nil => exact Or.inl rfl
  | @cons cursor crossing rest tailVisits finalCursor
      htime hsource htail ih =>
      rcases ih with hnil | ⟨before, lastVisit, hvisits, hlast⟩
      · subst tailVisits
        cases htail with
        | nil tailCursor =>
            right
            refine ⟨[], timedAlphaScheduledVisitAtCrossing
              alpha cursor crossing htime, by simp, ?_⟩
            refine ⟨rfl, rfl, ?_⟩
            change cursor.block ≠
              advertisedTimedCrossingDestinationBlock crossing
            rw [hsource]
            exact advertisedTimedCrossing_sourceBlock_ne_destinationBlock
              crossing
      · right
        refine ⟨timedAlphaScheduledVisitAtCrossing
            alpha cursor crossing htime :: before,
          lastVisit, ?_, hlast⟩
        simp [hvisits]

/-- Either terminal convention preserves exact adjacent chaining: finishing at
time `T` appends nothing, while finishing earlier appends one last visit linked
to the fold's final cursor. -/
theorem timedAlphaTokenVisitFold_finish_chained
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {initialCursor finalCursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visitsSoFar visits : List (TimedAlphaScheduledVisit State T b)}
    (hfold : TimedAlphaTokenVisitFold alpha initialCursor tokens
      visitsSoFar finalCursor)
    (hfinish : TimedAlphaVisitScheduleFinish alpha finalCursor
      visitsSoFar visits) :
    TimedAlphaScheduledVisitsChained visits := by
  have hchain := timedAlphaTokenVisitFold_chained hfold
  cases hfinish with
  | atTerminal htime hendpoint => exact hchain
  | finalVisit htime hterminalHead =>
      rcases timedAlphaTokenVisitFold_last_endsAtCursor hfold with
        hnil | ⟨before, lastVisit, hvisits, hlast⟩
      · subst visitsSoFar
        simp [TimedAlphaScheduledVisitsChained]
      · have hlink : TimedAlphaScheduledVisitLink lastVisit
            (timedAlphaFinalScheduledVisit alpha finalCursor htime) := by
          simpa [TimedAlphaScheduledVisitEndsAtCursor,
            TimedAlphaScheduledVisitLink,
            timedAlphaFinalScheduledVisit] using hlast
        unfold TimedAlphaScheduledVisitsChained at hchain ⊢
        apply hchain.append
        · simp
        · intro earlier hearlier later hlater
          simp [hvisits] at hearlier hlater
          subst earlier
          subst later
          exact hlink

/-- Public total-length form of the maximal-group partition theorem. -/
theorem timeGroupsLength_actualCanonicalWorkBlockRuns_eq
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    timeGroupsLength
      (actualCanonicalWorkBlockRuns machine input T b hb) = T := by
  unfold timeGroupsLength
  rw [← List.length_flatten,
    flatten_actualCanonicalWorkBlockRuns machine input T b hb]
  simp

/-- If a group list is written as a prefix and one last group, the recursive
final start is exactly the prefix's cumulative length. -/
theorem finalGroupStartFrom_append_singleton
    {T : Nat} (start : Nat)
    (beforeGroups : List (List (Fin T))) (lastGroup : List (Fin T)) :
    finalGroupStartFrom start (beforeGroups ++ [lastGroup]) =
      start + timeGroupsLength beforeGroups := by
  induction beforeGroups generalizing start with
  | nil => simp [finalGroupStartFrom]
  | cons first rest ih =>
      cases rest with
      | nil => simp [finalGroupStartFrom, timeGroupsLength]
      | cons second rest =>
          change finalGroupStartFrom (start + first.length)
              ((second :: rest) ++ [lastGroup]) = _
          rw [ih]
          simp [timeGroupsLength]
          omega

/-- A positive time bound yields at least one nonempty transition group. -/
theorem actualCanonicalWorkBlockRuns_ne_nil_of_pos
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (hT : 0 < T) :
    actualCanonicalWorkBlockRuns machine input T b hb ≠ [] := by
  intro hnil
  have htotal := timeGroupsLength_actualCanonicalWorkBlockRuns_eq
    machine input T b hb
  rw [hnil] at htotal
  simp [timeGroupsLength] at htotal
  omega

/-- Entry times themselves are strictly chronological. -/
theorem chronologicalCanonicalCrossingEntries_pairwise_time_lt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalCanonicalCrossingEntries machine input T b hb).Pairwise
      (fun earlier later => earlier.time < later.time) := by
  simpa only [List.pairwise_map] using
    (chronologicalCanonicalCrossingEntries_times_pairwise_lt
      machine input T b hb)

/-- If no entry has terminal post-time `T`, filtering to proper entries removes
nothing. -/
theorem chronologicalEntries_eq_proper_of_no_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (hterminal : ∀ entry,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb →
        entry.time.val + 1 ≠ T) :
    chronologicalCanonicalCrossingEntries machine input T b hb =
      actualProperChronologicalCrossingEntries machine input T b hb := by
  symm
  apply List.filter_eq_self.mpr
  intro entry hentry
  apply decide_eq_true
  have hbound : entry.time.val + 1 ≤ T := entry.time.isLt
  exact lt_of_le_of_ne hbound (hterminal entry hentry)

/-- A terminal entry is uniquely last; the proper filter is exactly the prefix
before it. -/
theorem chronologicalEntries_eq_proper_append_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (htime : entry.time.val + 1 = T) :
    chronologicalCanonicalCrossingEntries machine input T b hb =
      actualProperChronologicalCrossingEntries machine input T b hb ++
        [entry] := by
  obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp hentry
  have hpair := chronologicalCanonicalCrossingEntries_pairwise_time_lt
    machine input T b hb
  rw [hsplit, List.pairwise_append] at hpair
  have htailPair : (entry :: after).Pairwise
      (fun earlier later => earlier.time < later.time) := hpair.2.1
  have hafter : after = [] := by
    cases after with
    | nil => rfl
    | cons candidate rest =>
        have hlater := (List.pairwise_cons.mp htailPair).1
          candidate (by simp)
        have hcandidateBound : candidate.time.val < T := candidate.time.isLt
        exfalso
        omega
  subst after
  have hbeforeProper : ∀ candidate,
      candidate ∈ before → candidate.time.val + 1 < T := by
    intro candidate hcandidate
    have hcross := hpair.2.2 candidate hcandidate entry (by simp)
    omega
  have hfilterBefore :
      before.filter (fun candidate =>
        decide (candidate.time.val + 1 < T)) = before := by
    apply List.filter_eq_self.mpr
    intro candidate hcandidate
    exact decide_eq_true (hbeforeProper candidate hcandidate)
  rw [actualProperChronologicalCrossingEntries, hsplit,
    List.filter_append, hfilterBefore]
  have hnotProper : ¬ entry.time.val + 1 < T := by omega
  simp [hnotProper]

/-- Specialization of the group fold to all actual proper entries and the
advertised initial cursor. -/
theorem actualProperTimedTokenFold
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    ∃ visits finalCursor,
      TimedAlphaTokenVisitFold
          (chronologicalTimedCanonicalAlpha machine input T b hb)
          (initialTimedAlphaVisitCursor machine T b)
          (actualProperTimedCrossingTokens machine input T b hb)
          visits finalCursor ∧
        TimedAlphaVisitCursorMatchesActualRunAt machine input hb finalCursor
          (finalGroupStartFrom 0
            (actualCanonicalWorkBlockRuns machine input T b hb)) := by
  have hentries : ∀ entry,
      entry ∈ actualProperChronologicalCrossingEntries machine input T b hb →
        entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb := by
    intro entry hentry
    exact (List.mem_filter.mp hentry).1
  obtain ⟨visits, finalCursor, hfold, hmatches⟩ :=
    actualProperEntryTokenFold_from_groups
      machine input T b hb []
      (actualCanonicalWorkBlockRuns machine input T b hb) (by simp)
      (actualProperChronologicalCrossingEntries machine input T b hb)
      hentries (by simpa [timeGroupsLength] using
        (properGroupStops_eq_map_actualProperEntryPostTimes
          machine input T b hb)) (by simp [timeGroupsLength])
  refine ⟨visits, finalCursor, ?_, hmatches⟩
  rw [initialTimedAlphaVisitCursor_eq_actual machine input T b hb]
  rw [← map_actualProperEntries_eq_actualProperTokens]
  exact hfold

/-- Appending one token at the final cursor extends an exact fold without
rebuilding its prefix. -/
theorem timedAlphaTokenVisitFold_append_one
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {initialCursor finalCursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    (hfold : TimedAlphaTokenVisitFold alpha initialCursor tokens
      visits finalCursor)
    (crossing : TimedCanonicalCrossingToken State T b)
    (htime : finalCursor.time.val ≤ crossing.sourceTime.val)
    (hsource : finalCursor.block =
      advertisedTimedCrossingSourceBlock crossing) :
    TimedAlphaTokenVisitFold alpha initialCursor (tokens ++ [crossing])
      (visits ++ [timedAlphaScheduledVisitAtCrossing
        alpha finalCursor crossing htime])
      (timedAlphaVisitCursorAfterCrossing alpha crossing) := by
  revert crossing
  induction hfold with
  | nil cursor =>
      intro crossing htime hsource
      exact TimedAlphaTokenVisitFold.cons cursor crossing [] []
        (timedAlphaVisitCursorAfterCrossing alpha crossing)
        htime hsource (TimedAlphaTokenVisitFold.nil _)
  | @cons cursor first rest tailVisits oldFinal
      hfirstTime hfirstSource htail ih =>
      intro crossing htime hsource
      exact TimedAlphaTokenVisitFold.cons cursor first
        (rest ++ [crossing])
        (tailVisits ++ [timedAlphaScheduledVisitAtCrossing
          alpha oldFinal crossing htime])
        (timedAlphaVisitCursorAfterCrossing alpha crossing)
        hfirstTime hfirstSource (ih crossing htime hsource)

/-- For positive `T`, expose the final actual group together with its exact
cumulative start, total end, and recursive final-start identity. -/
theorem exists_actualCanonicalLastGroup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (hT : 0 < T) :
    ∃ beforeGroups lastGroup,
      actualCanonicalWorkBlockRuns machine input T b hb =
          beforeGroups ++ [lastGroup] ∧
        lastGroup ≠ [] ∧
        timeGroupsLength beforeGroups + lastGroup.length = T ∧
        finalGroupStartFrom 0
            (actualCanonicalWorkBlockRuns machine input T b hb) =
          timeGroupsLength beforeGroups := by
  let groups := actualCanonicalWorkBlockRuns machine input T b hb
  have hgroups : groups ≠ [] :=
    actualCanonicalWorkBlockRuns_ne_nil_of_pos machine input T b hb hT
  let beforeGroups := groups.dropLast
  let lastGroup := groups.getLast hgroups
  have hdecomp : groups = beforeGroups ++ [lastGroup] := by
    exact (List.dropLast_append_getLast hgroups).symm
  have hlastMem : lastGroup ∈ groups := by
    exact List.getLast_mem hgroups
  have hlastNonempty : lastGroup ≠ [] :=
    actualCanonicalWorkBlockRuns_nonempty machine input T b hb hlastMem
  have htotal := timeGroupsLength_actualCanonicalWorkBlockRuns_eq
    machine input T b hb
  change timeGroupsLength groups = T at htotal
  rw [hdecomp, timeGroupsLength_append, timeGroupsLength_cons,
    timeGroupsLength_nil, Nat.add_zero] at htotal
  refine ⟨beforeGroups, lastGroup, ?_, hlastNonempty, htotal, ?_⟩
  · exact hdecomp
  · rw [show actualCanonicalWorkBlockRuns machine input T b hb = groups
      from rfl, hdecomp, finalGroupStartFrom_append_singleton]
    simp

/-- With no terminal crossing entry, the proper fold closes by the unique
positive final visit (or, when `T = 0`, by exact terminal equality). -/
theorem actualFinalCursor_finish_of_no_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (visitsSoFar : List (TimedAlphaScheduledVisit machine.State T b))
    (hmatches : TimedAlphaVisitCursorMatchesActualRunAt
      machine input hb cursor
        (finalGroupStartFrom 0
          (actualCanonicalWorkBlockRuns machine input T b hb)))
    (hterminal : ∀ entry,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb →
        entry.time.val + 1 ≠ T) :
    ∃ visits,
      TimedAlphaVisitScheduleFinish
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        cursor visitsSoFar visits := by
  by_cases hT : T = 0
  · subst T
    have hgroups := actualCanonicalWorkBlockRuns_zero machine input b hb
    have hmatchesZero : TimedAlphaVisitCursorMatchesActualRunAt
        machine input hb cursor 0 := by
      simpa [hgroups, finalGroupStartFrom] using hmatches
    refine ⟨visitsSoFar, TimedAlphaVisitScheduleFinish.atTerminal
      hmatchesZero.1 ?_⟩
    rw [chronologicalTimedCanonicalAlpha_terminal_eq_runEndpoint]
    apply fixedAlphaVisitEndpoint_ext
    · exact hmatchesZero.2.1
    · apply Fin.ext
      exact hmatchesZero.2.2.1
    · apply Fin.ext
      exact hmatchesZero.2.2.2.1
  · have hTpos : 0 < T := Nat.pos_of_ne_zero hT
    obtain ⟨beforeGroups, lastGroup, hsplit, hlastNonempty,
      htotal, hfinalStart⟩ :=
      exists_actualCanonicalLastGroup machine input T b hb hTpos
    have hcursorTime : cursor.time.val = timeGroupsLength beforeGroups :=
      hmatches.1.trans hfinalStart
    have hcursorBlock : cursor.block =
        actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength beforeGroups) := by
      simpa [hfinalStart] using hmatches.2.2.2.2
    have hfinishTime : cursor.time.val < T := by
      have hlastPositive : 0 < lastGroup.length :=
        List.length_pos_iff.mpr hlastNonempty
      omega
    have hlastLabel := actualCanonicalWorkBlockGroup_label_constant
      machine input T b hb beforeGroups [] lastGroup hsplit
        (lastGroup.length - 1) (by
          exact Nat.sub_lt (List.length_pos_iff.mpr hlastNonempty)
            (Nat.zero_lt_one))
    have hlastTime :
        timeGroupsLength beforeGroups + (lastGroup.length - 1) = T - 1 := by
      have hlastPositive : 0 < lastGroup.length :=
        List.length_pos_iff.mpr hlastNonempty
      omega
    have hnoLastCrossing :
        actualCanonicalWorkBlockAtTime machine input T b hb (T - 1) =
          actualCanonicalWorkBlockAtTime machine input T b hb T := by
      by_contra hne
      obtain ⟨entry, hentry, hentryTime⟩ :=
        (exists_chronologicalEntry_at_lastTransition_iff
          machine input T b hb hTpos).mpr hne
      apply hterminal entry hentry
      have hvalue := congrArg Fin.val hentryTime
      change entry.time.val = T - 1 at hvalue
      omega
    have hblockTerminal :
        actualCanonicalWorkBlockAtTime machine input T b hb T =
          cursor.block := by
      calc
        actualCanonicalWorkBlockAtTime machine input T b hb T =
            actualCanonicalWorkBlockAtTime machine input T b hb (T - 1) :=
          hnoLastCrossing.symm
        _ = actualCanonicalWorkBlockAtTime machine input T b hb
              (timeGroupsLength beforeGroups) := by
          rw [← hlastTime]
          exact hlastLabel
        _ = cursor.block := hcursorBlock.symm
    have hcanonical := workHeadTrajectory_in_canonicalBlockSlab
      hb (actualWorkBoundaryCounts machine input T)
      machine input T (Nat.le_refl T) cursor.block (by
        simpa [actualCanonicalWorkBlockAtTime,
          actualWorkBoundaryCounts] using hblockTerminal)
    have hterminalHead : WorkCellInSlab
        (advertisedBlockLower
          (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
          cursor.block)
        (advertisedBlockWidth
          (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
          cursor.block)
        (chronologicalTimedCanonicalAlpha machine input T b hb).terminal.workHead.val := by
      simpa [chronologicalTimedCanonicalAlpha,
        actualWorkBoundaryCounts, workHeadTrajectory, workHeadTrajectoryFrom,
        run] using hcanonical
    refine ⟨visitsSoFar ++ [timedAlphaFinalScheduledVisit
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        cursor hfinishTime], ?_⟩
    exact TimedAlphaVisitScheduleFinish.finalVisit hfinishTime hterminalHead

/-- No terminal entry means the full actual timed-token list is exactly its
proper prefix. -/
theorem chronologicalTimedTokens_eq_proper_of_no_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (hterminal : ∀ entry,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb →
        entry.time.val + 1 ≠ T) :
    chronologicalTimedCanonicalCrossingTokens machine input T b hb =
      actualProperTimedCrossingTokens machine input T b hb := by
  rw [chronologicalTimedCanonicalCrossingTokens,
    chronologicalEntries_eq_proper_of_no_terminal
      machine input T b hb hterminal,
    map_actualProperEntries_eq_actualProperTokens]

/-- Completeness of the advertised schedule in the no-terminal-crossing case,
including `T = 0` and the positive final-visit convention. -/
theorem exists_actualTimedAlphaVisitScheduleValid_of_no_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (hterminal : ∀ entry,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb →
        entry.time.val + 1 ≠ T) :
    ∃ visits,
      TimedAlphaVisitScheduleValid machine
        (chronologicalTimedCanonicalAlpha machine input T b hb) visits := by
  obtain ⟨visitsSoFar, finalCursor, hfold, hmatches⟩ :=
    actualProperTimedTokenFold machine input T b hb
  obtain ⟨visits, hfinish⟩ := actualFinalCursor_finish_of_no_terminal
    machine input T b hb finalCursor visitsSoFar hmatches hterminal
  have hchained := timedAlphaTokenVisitFold_finish_chained hfold hfinish
  refine ⟨visits,
    chronologicalTimedCanonicalAlpha_word_syntacticallyValid
      machine input T b hb, finalCursor, visitsSoFar, ?_, hfinish, hchained⟩
  rw [decode_chronologicalTimedCanonicalAlpha_word,
    chronologicalTimedTokens_eq_proper_of_no_terminal
      machine input T b hb hterminal]
  exact hfold

/-- A terminal crossing entry is the unique final token after the proper token
prefix. -/
theorem chronologicalTimedTokens_eq_proper_append_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (htime : entry.time.val + 1 = T) :
    chronologicalTimedCanonicalCrossingTokens machine input T b hb =
      actualProperTimedCrossingTokens machine input T b hb ++
        [timedCanonicalCrossingTokenOfEntry entry] := by
  rw [chronologicalTimedCanonicalCrossingTokens,
    chronologicalEntries_eq_proper_append_terminal
      machine input T b hb entry hentry htime,
    List.map_append, map_actualProperEntries_eq_actualProperTokens]
  rfl

/-- Completeness when the last transition crosses a selected cut: the terminal
token emits the last nonempty group visit, advances to time `T`, and the finish
constructor appends no zero-length visit. -/
theorem exists_actualTimedAlphaVisitScheduleValid_of_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (htime : entry.time.val + 1 = T) :
    ∃ visits,
      TimedAlphaVisitScheduleValid machine
        (chronologicalTimedCanonicalAlpha machine input T b hb) visits := by
  have hTpos : 0 < T := by omega
  obtain ⟨visitsSoFar, cursor, hproperFold, hmatches⟩ :=
    actualProperTimedTokenFold machine input T b hb
  obtain ⟨beforeGroups, lastGroup, hsplit, hlastNonempty,
    htotal, hfinalStart⟩ :=
    exists_actualCanonicalLastGroup machine input T b hb hTpos
  have hcursorTime : cursor.time.val = timeGroupsLength beforeGroups :=
    hmatches.1.trans hfinalStart
  have hcursorBlock : cursor.block =
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength beforeGroups) := by
    simpa [hfinalStart] using hmatches.2.2.2.2
  have hgroupSplit :
      actualCanonicalWorkBlockRuns machine input T b hb =
        beforeGroups ++ lastGroup :: [] := by
    simpa using hsplit
  have hgroupStop : entry.time.val + 1 =
      timeGroupsLength beforeGroups + lastGroup.length :=
    htime.trans htotal.symm
  have hsourceActual := actualTimedEntry_sourceBlock_eq_groupLabel
    machine input T b hb beforeGroups [] lastGroup hgroupSplit
      entry hentry hgroupStop
  have hsource : cursor.block =
      advertisedTimedCrossingSourceBlock
        (timedCanonicalCrossingTokenOfEntry entry) := by
    change cursor.block =
      advertisedTimedCrossingSourceBlock
        (timedCanonicalCrossingTokenOfEntry entry)
    exact hcursorBlock.trans hsourceActual.symm
  have hfoldTime : cursor.time.val ≤ entry.time.val := by
    have hlastPositive : 0 < lastGroup.length :=
      List.length_pos_iff.mpr hlastNonempty
    omega
  let terminalToken := timedCanonicalCrossingTokenOfEntry entry
  let terminalVisit := timedAlphaScheduledVisitAtCrossing
    (chronologicalTimedCanonicalAlpha machine input T b hb)
    cursor terminalToken hfoldTime
  let terminalCursor := timedAlphaVisitCursorAfterCrossing
    (chronologicalTimedCanonicalAlpha machine input T b hb) terminalToken
  have hfold : TimedAlphaTokenVisitFold
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      (initialTimedAlphaVisitCursor machine T b)
      (actualProperTimedCrossingTokens machine input T b hb ++
        [terminalToken])
      (visitsSoFar ++ [terminalVisit]) terminalCursor := by
    exact timedAlphaTokenVisitFold_append_one hproperFold terminalToken
      hfoldTime hsource
  have hterminalTime : terminalCursor.time.val = T := by
    change entry.time.val + 1 = T
    exact htime
  have hterminalEndpoint : terminalCursor.endpoint =
      (chronologicalTimedCanonicalAlpha machine input T b hb).terminal := by
    change advertisedTimedCrossingPostEndpoint
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (timedCanonicalCrossingTokenOfEntry entry) =
      (chronologicalTimedCanonicalAlpha machine input T b hb).terminal
    rw [actualTimedEntry_advertisedPostEndpoint_eq_runEndpoint
      machine input T b hb entry hentry,
      chronologicalTimedCanonicalAlpha_terminal_eq_runEndpoint]
    apply fixedAlphaVisitEndpoint_ext <;>
      simp [fixedAlphaVisitEndpointAtRunTime, htime]
  have hfinish : TimedAlphaVisitScheduleFinish
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      terminalCursor (visitsSoFar ++ [terminalVisit])
      (visitsSoFar ++ [terminalVisit]) :=
    TimedAlphaVisitScheduleFinish.atTerminal
      hterminalTime hterminalEndpoint
  have hchained := timedAlphaTokenVisitFold_finish_chained hfold hfinish
  refine ⟨visitsSoFar ++ [terminalVisit],
    chronologicalTimedCanonicalAlpha_word_syntacticallyValid
      machine input T b hb, terminalCursor, visitsSoFar ++ [terminalVisit],
    ?_, hfinish, hchained⟩
  rw [decode_chronologicalTimedCanonicalAlpha_word,
    chronologicalTimedTokens_eq_proper_append_terminal
      machine input T b hb entry hentry htime]
  exact hfold

/-- Unconditional advertised-schedule completeness for the timed alpha
extracted from every concrete run.

The proof splits only on the real endpoint convention: either a last-transition
crossing token exists and closes the last group at time `T`, or it does not and
one positive final visit closes the last group (with the degenerate `T = 0`
case finishing without a visit).  This theorem adds no replay, minimal-cut, or
arbitrary-alpha soundness assumption. -/
theorem exists_actualTimedAlphaVisitScheduleValid
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    ∃ visits,
      TimedAlphaVisitScheduleValid machine
        (chronologicalTimedCanonicalAlpha machine input T b hb) visits := by
  by_cases hterminal : ∃ entry :
      ChronologicalCanonicalCrossingEntry machine.State T b,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb ∧
        entry.time.val + 1 = T
  · obtain ⟨entry, hentry, htime⟩ := hterminal
    exact exists_actualTimedAlphaVisitScheduleValid_of_terminal
      machine input T b hb entry hentry htime
  · apply exists_actualTimedAlphaVisitScheduleValid_of_no_terminal
    intro entry hentry htime
    exact hterminal ⟨entry, hentry, htime⟩

end OneTapeMagnification
end Frontier
end Pnp4
