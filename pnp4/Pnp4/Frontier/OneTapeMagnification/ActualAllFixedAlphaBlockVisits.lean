import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualFixedAlphaBlockVisitCarry
import Pnp4.Frontier.OneTapeMagnification.ActualTimedAlphaVisitSchedule

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# All actual visits to one fixed alpha block

This module removes the two-visit restriction from the actual fixed-block
replay layer.  It scans the complete list of actual maximal work-block groups,
retains exactly the groups whose actual label is a fixed target block, and
threads one carried target slab through the resulting list.

The key invariant is deliberately concrete.  Across a retained target group,
the validator output is the actual target slab at that group's exit.  Across a
discarded group, disjointness of canonical slabs implies that the actual target
slab is unchanged.  Consequently the recursive validator accepts an arbitrary
number of actual returns without a reset or an independently supplied
midpoint tape.

This remains an actual-run completeness theorem.  It does not establish
soundness for an arbitrary advertised alpha, cut minimality, a circuit lower
bound, or the `PpolyDAG` bridge.
-/

/-- One actual maximal group whose label differs from `target` leaves the
actual restriction of the target canonical slab unchanged. -/
theorem actualFixedAlphaBlockSlabAtTime_eq_after_away_group
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before after : List (List (Fin T))) (group : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: after)
    (haway : actualCanonicalWorkBlockGroupLabel
      machine input T b hb before ≠ target) :
    actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before + group.length) =
      actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before) := by
  let crossings := actualWorkBoundaryCounts machine input T
  let visited := actualCanonicalWorkBlockGroupLabel
    machine input T b hb before
  let visitedBase := canonicalBlockLower hb crossings visited
  let visitedWidth := canonicalBlockWidth hb crossings visited
  let targetBase := canonicalBlockLower hb crossings target
  let targetWidth := canonicalBlockWidth hb crossings target
  have hdisjoint : WorkSlabsDisjoint
      visitedBase visitedWidth targetBase targetWidth := by
    exact canonicalBlockSlabsDisjoint_of_ne
      hb crossings visited target haway
  have havoids : ∀ time, time < group.length →
      ¬ WorkCellInSlab targetBase targetWidth
        (runFrom machine input
          (run machine input (timeGroupsLength before)) time).workHead := by
    intro time htime htarget
    have hvisitedGlobal := actualCanonicalWorkBlockGroup_workHead_in_slab
      machine input T b hb before after group hsplit time htime
    have hrun :
        run machine input (timeGroupsLength before + time) =
          runFrom machine input
            (run machine input (timeGroupsLength before)) time := by
      simpa [run] using
        (runFrom_add_eq_runFrom_runFrom machine input
          (initialConfiguration machine) (timeGroupsLength before) time)
    have hvisited : WorkCellInSlab visitedBase visitedWidth
        (runFrom machine input
          (run machine input (timeGroupsLength before)) time).workHead := by
      have := congrArg Configuration.workHead hrun ▸ hvisitedGlobal
      simpa [visitedBase, visitedWidth, visited,
        actualCanonicalWorkBlockGroupLabel, crossings,
        actualWorkBoundaryCounts] using this
    exact hdisjoint _ hvisited htarget
  have hpersistence := restrictWorkSlab_runFrom_eq_of_avoids
    machine input (run machine input (timeGroupsLength before))
      targetBase targetWidth group.length havoids
  have hrunEnd :
      runFrom machine input
          (run machine input (timeGroupsLength before)) group.length =
        run machine input (timeGroupsLength before + group.length) := by
    symm
    simpa [run] using
      (runFrom_add_eq_runFrom_runFrom machine input
        (initialConfiguration machine) (timeGroupsLength before) group.length)
  rw [hrunEnd] at hpersistence
  simpa [actualFixedAlphaBlockSlabAtTime,
    chronologicalTimedCanonicalAlpha, actualWorkBoundaryCounts,
    targetBase, targetWidth, crossings] using hpersistence

/-- Relational scan of a suffix of the actual maximal-group list.  `before`
is the already consumed prefix.  A target-labelled group contributes its
concrete fixed-alpha visit; every other group contributes nothing. -/
inductive ActualFixedAlphaBlockVisitsFromGroups
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1)) :
    List (List (Fin T)) -> List (List (Fin T)) ->
      List (FixedAlphaBlockVisit machine.State T) -> Prop
  | nil (before : List (List (Fin T))) :
      ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target
        before [] []
  | skip
      (before : List (List (Fin T)))
      (group : List (Fin T)) (rest : List (List (Fin T)))
      (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
        before ++ group :: rest)
      (haway : actualCanonicalWorkBlockGroupLabel
        machine input T b hb before ≠ target)
      (visits : List (FixedAlphaBlockVisit machine.State T))
      (htail : ActualFixedAlphaBlockVisitsFromGroups
        machine input T b hb target (before ++ [group]) rest visits) :
      ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target
        before (group :: rest) visits
  | keep
      (before : List (List (Fin T)))
      (group : List (Fin T)) (rest : List (List (Fin T)))
      (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
        before ++ group :: rest)
      (htarget : actualCanonicalWorkBlockGroupLabel
        machine input T b hb before = target)
      (visits : List (FixedAlphaBlockVisit machine.State T))
      (htail : ActualFixedAlphaBlockVisitsFromGroups
        machine input T b hb target (before ++ [group]) rest visits) :
      ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target
        before (group :: rest)
          (actualCanonicalWorkBlockGroupVisit
            machine input T b hb before rest group hsplit :: visits)

/-- Unfiltered scheduled-side counterpart of the actual group scan: exactly
one advertised scheduled visit is stored for every actual maximal group. -/
inductive ActualTimedAlphaScheduledVisitsFromGroups
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (List (Fin T)) -> List (List (Fin T)) ->
      List (TimedAlphaScheduledVisit machine.State T b) -> Prop
  | nil (before : List (List (Fin T))) :
      ActualTimedAlphaScheduledVisitsFromGroups machine input T b hb
        before [] []
  | cons
      (before : List (List (Fin T)))
      (group : List (Fin T)) (rest : List (List (Fin T)))
      (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
        before ++ group :: rest)
      (visits : List (TimedAlphaScheduledVisit machine.State T b))
      (htail : ActualTimedAlphaScheduledVisitsFromGroups
        machine input T b hb (before ++ [group]) rest visits) :
      ActualTimedAlphaScheduledVisitsFromGroups machine input T b hb
        before (group :: rest)
          (actualTimedAlphaScheduledVisitForGroup
            machine input T b hb before rest group hsplit :: visits)

/-- Token folds emit exactly the visits of all groups except the final group;
the terminal convention later supplies that one remaining visit. -/
inductive ActualProperTimedAlphaScheduledVisitsFromGroups
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (List (Fin T)) -> List (List (Fin T)) ->
      List (TimedAlphaScheduledVisit machine.State T b) -> Prop
  | nil (before : List (List (Fin T))) :
      ActualProperTimedAlphaScheduledVisitsFromGroups
        machine input T b hb before [] []
  | singleton
      (before : List (List (Fin T))) (group : List (Fin T))
      (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
        before ++ [group]) :
      ActualProperTimedAlphaScheduledVisitsFromGroups
        machine input T b hb before [group] []
  | cons
      (before : List (List (Fin T)))
      (group next : List (Fin T)) (rest : List (List (Fin T)))
      (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
        before ++ group :: next :: rest)
      (visits : List (TimedAlphaScheduledVisit machine.State T b))
      (htail : ActualProperTimedAlphaScheduledVisitsFromGroups
        machine input T b hb (before ++ [group]) (next :: rest) visits) :
      ActualProperTimedAlphaScheduledVisitsFromGroups
        machine input T b hb before (group :: next :: rest)
          (actualTimedAlphaScheduledVisitForGroup machine input T b hb
            before (next :: rest) group hsplit :: visits)

/-- Appending the concrete visit of a named final group completes an exact
proper-group list into the exact all-group scheduled list. -/
theorem ActualProperTimedAlphaScheduledVisitsFromGroups.complete_with_last
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before groups : List (List (Fin T)))
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hproper : ActualProperTimedAlphaScheduledVisitsFromGroups
      machine input T b hb before groups visits)
    (leading : List (List (Fin T))) (last : List (Fin T))
    (hgroups : groups = leading ++ [last])
    (hlastSplit : actualCanonicalWorkBlockRuns machine input T b hb =
      (before ++ leading) ++ last :: []) :
    ActualTimedAlphaScheduledVisitsFromGroups machine input T b hb
      before groups
        (visits ++ [actualTimedAlphaScheduledVisitForGroup
          machine input T b hb (before ++ leading) [] last hlastSplit]) := by
  induction hproper generalizing leading last with
  | nil currentBefore =>
      have hlength := congrArg List.length hgroups
      simp at hlength
  | singleton currentBefore group hsplit =>
      cases leading with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hgroups
          rcases hgroups with ⟨hgroupLast, _⟩
          subst last
          simpa using
            (ActualTimedAlphaScheduledVisitsFromGroups.cons
              currentBefore group [] hsplit []
                (ActualTimedAlphaScheduledVisitsFromGroups.nil
                  (currentBefore ++ [group])))
      | cons first tail =>
          have hlength := congrArg List.length hgroups
          simp at hlength
  | @cons currentBefore group next rest hsplit tailVisits htail ih =>
      cases leading with
      | nil =>
          have hlength := congrArg List.length hgroups
          simp at hlength
      | cons first prefixTail =>
          simp only [List.cons_append, List.cons.injEq] at hgroups
          rcases hgroups with ⟨hfirst, htailGroups⟩
          subst first
          have hlastSplitTail :
              actualCanonicalWorkBlockRuns machine input T b hb =
                ((currentBefore ++ [group]) ++ prefixTail) ++ last :: [] := by
            simpa [List.append_assoc] using hlastSplit
          have hcompletedTail := ih prefixTail last htailGroups hlastSplitTail
          simpa [List.append_assoc] using
            (ActualTimedAlphaScheduledVisitsFromGroups.cons
              currentBefore group (next :: rest) hsplit
                (tailVisits ++ [actualTimedAlphaScheduledVisitForGroup
                  machine input T b hb
                    ((currentBefore ++ [group]) ++ prefixTail) [] last
                      hlastSplitTail]) hcompletedTail)

/-- Strengthened proper-token fold: besides the advertised fold and actual
cursor match, the emitted list is recorded as exactly the actual groups except
the final one. -/
theorem actualProperEntryTokenFold_from_groups_with_schedule
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
          (finalGroupStartFrom (timeGroupsLength beforeGroups) groups) ∧
        ActualProperTimedAlphaScheduledVisitsFromGroups
          machine input T b hb beforeGroups groups visits := by
  induction groups generalizing beforeGroups entries with
  | nil =>
      have hnil : entries = [] := by
        simpa [properGroupStopTimesFrom] using hstops.symm
      subst entries
      refine ⟨[], actualTimedAlphaVisitCursorAt machine input T b hb
        (timeGroupsLength beforeGroups) hstart, ?_, ?_, ?_⟩
      · exact TimedAlphaTokenVisitFold.nil _
      · simpa [finalGroupStartFrom] using
          (actualTimedAlphaVisitCursorAt_matches
            machine input T b hb (timeGroupsLength beforeGroups) hstart)
      · exact ActualProperTimedAlphaScheduledVisitsFromGroups.nil beforeGroups
  | cons group tail ih =>
      cases tail with
      | nil =>
          have hnil : entries = [] := by
            simpa [properGroupStopTimesFrom] using hstops.symm
          subst entries
          have hsingleSplit :
              actualCanonicalWorkBlockRuns machine input T b hb =
                beforeGroups ++ [group] := by
            simpa using hsplit
          refine ⟨[], actualTimedAlphaVisitCursorAt machine input T b hb
            (timeGroupsLength beforeGroups) hstart, ?_, ?_, ?_⟩
          · exact TimedAlphaTokenVisitFold.nil _
          · simpa [finalGroupStartFrom] using
              (actualTimedAlphaVisitCursorAt_matches
                machine input T b hb (timeGroupsLength beforeGroups) hstart)
          · exact ActualProperTimedAlphaScheduledVisitsFromGroups.singleton
              beforeGroups group hsingleSplit
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
              obtain ⟨visits, finalCursor, htailFold, hfinalMatches,
                  htailSchedule⟩ :=
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
              let emitted := timedAlphaScheduledVisitAtCrossing
                (chronologicalTimedCanonicalAlpha machine input T b hb)
                (actualTimedAlphaVisitCursorAt machine input T b hb
                  (timeGroupsLength beforeGroups) hstart)
                (timedCanonicalCrossingTokenOfEntry entry) htime
              refine ⟨emitted :: visits, finalCursor, ?_, ?_, ?_⟩
              · apply TimedAlphaTokenVisitFold.cons
                  (htime := htime) (hsource := hsource)
                rw [hafter]
                exact htailFold
              · simpa [finalGroupStartFrom, timeGroupsLength_append] using
                  hfinalMatches
              · have hemitted : emitted =
                    actualTimedAlphaScheduledVisitForGroup
                      machine input T b hb beforeGroups (next :: rest) group
                        hsplit := by
                  exact timedAlphaScheduledVisitAt_actualGroup
                    machine input T b hb beforeGroups (next :: rest) group
                      hsplit entry hentry hstop hstart htime
                rw [hemitted]
                exact ActualProperTimedAlphaScheduledVisitsFromGroups.cons
                  beforeGroups group next rest hsplit visits htailSchedule

/-- Specialization of the strengthened fold to all proper actual crossing
entries. -/
theorem actualProperTimedTokenFold_with_schedule
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
            (actualCanonicalWorkBlockRuns machine input T b hb)) ∧
        ActualProperTimedAlphaScheduledVisitsFromGroups machine input T b hb []
          (actualCanonicalWorkBlockRuns machine input T b hb) visits := by
  have hentries : ∀ entry,
      entry ∈ actualProperChronologicalCrossingEntries machine input T b hb →
        entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb := by
    intro entry hentry
    exact (List.mem_filter.mp hentry).1
  obtain ⟨visits, finalCursor, hfold, hmatches, hschedule⟩ :=
    actualProperEntryTokenFold_from_groups_with_schedule
      machine input T b hb []
      (actualCanonicalWorkBlockRuns machine input T b hb) (by simp)
      (actualProperChronologicalCrossingEntries machine input T b hb)
      hentries (by simpa [timeGroupsLength] using
        (properGroupStops_eq_map_actualProperEntryPostTimes
          machine input T b hb)) (by simp [timeGroupsLength])
  refine ⟨visits, finalCursor, ?_, hmatches, hschedule⟩
  rw [initialTimedAlphaVisitCursor_eq_actual machine input T b hb]
  rw [← map_actualProperEntries_eq_actualProperTokens]
  exact hfold

/-- A cursor satisfying the concrete finite-interface invariant is the
canonical actual cursor at that time. -/
theorem timedAlphaVisitCursor_eq_actual_of_matches
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (time : Nat) (htime : time ≤ T)
    (hmatches : TimedAlphaVisitCursorMatchesActualRunAt
      machine input hb cursor time) :
    cursor = actualTimedAlphaVisitCursorAt
      machine input T b hb time htime := by
  apply timedAlphaVisitCursor_ext
  · apply Fin.ext
    exact hmatches.1
  · apply fixedAlphaVisitEndpoint_ext
    · simpa [actualTimedAlphaVisitCursorAt,
        fixedAlphaVisitEndpointAtRunTime] using hmatches.2.1
    · apply Fin.ext
      simpa [actualTimedAlphaVisitCursorAt,
        fixedAlphaVisitEndpointAtRunTime] using hmatches.2.2.1
    · apply Fin.ext
      simpa [actualTimedAlphaVisitCursorAt,
        fixedAlphaVisitEndpointAtRunTime] using hmatches.2.2.2.1
  · simpa [actualTimedAlphaVisitCursorAt] using hmatches.2.2.2.2

/-- The positive final visit emitted by the no-terminal-token convention is
exactly the concrete visit of the final actual maximal group. -/
theorem timedAlphaFinalScheduledVisit_eq_actualLastGroup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (before : List (List (Fin T))) (last : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [last])
    (htotal : timeGroupsLength before + last.length = T)
    (hmatches : TimedAlphaVisitCursorMatchesActualRunAt
      machine input hb cursor (timeGroupsLength before))
    (hfinishTime : cursor.time.val < T) :
    timedAlphaFinalScheduledVisit
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        cursor hfinishTime =
      actualTimedAlphaScheduledVisitForGroup
        machine input T b hb before [] last (by simpa using hsplit) := by
  have hstart : timeGroupsLength before ≤ T := by omega
  have hcursor := timedAlphaVisitCursor_eq_actual_of_matches
    machine input T b hb cursor (timeGroupsLength before) hstart hmatches
  subst cursor
  apply timedAlphaScheduledVisit_ext
  · rfl
  · apply fixedAlphaBlockVisit_ext
    · rfl
    · apply Fin.ext
      exact htotal.symm
    · apply fixedAlphaVisitEndpoint_ext <;> rfl
    · change (chronologicalTimedCanonicalAlpha
          machine input T b hb).terminal =
        (actualCanonicalWorkBlockGroupVisit
          machine input T b hb before [] last (by simpa using hsplit)).exit
      rw [chronologicalTimedCanonicalAlpha_terminal_eq_runEndpoint]
      apply fixedAlphaVisitEndpoint_ext
      · change (run machine input T).state =
          (run machine input
            (timeGroupsLength before + last.length)).state
        rw [htotal]
      · apply Fin.ext
        change (run machine input T).inputHead =
          (run machine input
            (timeGroupsLength before + last.length)).inputHead
        rw [htotal]
      · apply Fin.ext
        change (run machine input T).workHead =
          (run machine input
            (timeGroupsLength before + last.length)).workHead
        rw [htotal]

/-- The token-emitted terminal visit is likewise the exact final actual group
visit once its cursor is known to match the actual final-group start. -/
theorem timedAlphaScheduledVisitAtCrossing_eq_actualLastGroup
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (before : List (List (Fin T))) (last : List (Fin T))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [last])
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (hstop : entry.time.val + 1 =
      timeGroupsLength before + last.length)
    (hstart : timeGroupsLength before ≤ T)
    (htime : cursor.time.val ≤ entry.time.val)
    (hmatches : TimedAlphaVisitCursorMatchesActualRunAt
      machine input hb cursor (timeGroupsLength before)) :
    timedAlphaScheduledVisitAtCrossing
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        cursor (timedCanonicalCrossingTokenOfEntry entry) htime =
      actualTimedAlphaScheduledVisitForGroup
        machine input T b hb before [] last (by simpa using hsplit) := by
  have hcursor := timedAlphaVisitCursor_eq_actual_of_matches
    machine input T b hb cursor (timeGroupsLength before) hstart hmatches
  subst cursor
  exact timedAlphaScheduledVisitAt_actualGroup
    machine input T b hb before [] last (by simpa using hsplit)
      entry hentry hstop hstart htime

/-- Schedule completeness with the exact all-group relation in the
last-transition-crossing convention. -/
theorem exists_actualTimedAlphaVisitScheduleValid_with_groups_of_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (htime : entry.time.val + 1 = T) :
    ∃ visits,
      TimedAlphaVisitScheduleValid machine
          (chronologicalTimedCanonicalAlpha machine input T b hb) visits ∧
        ActualTimedAlphaScheduledVisitsFromGroups machine input T b hb []
          (actualCanonicalWorkBlockRuns machine input T b hb) visits := by
  have hTpos : 0 < T := by omega
  obtain ⟨visitsSoFar, cursor, hproperFold, hmatches, hproperSchedule⟩ :=
    actualProperTimedTokenFold_with_schedule machine input T b hb
  obtain ⟨beforeGroups, lastGroup, hsplit, hlastNonempty,
    htotal, hfinalStart⟩ :=
    exists_actualCanonicalLastGroup machine input T b hb hTpos
  have hmatchesLast : TimedAlphaVisitCursorMatchesActualRunAt
      machine input hb cursor (timeGroupsLength beforeGroups) := by
    simpa [hfinalStart] using hmatches
  have hcursorTime : cursor.time.val = timeGroupsLength beforeGroups :=
    hmatchesLast.1
  have hcursorBlock : cursor.block =
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength beforeGroups) := hmatchesLast.2.2.2.2
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
  have hterminalVisitActual : terminalVisit =
      actualTimedAlphaScheduledVisitForGroup
        machine input T b hb beforeGroups [] lastGroup hgroupSplit := by
    simpa [terminalVisit, terminalToken] using
      (timedAlphaScheduledVisitAtCrossing_eq_actualLastGroup
        machine input T b hb cursor beforeGroups lastGroup hsplit
          entry hentry hgroupStop (by omega) hfoldTime hmatchesLast)
  have hallActual : ActualTimedAlphaScheduledVisitsFromGroups
      machine input T b hb []
      (actualCanonicalWorkBlockRuns machine input T b hb)
      (visitsSoFar ++ [terminalVisit]) := by
    have hcompleted :=
      ActualProperTimedAlphaScheduledVisitsFromGroups.complete_with_last
        machine input T b hb []
          (actualCanonicalWorkBlockRuns machine input T b hb) visitsSoFar
          hproperSchedule beforeGroups lastGroup hsplit (by simpa using hsplit)
    rw [hterminalVisitActual]
    simpa using hcompleted
  refine ⟨visitsSoFar ++ [terminalVisit], ?_, hallActual⟩
  refine ⟨chronologicalTimedCanonicalAlpha_word_syntacticallyValid
      machine input T b hb, terminalCursor, visitsSoFar ++ [terminalVisit],
    ?_, hfinish, hchained⟩
  rw [decode_chronologicalTimedCanonicalAlpha_word,
    chronologicalTimedTokens_eq_proper_append_terminal
      machine input T b hb entry hentry htime]
  exact hfold

/-- Schedule completeness with the exact all-group relation when no crossing
token occurs on the last transition.  This includes the `T = 0` empty schedule
and the positive final-visit convention. -/
theorem exists_actualTimedAlphaVisitScheduleValid_with_groups_of_no_terminal
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (hterminal : ∀ entry,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb →
        entry.time.val + 1 ≠ T) :
    ∃ visits,
      TimedAlphaVisitScheduleValid machine
          (chronologicalTimedCanonicalAlpha machine input T b hb) visits ∧
        ActualTimedAlphaScheduledVisitsFromGroups machine input T b hb []
          (actualCanonicalWorkBlockRuns machine input T b hb) visits := by
  obtain ⟨visitsSoFar, cursor, hfold, hmatches, hproperSchedule⟩ :=
    actualProperTimedTokenFold_with_schedule machine input T b hb
  obtain ⟨visits, hfinish⟩ := actualFinalCursor_finish_of_no_terminal
    machine input T b hb cursor visitsSoFar hmatches hterminal
  have hchained := timedAlphaTokenVisitFold_finish_chained hfold hfinish
  have hallActual : ActualTimedAlphaScheduledVisitsFromGroups
      machine input T b hb []
      (actualCanonicalWorkBlockRuns machine input T b hb) visits := by
    cases hfinish with
    | atTerminal hcursorTerminal hendpoint =>
        have hTzero : T = 0 := by
          by_contra hTne
          have hTpos : 0 < T := Nat.pos_of_ne_zero hTne
          obtain ⟨beforeGroups, lastGroup, hsplit, hlastNonempty,
            htotal, hfinalStart⟩ :=
            exists_actualCanonicalLastGroup machine input T b hb hTpos
          have hcursorStart : cursor.time.val =
              timeGroupsLength beforeGroups := hmatches.1.trans hfinalStart
          have hlastPositive : 0 < lastGroup.length :=
            List.length_pos_iff.mpr hlastNonempty
          omega
        subst T
        have hgroups := actualCanonicalWorkBlockRuns_zero
          machine input b hb
        rw [hgroups] at hproperSchedule ⊢
        cases hproperSchedule
        exact ActualTimedAlphaScheduledVisitsFromGroups.nil []
    | finalVisit hfinishTime hterminalHead =>
        have hTpos : 0 < T := by
          have hcursorNonnegative : 0 ≤ cursor.time.val := Nat.zero_le _
          omega
        obtain ⟨beforeGroups, lastGroup, hsplit, hlastNonempty,
          htotal, hfinalStart⟩ :=
          exists_actualCanonicalLastGroup machine input T b hb hTpos
        have hmatchesLast : TimedAlphaVisitCursorMatchesActualRunAt
            machine input hb cursor (timeGroupsLength beforeGroups) := by
          simpa [hfinalStart] using hmatches
        have hfinalActual : timedAlphaFinalScheduledVisit
              (chronologicalTimedCanonicalAlpha machine input T b hb)
              cursor hfinishTime =
            actualTimedAlphaScheduledVisitForGroup
              machine input T b hb beforeGroups [] lastGroup
                (by simpa using hsplit) := by
          exact timedAlphaFinalScheduledVisit_eq_actualLastGroup
            machine input T b hb cursor beforeGroups lastGroup hsplit htotal
              hmatchesLast hfinishTime
        have hcompleted :=
          ActualProperTimedAlphaScheduledVisitsFromGroups.complete_with_last
            machine input T b hb []
              (actualCanonicalWorkBlockRuns machine input T b hb) visitsSoFar
              hproperSchedule beforeGroups lastGroup hsplit
                (by simpa using hsplit)
        rw [hfinalActual]
        simpa using hcompleted
  refine ⟨visits, ?_, hallActual⟩
  refine ⟨chronologicalTimedCanonicalAlpha_word_syntacticallyValid
      machine input T b hb, cursor, visitsSoFar, ?_, hfinish, hchained⟩
  rw [decode_chronologicalTimedCanonicalAlpha_word,
    chronologicalTimedTokens_eq_proper_of_no_terminal
      machine input T b hb hterminal]
  exact hfold

/-- Unconditional actual schedule completeness strengthened by exact
correspondence with every actual maximal group. -/
theorem exists_actualTimedAlphaVisitScheduleValid_with_groups
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    ∃ visits,
      TimedAlphaVisitScheduleValid machine
          (chronologicalTimedCanonicalAlpha machine input T b hb) visits ∧
        ActualTimedAlphaScheduledVisitsFromGroups machine input T b hb []
          (actualCanonicalWorkBlockRuns machine input T b hb) visits := by
  by_cases hterminal : ∃ entry :
      ChronologicalCanonicalCrossingEntry machine.State T b,
      entry ∈ chronologicalCanonicalCrossingEntries machine input T b hb ∧
        entry.time.val + 1 = T
  · obtain ⟨entry, hentry, htime⟩ := hterminal
    exact exists_actualTimedAlphaVisitScheduleValid_with_groups_of_terminal
      machine input T b hb entry hentry htime
  · apply exists_actualTimedAlphaVisitScheduleValid_with_groups_of_no_terminal
    intro entry hentry htime
    exact hterminal ⟨entry, hentry, htime⟩

/-- Stable filtering of an exact all-group scheduled list is precisely the
target fixed-visit scan above. -/
theorem ActualTimedAlphaScheduledVisitsFromGroups.blockVisits_scan
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before groups : List (List (Fin T)))
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hall : ActualTimedAlphaScheduledVisitsFromGroups
      machine input T b hb before groups scheduled)
    (target : Fin (T / b + 1)) :
    ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target
      before groups (timedAlphaBlockVisits target scheduled) := by
  induction hall with
  | nil before =>
      exact ActualFixedAlphaBlockVisitsFromGroups.nil before
  | @cons before group rest hsplit scheduled htail ih =>
      by_cases htarget : actualCanonicalWorkBlockGroupLabel
          machine input T b hb before = target
      · have hfiltered : timedAlphaBlockVisits target
            (actualTimedAlphaScheduledVisitForGroup
                machine input T b hb before rest group hsplit :: scheduled) =
          actualCanonicalWorkBlockGroupVisit
              machine input T b hb before rest group hsplit ::
            timedAlphaBlockVisits target scheduled := by
          simp [timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
            actualTimedAlphaScheduledVisitForGroup, htarget]
        rw [hfiltered]
        exact ActualFixedAlphaBlockVisitsFromGroups.keep
          before group rest hsplit htarget
            (timedAlphaBlockVisits target scheduled) ih
      · have hfiltered : timedAlphaBlockVisits target
            (actualTimedAlphaScheduledVisitForGroup
                machine input T b hb before rest group hsplit :: scheduled) =
            timedAlphaBlockVisits target scheduled := by
          simp [timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
            actualTimedAlphaScheduledVisitForGroup, htarget]
        rw [hfiltered]
        exact ActualFixedAlphaBlockVisitsFromGroups.skip
          before group rest hsplit htarget
            (timedAlphaBlockVisits target scheduled) ih

/-- The relational scan is total on every genuine suffix decomposition. -/
theorem exists_actualFixedAlphaBlockVisitsFromGroups
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before groups : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ groups) :
    exists visits, ActualFixedAlphaBlockVisitsFromGroups
      machine input T b hb target before groups visits := by
  induction groups generalizing before with
  | nil =>
      exact ⟨[], ActualFixedAlphaBlockVisitsFromGroups.nil before⟩
  | cons group rest ih =>
      have hcurrent : actualCanonicalWorkBlockRuns machine input T b hb =
          before ++ group :: rest := by
        simpa using hsplit
      have hnext : actualCanonicalWorkBlockRuns machine input T b hb =
          (before ++ [group]) ++ rest := by
        simpa [List.append_assoc] using hcurrent
      obtain ⟨visits, htail⟩ := ih (before ++ [group]) hnext
      by_cases htarget : actualCanonicalWorkBlockGroupLabel
          machine input T b hb before = target
      · exact ⟨actualCanonicalWorkBlockGroupVisit
            machine input T b hb before rest group hcurrent :: visits,
          ActualFixedAlphaBlockVisitsFromGroups.keep
            before group rest hcurrent htarget visits htail⟩
      · exact ⟨visits,
          ActualFixedAlphaBlockVisitsFromGroups.skip
            before group rest hcurrent htarget visits htail⟩

/-- If the first remaining actual group is not the target, inversion of the
scan exposes the unchanged visit list and the scan of the following suffix. -/
theorem ActualFixedAlphaBlockVisitsFromGroups.tail_of_head_away
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (group : List (Fin T)) (rest : List (List (Fin T)))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hscan : ActualFixedAlphaBlockVisitsFromGroups
      machine input T b hb target before (group :: rest) visits)
    (haway : actualCanonicalWorkBlockGroupLabel
      machine input T b hb before ≠ target) :
    ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target
      (before ++ [group]) rest visits := by
  cases hscan with
  | skip _ _ _ _ _ _ htail => exact htail
  | keep _ _ _ _ htarget _ _ => exact False.elim (haway htarget)

/-- Every retained visit begins no earlier than the start of the scanned
actual suffix. -/
theorem ActualFixedAlphaBlockVisitsFromGroups.entryTime_ge_start
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before groups : List (List (Fin T)))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hscan : ActualFixedAlphaBlockVisitsFromGroups
      machine input T b hb target before groups visits) :
    ∀ visit, visit ∈ visits →
      timeGroupsLength before ≤ visit.entryTime.val := by
  induction hscan with
  | nil before => simp
  | @skip before group rest hsplit haway visits htail ih =>
      intro visit hvisit
      have hbound := ih visit hvisit
      simp only [timeGroupsLength_append, timeGroupsLength_cons,
        timeGroupsLength_nil, Nat.add_zero] at hbound
      omega
  | @keep before group rest hsplit htarget visits htail ih =>
      intro visit hvisit
      simp only [List.mem_cons] at hvisit
      rcases hvisit with rfl | hvisit
      · rw [actualCanonicalWorkBlockGroupVisit_entryTime_val]
      · have hbound := ih visit hvisit
        simp only [timeGroupsLength_append, timeGroupsLength_cons,
          timeGroupsLength_nil, Nat.add_zero] at hbound
        omega

/-- After a retained target group, every later retained target visit starts
strictly after that group's exit.  The strictness comes from maximality: the
immediately following group has a different label and is nonempty. -/
theorem actualFixedAlphaBlockVisits_tail_strict_after_target_group
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (group : List (Fin T)) (rest : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ group :: rest)
    (htarget : actualCanonicalWorkBlockGroupLabel
      machine input T b hb before = target)
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (htail : ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target
      (before ++ [group]) rest visits) :
    ∀ later, later ∈ visits →
      (actualCanonicalWorkBlockGroupVisit
        machine input T b hb before rest group hsplit).exitTime.val <
        later.entryTime.val := by
  intro later hlater
  cases rest with
  | nil =>
      cases htail
      simp at hlater
  | cons next more =>
      have hnextSplit : actualCanonicalWorkBlockRuns machine input T b hb =
          (before ++ [group]) ++ next :: more := by
        simpa [List.append_assoc] using hsplit
      have hnextAway : actualCanonicalWorkBlockGroupLabel
          machine input T b hb (before ++ [group]) ≠ target := by
        intro hnextTarget
        have hchain := actualCanonicalWorkBlockRuns_adjacent_differ
          machine input T b hb
        have hadjacent :=
          (List.chain'_iff_forall_rel_of_append_cons_cons.mp hchain) hsplit
        rcases hadjacent with
          ⟨hgroupNonempty, hnextNonempty, hdifferent⟩
        have hgroupLastLabel := actualCanonicalWorkBlockGroup_label_eq_initial
          machine input T b hb before (next :: more) group hsplit
            (group.getLast hgroupNonempty)
            (List.getLast_mem hgroupNonempty)
        have hnextHeadLabel := actualCanonicalWorkBlockGroup_label_eq_initial
          machine input T b hb (before ++ [group]) more next hnextSplit
            (next.head hnextNonempty) (List.head_mem hnextNonempty)
        apply hdifferent
        exact (hgroupLastLabel.trans htarget).trans
          (hnextHeadLabel.trans hnextTarget).symm
      have hdeeper :=
        ActualFixedAlphaBlockVisitsFromGroups.tail_of_head_away
          machine input T b hb target (before ++ [group]) next more visits
            htail hnextAway
      have hbound :=
        ActualFixedAlphaBlockVisitsFromGroups.entryTime_ge_start
          machine input T b hb target
            ((before ++ [group]) ++ [next]) more visits hdeeper later hlater
      have hnextNonempty := actualCanonicalWorkBlockGroup_nonempty
        machine input T b hb (before ++ [group]) more next hnextSplit
      have hnextPositive : 0 < next.length :=
        List.length_pos_iff.mpr hnextNonempty
      rw [actualCanonicalWorkBlockGroupVisit_exitTime_val]
      simp only [timeGroupsLength_append, timeGroupsLength_cons,
        timeGroupsLength_nil, Nat.add_zero] at hbound
      omega

/-- The complete filtered list of actual target groups has the strict
chronology required by the public fixed-list validator. -/
theorem ActualFixedAlphaBlockVisitsFromGroups.chronological
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before groups : List (List (Fin T)))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hscan : ActualFixedAlphaBlockVisitsFromGroups
      machine input T b hb target before groups visits) :
    FixedAlphaBlockVisitsChronological visits := by
  induction hscan with
  | nil before => simp [FixedAlphaBlockVisitsChronological]
  | @skip before group rest hsplit haway visits htail ih =>
      exact ih
  | @keep before group rest hsplit htarget visits htail ih =>
      unfold FixedAlphaBlockVisitsChronological at ih ⊢
      rw [List.pairwise_cons]
      exact ⟨actualFixedAlphaBlockVisits_tail_strict_after_target_group
        machine input T b hb target before group rest hsplit htarget
          visits htail, ih⟩

/-- Main carried-slab induction.  Starting from the actual target restriction
at the beginning of a suffix, every retained actual visit is accepted and the
deterministic fold ends at the actual target restriction after the suffix.

The end equality is intentionally maintained even when the suffix contains no
target visit: then it is exactly persistence across the discarded groups. -/
theorem actualFixedAlphaBlockVisitsFromGroups_replayAccepted_and_result
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before groups : List (List (Fin T)))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hscan : ActualFixedAlphaBlockVisitsFromGroups
      machine input T b hb target before groups visits) :
    FixedAlphaBlockVisitReplayAccepted machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) target
        (actualFixedAlphaBlockSlabAtTime machine input T b hb target
          (timeGroupsLength before)) visits /\
      replayFixedAlphaBlockVisits machine input
          (chronologicalTimedCanonicalAlpha machine input T b hb) target
          (actualFixedAlphaBlockSlabAtTime machine input T b hb target
            (timeGroupsLength before)) visits =
        actualFixedAlphaBlockSlabAtTime machine input T b hb target
          (timeGroupsLength before + timeGroupsLength groups) := by
  induction hscan with
  | nil before =>
      simp [FixedAlphaBlockVisitReplayAccepted,
        replayFixedAlphaBlockVisits, timeGroupsLength]
  | @skip before group rest hsplit haway visits htail ih =>
      have hpersist := actualFixedAlphaBlockSlabAtTime_eq_after_away_group
        machine input T b hb target before rest group hsplit haway
      have hstart :
          timeGroupsLength (before ++ [group]) =
            timeGroupsLength before + group.length := by
        simp [timeGroupsLength_append]
      have ih' := ih
      rw [hstart, hpersist] at ih'
      constructor
      · exact ih'.1
      · simpa [timeGroupsLength_cons, Nat.add_assoc] using ih'.2
  | @keep before group rest hsplit htarget visits htail ih =>
      let alpha := chronologicalTimedCanonicalAlpha machine input T b hb
      let carried := actualFixedAlphaBlockSlabAtTime
        machine input T b hb target (timeGroupsLength before)
      let visit := actualCanonicalWorkBlockGroupVisit
        machine input T b hb before rest group hsplit
      have hvalid : FixedAlphaBlockVisitValid machine input alpha target
          visit carried := by
        exact actualCanonicalWorkBlockGroupVisit_valid_for_target
          machine input T b hb target before rest group hsplit htarget
      have houtput : fixedAlphaBlockVisitOutputSlab machine input alpha target
            visit carried =
          actualFixedAlphaBlockSlabAtTime machine input T b hb target
            (timeGroupsLength before + group.length) := by
        exact actualCanonicalWorkBlockGroupVisit_outputSlab_for_target
          machine input T b hb target before rest group hsplit htarget
      have hstart :
          timeGroupsLength (before ++ [group]) =
            timeGroupsLength before + group.length := by
        simp [timeGroupsLength_append]
      have ih' := ih
      rw [hstart, ← houtput] at ih'
      constructor
      · exact ⟨hvalid, ih'.1⟩
      · simpa [replayFixedAlphaBlockVisits, timeGroupsLength_cons,
          Nat.add_assoc, alpha, carried, visit] using ih'.2

/-- Public list-acceptance form of the arbitrary-return induction. -/
theorem ActualFixedAlphaBlockVisitsFromGroups.listAccepted
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before groups : List (List (Fin T)))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hscan : ActualFixedAlphaBlockVisitsFromGroups
      machine input T b hb target before groups visits) :
    FixedAlphaBlockVisitListAccepted machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb) target
      (actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before)) visits := by
  constructor
  · exact hscan.chronological machine input T b hb target
  · exact (actualFixedAlphaBlockVisitsFromGroups_replayAccepted_and_result
      machine input T b hb target before groups visits hscan).1

/-- Arbitrarily many actual visits to a target block are replay-accepted from
the literal blank slab.  No first-visit or consecutive-pair premise is exposed:
the scan itself proves blank persistence before the first target group and
carried-slab persistence between all later returns. -/
theorem exists_allActualFixedAlphaBlockVisits_replayAcceptedFromBlank
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1)) :
    exists visits : List (FixedAlphaBlockVisit machine.State T),
      ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target []
          (actualCanonicalWorkBlockRuns machine input T b hb) visits /\
      FixedAlphaBlockVisitReplayAccepted machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) target
        (blankWorkSlab
          (advertisedBlockWidth
            (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
            target)) visits /\
      replayFixedAlphaBlockVisits machine input
          (chronologicalTimedCanonicalAlpha machine input T b hb) target
          (blankWorkSlab
            (advertisedBlockWidth
              (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
              target)) visits =
        actualFixedAlphaBlockSlabAtTime machine input T b hb target T := by
  obtain ⟨visits, hscan⟩ := exists_actualFixedAlphaBlockVisitsFromGroups
    machine input T b hb target []
      (actualCanonicalWorkBlockRuns machine input T b hb) (by simp)
  have hmain := actualFixedAlphaBlockVisitsFromGroups_replayAccepted_and_result
    machine input T b hb target []
      (actualCanonicalWorkBlockRuns machine input T b hb) visits hscan
  have htotal := timeGroupsLength_actualCanonicalWorkBlockRuns_eq
    machine input T b hb
  refine ⟨visits, hscan, ?_, ?_⟩
  · simpa using hmain.1
  · simpa [htotal] using hmain.2

/-- Complete public interface for the actual filtered target list: it starts
from one literal blank slab, is strictly chronological, accepts every local
replay with the preceding output as the sole carried state, and folds to the
exact actual target slab at time `T`. -/
theorem exists_allActualFixedAlphaBlockVisits_listAcceptedFromBlank
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1)) :
    ∃ visits : List (FixedAlphaBlockVisit machine.State T),
      ActualFixedAlphaBlockVisitsFromGroups machine input T b hb target []
          (actualCanonicalWorkBlockRuns machine input T b hb) visits ∧
      FixedAlphaBlockVisitListAcceptedFromBlank machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) target visits ∧
      replayFixedAlphaBlockVisits machine input
          (chronologicalTimedCanonicalAlpha machine input T b hb) target
          (blankWorkSlab
            (advertisedBlockWidth
              (chronologicalTimedCanonicalAlpha machine input T b hb).offsets
              target)) visits =
        actualFixedAlphaBlockSlabAtTime machine input T b hb target T := by
  obtain ⟨visits, hscan, hreplay, hresult⟩ :=
    exists_allActualFixedAlphaBlockVisits_replayAcceptedFromBlank
      machine input T b hb target
  refine ⟨visits, hscan, ?_, hresult⟩
  unfold FixedAlphaBlockVisitListAcceptedFromBlank
  exact ⟨hscan.chronological machine input T b hb target, hreplay⟩

/-- Final actual-completeness interface for the fixed-block replay layer.

One actual timed-alpha schedule works simultaneously for every target block.
Stable filtering by `timedAlphaBlockVisits` gives exactly all actual visits to
that target; the public fixed-list validator accepts the result from one blank
slab, and its deterministic fold ends at the exact actual target restriction
at time `T`. -/
theorem exists_actualTimedAlphaVisitScheduleValid_allBlockVisitsAccepted
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    ∃ scheduled : List (TimedAlphaScheduledVisit machine.State T b),
      TimedAlphaVisitScheduleValid machine
          (chronologicalTimedCanonicalAlpha machine input T b hb) scheduled ∧
        ActualTimedAlphaScheduledVisitsFromGroups machine input T b hb []
          (actualCanonicalWorkBlockRuns machine input T b hb) scheduled ∧
        ∀ target : Fin (T / b + 1),
          FixedAlphaBlockVisitListAcceptedFromBlank machine input
              (chronologicalTimedCanonicalAlpha machine input T b hb) target
              (timedAlphaBlockVisits target scheduled) ∧
            replayFixedAlphaBlockVisits machine input
                (chronologicalTimedCanonicalAlpha machine input T b hb) target
                (blankWorkSlab
                  (advertisedBlockWidth
                    (chronologicalTimedCanonicalAlpha
                      machine input T b hb).offsets target))
                (timedAlphaBlockVisits target scheduled) =
              actualFixedAlphaBlockSlabAtTime
                machine input T b hb target T := by
  obtain ⟨scheduled, hvalid, hall⟩ :=
    exists_actualTimedAlphaVisitScheduleValid_with_groups
      machine input T b hb
  refine ⟨scheduled, hvalid, hall, ?_⟩
  intro target
  have hscan :=
    ActualTimedAlphaScheduledVisitsFromGroups.blockVisits_scan
      machine input T b hb []
        (actualCanonicalWorkBlockRuns machine input T b hb) scheduled hall target
  have haccepted := hscan.listAccepted machine input T b hb target
  have hresult :=
    (actualFixedAlphaBlockVisitsFromGroups_replayAccepted_and_result
      machine input T b hb target []
        (actualCanonicalWorkBlockRuns machine input T b hb)
        (timedAlphaBlockVisits target scheduled) hscan).2
  have htotal := timeGroupsLength_actualCanonicalWorkBlockRuns_eq
    machine input T b hb
  constructor
  · unfold FixedAlphaBlockVisitListAcceptedFromBlank
    simpa using haccepted
  · simpa [htotal] using hresult

end OneTapeMagnification
end Frontier
end Pnp4
