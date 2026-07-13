import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaGlobalGlue
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaCutCounterReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Executable timed-alpha canonicality

This file combines executable visit replay with exact advertised-cut
minimality.  The first lemmas expose the missing converse direction needed
for canonicality: an accepted local visit stays in its advertised block on
the actual global run.  Once the advertised offsets are the actual canonical
offsets, this is an exact statement about `actualCanonicalWorkBlockAtTime`.
-/

/-- Membership of an actual run head in an advertised slab identifies its
canonical block once the advertised offsets have been checked canonical. -/
theorem actualCanonicalWorkBlockAtTime_eq_of_advertisedSlab
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hoffsets : alpha.offsets = canonicalCutOffsets machine input T b hb)
    (time : Nat) (htime : time <= T)
    (block : Fin (T / b + 1))
    (hslab : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      (run machine input time).workHead) :
    actualCanonicalWorkBlockAtTime machine input T b hb time = block := by
  have hhead : (run machine input time).workHead <= time := by
    simpa [workHeadTrajectory, workHeadTrajectoryFrom, run] using
      (workHeadTrajectory_le_time machine input time)
  let cell : Fin (T + 1) :=
    ⟨(run machine input time).workHead, by
      exact Nat.lt_succ_of_le
        (hhead.trans htime)⟩
  apply (workBlockAt_eq_iff_workCellInCanonicalSlab hb
    (actualWorkBoundaryCounts machine input T) cell block).2
  simpa [actualCanonicalWorkBlockAtTime, canonicalWorkBlockAtTime,
    workHeadTrajectory, cell, hoffsets] using hslab

/-- The local pre-transition confinement check transfers to every concrete
entry whose finite endpoint and carried slab agree with the advertisement. -/
theorem fixedAlphaAcceptedVisit_concreteInside
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (scheduled : TimedAlphaScheduledVisit machine.State T b)
    (config : Configuration machine.State)
    (hvalid : FixedAlphaBlockVisitValid machine input alpha scheduled.block
      scheduled.visit (store scheduled.block))
    (hentry : ConfigurationMatchesFixedAlphaEndpoint
      scheduled.visit.entry config)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target)
    (time : Nat) (htime : time < scheduled.visit.steps) :
    WorkCellInSlab
      (advertisedBlockLower alpha.offsets scheduled.block)
      (advertisedBlockWidth alpha.offsets scheduled.block)
      (runFrom machine input config time).workHead := by
  let base := advertisedBlockLower alpha.offsets scheduled.block
  let width := advertisedBlockWidth alpha.offsets scheduled.block
  let localEntry := fixedAlphaBlockVisitEntryConfiguration
    alpha scheduled.block scheduled.visit (store scheduled.block)
  have hsameEntry : SameOnWorkSlab base width localEntry config := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [localEntry, base, width] using hentry.1
    · simpa [localEntry, base, width] using hentry.2.1
    · simpa [localEntry, base, width] using hentry.2.2
    · calc
        restrictWorkSlab base width localEntry.workTape =
            store scheduled.block := by
          simp [localEntry, base, width,
            fixedAlphaBlockVisitEntryConfiguration]
        _ = restrictWorkSlab base width config.workTape := by
          simpa [base, width] using (hstore scheduled.block).symm
  have hsameAt := runFrom_sameOnWorkSlab_same_input (steps := time)
    machine input hsameEntry (fun earlier hearlier =>
      hvalid.1 ⟨earlier, by omega⟩)
  have hinsideLocal := hvalid.1 ⟨time, htime⟩
  rw [← hsameAt.2.2.1]
  exact hinsideLocal

private theorem crossingRecordPayload_eq_of_fields
    {State : Type} {T : Nat}
    (left right : CrossingRecordPayload State T)
    (hdirection : left.direction = right.direction)
    (hstate : left.postState = right.postState)
    (hinput : left.postInputHead = right.postInputHead) :
    left = right := by
  cases left
  cases right
  simp_all

/-- A timed token whose source/destination labels and post endpoint agree
with one actual chronological crossing is exactly the extracted token. -/
theorem timedCanonicalCrossingToken_eq_actualEntry_of_blocks_endpoint
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (crossing : TimedCanonicalCrossingToken machine.State T b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb)
    (htime : crossing.sourceTime = entry.time)
    (hsource : actualCanonicalWorkBlockAtTime machine input T b hb
        crossing.sourceTime.val =
      advertisedTimedCrossingSourceBlock crossing)
    (hdestination : actualCanonicalWorkBlockAtTime machine input T b hb
        (crossing.sourceTime.val + 1) =
      advertisedTimedCrossingDestinationBlock crossing)
    (hpost : ConfigurationMatchesFixedAlphaEndpoint
      (advertisedTimedCrossingPostEndpoint alpha crossing)
      (run machine input (crossing.sourceTime.val + 1))) :
    crossing = timedCanonicalCrossingTokenOfEntry entry := by
  let crossings := actualWorkBoundaryCounts machine input T
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  have hsource' :
      workBlockAt hb crossings
          (run machine input crossing.sourceTime.val).workHead =
        advertisedTimedCrossingSourceBlock crossing := by
    simpa [actualCanonicalWorkBlockAtTime, canonicalWorkBlockAtTime,
      workHeadTrajectory, workHeadTrajectoryFrom, run, crossings] using hsource
  have hdestination' :
      workBlockAt hb crossings
          (run machine input (crossing.sourceTime.val + 1)).workHead =
        advertisedTimedCrossingDestinationBlock crossing := by
    simpa [actualCanonicalWorkBlockAtTime, canonicalWorkBlockAtTime,
      workHeadTrajectory, workHeadTrajectoryFrom, run, crossings] using
        hdestination
  have hentryBlocksLeft
      (hdirection : entry.record.payload.direction = .leftToRight) :
      workBlockAt hb crossings
          (run machine input crossing.sourceTime.val).workHead =
            Fin.castSucc entry.record.selectedCut ∧
        workBlockAt hb crossings
          (run machine input (crossing.sourceTime.val + 1)).workHead =
            Fin.succ entry.record.selectedCut := by
    have hheads := hdata.2.2.2.2.1.mp hdirection
    constructor
    · rw [htime, hheads.1, hdata.1]
      exact workBlockAt_canonicalBoundary hb crossings entry.record.selectedCut
    · rw [htime, hheads.2, hdata.1]
      exact workBlockAt_canonicalBoundary_succ hb crossings
        entry.record.selectedCut
  have hentryBlocksRight
      (hdirection : entry.record.payload.direction = .rightToLeft) :
      workBlockAt hb crossings
          (run machine input crossing.sourceTime.val).workHead =
            Fin.succ entry.record.selectedCut ∧
        workBlockAt hb crossings
          (run machine input (crossing.sourceTime.val + 1)).workHead =
            Fin.castSucc entry.record.selectedCut := by
    have hheads := hdata.2.2.2.2.2.mp hdirection
    constructor
    · rw [htime, hheads.1, hdata.1]
      exact workBlockAt_canonicalBoundary_succ hb crossings
        entry.record.selectedCut
    · rw [htime, hheads.2, hdata.1]
      exact workBlockAt_canonicalBoundary hb crossings entry.record.selectedCut
  have hbucket : crossing.token.1 = entry.record.selectedCut := by
    cases hcrossingDirection : crossing.token.2.direction <;>
      cases hentryDirection : entry.record.payload.direction
    · have hblocks := hentryBlocksLeft hentryDirection
      apply Fin.ext
      have hs := congrArg Fin.val (hblocks.1.symm.trans hsource')
      simpa [advertisedTimedCrossingSourceBlock,
        hcrossingDirection] using hs.symm
    · have hblocks := hentryBlocksRight hentryDirection
      have hs := congrArg Fin.val (hblocks.1.symm.trans hsource')
      have hd := congrArg Fin.val (hblocks.2.symm.trans hdestination')
      simp [advertisedTimedCrossingSourceBlock,
        advertisedTimedCrossingDestinationBlock,
        hcrossingDirection] at hs hd
      omega
    · have hblocks := hentryBlocksLeft hentryDirection
      have hs := congrArg Fin.val (hblocks.1.symm.trans hsource')
      have hd := congrArg Fin.val (hblocks.2.symm.trans hdestination')
      simp [advertisedTimedCrossingSourceBlock,
        advertisedTimedCrossingDestinationBlock,
        hcrossingDirection] at hs hd
      omega
    · have hblocks := hentryBlocksRight hentryDirection
      apply Fin.ext
      have hs := congrArg Fin.val (hblocks.1.symm.trans hsource')
      simpa [advertisedTimedCrossingSourceBlock,
        hcrossingDirection] using hs.symm
  have hdirection :
      crossing.token.2.direction = entry.record.payload.direction := by
    cases hcrossingDirection : crossing.token.2.direction <;>
      cases hentryDirection : entry.record.payload.direction
    · rfl
    · have hblocks := hentryBlocksRight hentryDirection
      have hs := congrArg Fin.val (hblocks.1.symm.trans hsource')
      have hd := congrArg Fin.val (hblocks.2.symm.trans hdestination')
      simp [advertisedTimedCrossingSourceBlock,
        advertisedTimedCrossingDestinationBlock,
        hcrossingDirection] at hs hd
      omega
    · have hblocks := hentryBlocksLeft hentryDirection
      have hs := congrArg Fin.val (hblocks.1.symm.trans hsource')
      have hd := congrArg Fin.val (hblocks.2.symm.trans hdestination')
      simp [advertisedTimedCrossingSourceBlock,
        advertisedTimedCrossingDestinationBlock,
        hcrossingDirection] at hs hd
      omega
    · rfl
  apply (timedCanonicalCrossingTokenEquiv machine.State T b).injective
  apply Prod.ext
  · exact htime
  · apply Prod.ext
    · exact hbucket
    · change crossing.token.2 = entry.record.payload
      apply crossingRecordPayload_eq_of_fields
      · exact hdirection
      · exact hpost.1.trans (by
          simpa [htime] using hdata.2.2.1.symm)
      · apply Fin.ext
        exact hpost.2.1.trans (by
          simpa [htime] using hdata.2.2.2.1.symm)

/-- Every token in a fold occurs no earlier than the fold's initial cursor. -/
theorem TimedAlphaTokenVisitFold.sourceTime_ge
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {cursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    {finalCursor : TimedAlphaVisitCursor State T b}
    (hfold : TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor) :
    ∀ crossing ∈ tokens, cursor.time.val <= crossing.sourceTime.val := by
  induction hfold with
  | nil cursor => simp
  | @cons cursor crossing rest visits finalCursor htime hsource htail ih =>
      intro candidate hcandidate
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | htailMem
      · exact htime
      · have htailLower := ih candidate htailMem
        change crossing.sourceTime.val + 1 <= candidate.sourceTime.val at htailLower
        omega

theorem TimedAlphaTokenVisitFold.cursor_time_le_finalCursor
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {cursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    {finalCursor : TimedAlphaVisitCursor State T b}
    (hfold : TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor) :
    cursor.time.val <= finalCursor.time.val := by
  induction hfold with
  | nil cursor => exact Nat.le_refl _
  | @cons cursor crossing rest visits finalCursor htime hsource htail ih =>
      change crossing.sourceTime.val + 1 <= finalCursor.time.val at ih
      omega

theorem TimedAlphaTokenVisitFold.sourceTime_lt_finalCursor
    {State : Type} {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha State T b}
    {cursor : TimedAlphaVisitCursor State T b}
    {tokens : List (TimedCanonicalCrossingToken State T b)}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    {finalCursor : TimedAlphaVisitCursor State T b}
    (hfold : TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor) :
    ∀ crossing ∈ tokens,
      crossing.sourceTime.val < finalCursor.time.val := by
  induction hfold with
  | nil cursor => simp
  | @cons cursor crossing rest visits finalCursor htime hsource htail ih =>
      intro candidate hcandidate
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | htailMem
      · have hfinal := htail.cursor_time_le_finalCursor
        change candidate.sourceTime.val + 1 <= finalCursor.time.val at hfinal
        omega
      · exact ih candidate htailMem

/-- An accepted token fold enumerates exactly the actual selected-boundary
crossings between its initial and final cursors, and every advertised token
is the corresponding actual chronological token. -/
theorem TimedAlphaTokenVisitFold.actualCrossingsExactly
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hoffsets : alpha.offsets = canonicalCutOffsets machine input T b hb)
    {cursor : TimedAlphaVisitCursor machine.State T b}
    {tokens : List (TimedCanonicalCrossingToken machine.State T b)}
    {visits : List (TimedAlphaScheduledVisit machine.State T b)}
    {finalCursor : TimedAlphaVisitCursor machine.State T b}
    (hfold : TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor)
    (store : FixedAlphaSlabStore alpha)
    (config : Configuration machine.State)
    (suffix : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllScheduledVisitsReplayAccepted machine input alpha store
      (visits ++ suffix))
    (hcursor : ConfigurationMatchesFixedAlphaEndpoint cursor.endpoint config)
    (hconfig : config = run machine input cursor.time.val)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target) :
    (∀ time, cursor.time.val <= time -> time < finalCursor.time.val ->
      ((∃ boundary : Fin (T / b),
          WorkBoundaryCrossingAt machine input time
            (canonicalBoundary hb
              (actualWorkBoundaryCounts machine input T) boundary).val) ↔
        ∃ crossing ∈ tokens, crossing.sourceTime.val = time)) ∧
      ∀ crossing ∈ tokens,
        ∃ entry ∈ chronologicalCanonicalCrossingEntries
            machine input T b hb,
          crossing = timedCanonicalCrossingTokenOfEntry entry := by
  induction hfold generalizing store config suffix with
  | nil cursor =>
      constructor
      · intro time hlower hupper
        omega
      · simp
  | @cons cursor crossing rest visits finalCursor htime hsource htail ih =>
      let emitted := timedAlphaScheduledVisitAtCrossing
        alpha cursor crossing htime
      change
        FixedAlphaBlockVisitValid machine input alpha emitted.block
            emitted.visit (store emitted.block) ∧
          AllScheduledVisitsReplayAccepted machine input alpha
            (updateFixedAlphaSlabStore machine input alpha store emitted)
            (visits ++ suffix) at haccepted
      have hemittedEntry : ConfigurationMatchesFixedAlphaEndpoint
          emitted.visit.entry config := by
        simpa [emitted, timedAlphaScheduledVisitAtCrossing] using hcursor
      have hemittedTime :
          cursor.time.val + emitted.visit.steps =
            crossing.sourceTime.val + 1 := by
        simpa [emitted, timedAlphaScheduledVisitAtCrossing] using
          emitted.visit.entryTime_add_steps
      have hnextConfigEq :
          runFrom machine input config emitted.visit.steps =
            run machine input (crossing.sourceTime.val + 1) := by
        rw [hconfig]
        calc
          runFrom machine input (run machine input cursor.time.val)
              emitted.visit.steps =
              runFrom machine input (initialConfiguration machine)
                (cursor.time.val + emitted.visit.steps) := by
            simpa [run] using
              (runFrom_add_eq_runFrom_runFrom machine input
                (initialConfiguration machine) cursor.time.val
                emitted.visit.steps).symm
          _ = run machine input (crossing.sourceTime.val + 1) := by
            simp [run, hemittedTime]
      have hinsideAbsolute : ∀ time,
          cursor.time.val <= time ->
          time < crossing.sourceTime.val + 1 ->
          WorkCellInSlab
            (advertisedBlockLower alpha.offsets cursor.block)
            (advertisedBlockWidth alpha.offsets cursor.block)
            (run machine input time).workHead := by
        intro time hlower hupper
        let relative := time - cursor.time.val
        have hrelative : relative < emitted.visit.steps := by
          dsimp [relative]
          omega
        have hinside := fixedAlphaAcceptedVisit_concreteInside
          machine input alpha store emitted config haccepted.1
          hemittedEntry hstore relative hrelative
        have hrun : runFrom machine input config relative =
            run machine input time := by
          rw [hconfig]
          calc
            runFrom machine input (run machine input cursor.time.val) relative =
                runFrom machine input (initialConfiguration machine)
                  (cursor.time.val + relative) := by
              simpa [run] using
                (runFrom_add_eq_runFrom_runFrom machine input
                  (initialConfiguration machine) cursor.time.val relative).symm
            _ = run machine input time := by
              have hadd : cursor.time.val + relative = time := by
                dsimp [relative]
                omega
              simp [run, hadd]
        simpa [emitted, timedAlphaScheduledVisitAtCrossing, hrun] using hinside
      have hlabelInside : ∀ time,
          cursor.time.val <= time ->
          time < crossing.sourceTime.val + 1 ->
          actualCanonicalWorkBlockAtTime machine input T b hb time =
            cursor.block := by
        intro time hlower hupper
        apply actualCanonicalWorkBlockAtTime_eq_of_advertisedSlab
          machine input T b hb alpha hoffsets time (by omega) cursor.block
        exact hinsideAbsolute time hlower hupper
      have hone := fixedAlphaAcceptedVisit_globalStep
        machine input alpha store emitted config haccepted.1
          hemittedEntry hstore
      have hsourceLabel :
          actualCanonicalWorkBlockAtTime machine input T b hb
              crossing.sourceTime.val =
            advertisedTimedCrossingSourceBlock crossing := by
        exact (hlabelInside crossing.sourceTime.val htime (by omega)).trans hsource
      have hpostHeadEq :
          (advertisedTimedCrossingPostWorkHead alpha crossing).val =
            (run machine input (crossing.sourceTime.val + 1)).workHead := by
        have hhead := hone.1.2.2
        rw [hnextConfigEq] at hhead
        simpa [emitted, timedAlphaScheduledVisitAtCrossing] using hhead
      have hpostSlab : WorkCellInSlab
          (advertisedBlockLower alpha.offsets
            (advertisedTimedCrossingDestinationBlock crossing))
          (advertisedBlockWidth alpha.offsets
            (advertisedTimedCrossingDestinationBlock crossing))
          (run machine input (crossing.sourceTime.val + 1)).workHead := by
        rw [← hpostHeadEq]
        exact advertisedTimedCrossing_postWorkHead_in_destinationSlab
          alpha crossing
      have hdestinationLabel :
          actualCanonicalWorkBlockAtTime machine input T b hb
              (crossing.sourceTime.val + 1) =
            advertisedTimedCrossingDestinationBlock crossing := by
        apply actualCanonicalWorkBlockAtTime_eq_of_advertisedSlab
          machine input T b hb alpha hoffsets
          (crossing.sourceTime.val + 1) (by omega)
          (advertisedTimedCrossingDestinationBlock crossing)
        exact hpostSlab
      have hcrossingExists : ∃ boundary : Fin (T / b),
          WorkBoundaryCrossingAt machine input crossing.sourceTime.val
            (canonicalBoundary hb
              (actualWorkBoundaryCounts machine input T) boundary).val := by
        apply (actualCanonicalWorkBlockAtTime_change_iff_selectedCrossing
          machine input T b hb crossing.sourceTime.val).1
        rw [hsourceLabel, hdestinationLabel]
        exact advertisedTimedCrossing_sourceBlock_ne_destinationBlock crossing
      have htimeMem : crossing.sourceTime ∈
          actualSelectedBoundaryCrossingTimes machine input T b hb :=
        (mem_actualSelectedBoundaryCrossingTimes_iff
          machine input T b hb crossing.sourceTime).2 hcrossingExists
      have hentryTimeMem : crossing.sourceTime ∈
          (chronologicalCanonicalCrossingEntries machine input T b hb).map
            ChronologicalCanonicalCrossingEntry.time := by
        rw [map_time_chronologicalCanonicalCrossingEntries]
        exact htimeMem
      obtain ⟨entry, hentry, hentryTime⟩ := List.mem_map.mp hentryTimeMem
      have hpostMatch : ConfigurationMatchesFixedAlphaEndpoint
          (advertisedTimedCrossingPostEndpoint alpha crossing)
          (run machine input (crossing.sourceTime.val + 1)) := by
        have hmatch := hone.1
        rw [hnextConfigEq] at hmatch
        simpa [emitted, timedAlphaScheduledVisitAtCrossing] using hmatch
      have hcrossingToken :
          crossing = timedCanonicalCrossingTokenOfEntry entry := by
        apply timedCanonicalCrossingToken_eq_actualEntry_of_blocks_endpoint
          machine input T b hb alpha crossing entry hentry hentryTime.symm
          hsourceLabel hdestinationLabel hpostMatch
      have hnextCursor : ConfigurationMatchesFixedAlphaEndpoint
          (timedAlphaVisitCursorAfterCrossing alpha crossing).endpoint
          (runFrom machine input config emitted.visit.steps) := by
        simpa [emitted, timedAlphaScheduledVisitAtCrossing,
          timedAlphaVisitCursorAfterCrossing] using hone.1
      have hrec := ih
        (store := updateFixedAlphaSlabStore machine input alpha store emitted)
        (config := runFrom machine input config emitted.visit.steps)
        (suffix := suffix) haccepted.2 hnextCursor hnextConfigEq hone.2
      constructor
      · intro time hlower hupper
        by_cases hbefore : time < crossing.sourceTime.val + 1
        · have htimeLe : time <= crossing.sourceTime.val := by omega
          by_cases heq : time = crossing.sourceTime.val
          · subst time
            constructor
            · intro _
              exact ⟨crossing, by simp⟩
            · intro _
              exact hcrossingExists
          · have hstrict : time < crossing.sourceTime.val := by omega
            have hnoCross : ¬ ∃ boundary : Fin (T / b),
                WorkBoundaryCrossingAt machine input time
                  (canonicalBoundary hb
                    (actualWorkBoundaryCounts machine input T) boundary).val := by
              intro hcross
              have hchange :=
                (actualCanonicalWorkBlockAtTime_change_iff_selectedCrossing
                  machine input T b hb time).2 hcross
              apply hchange
              exact (hlabelInside time hlower (by omega)).trans
                (hlabelInside (time + 1) (by omega) (by omega)).symm
            constructor
            · intro hcross
              exact False.elim (hnoCross hcross)
            · rintro ⟨candidate, hcandidate, hcandidateTime⟩
              simp only [List.mem_cons] at hcandidate
              rcases hcandidate with rfl | htailMem
              · omega
              · have hlowerTail := htail.sourceTime_ge candidate htailMem
                change crossing.sourceTime.val + 1 <=
                  candidate.sourceTime.val at hlowerTail
                omega
        · have hafter : crossing.sourceTime.val + 1 <= time := by omega
          have htailIff := hrec.1 time hafter hupper
          constructor
          · intro hcross
            obtain ⟨candidate, hcandidate, hcandidateTime⟩ :=
              htailIff.mp hcross
            exact ⟨candidate, by simp [hcandidate], hcandidateTime⟩
          · rintro ⟨candidate, hcandidate, hcandidateTime⟩
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | htailMem
            · omega
            · exact htailIff.mpr
                ⟨candidate, htailMem, hcandidateTime⟩
      · intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | htailMem
        · exact ⟨entry, hentry, hcrossingToken⟩
        · exact hrec.2 candidate htailMem

/-- The same accepted-fold induction exposes the exact global configuration
and slab store at the returned cursor, while leaving an arbitrary suffix for
the finish clause. -/
theorem TimedAlphaTokenVisitFold.advanceAccepted
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    {cursor : TimedAlphaVisitCursor machine.State T b}
    {tokens : List (TimedCanonicalCrossingToken machine.State T b)}
    {visits : List (TimedAlphaScheduledVisit machine.State T b)}
    {finalCursor : TimedAlphaVisitCursor machine.State T b}
    (hfold : TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor)
    (store : FixedAlphaSlabStore alpha)
    (config : Configuration machine.State)
    (suffix : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllScheduledVisitsReplayAccepted machine input alpha store
      (visits ++ suffix))
    (hcursor : ConfigurationMatchesFixedAlphaEndpoint cursor.endpoint config)
    (hconfig : config = run machine input cursor.time.val)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target) :
    ∃ finalStore : FixedAlphaSlabStore alpha,
      ∃ finalConfig : Configuration machine.State,
        AllScheduledVisitsReplayAccepted machine input alpha finalStore suffix ∧
          ConfigurationMatchesFixedAlphaEndpoint
            finalCursor.endpoint finalConfig ∧
          finalConfig = run machine input finalCursor.time.val ∧
          ∀ target,
            restrictWorkSlab
                (advertisedBlockLower alpha.offsets target)
                (advertisedBlockWidth alpha.offsets target)
                finalConfig.workTape = finalStore target := by
  induction hfold generalizing store config suffix with
  | nil cursor =>
      exact ⟨store, config, haccepted, hcursor, hconfig, hstore⟩
  | @cons cursor crossing rest visits finalCursor htime hsource htail ih =>
      let emitted := timedAlphaScheduledVisitAtCrossing
        alpha cursor crossing htime
      change
        FixedAlphaBlockVisitValid machine input alpha emitted.block
            emitted.visit (store emitted.block) ∧
          AllScheduledVisitsReplayAccepted machine input alpha
            (updateFixedAlphaSlabStore machine input alpha store emitted)
            (visits ++ suffix) at haccepted
      have hemittedEntry : ConfigurationMatchesFixedAlphaEndpoint
          emitted.visit.entry config := by
        simpa [emitted, timedAlphaScheduledVisitAtCrossing] using hcursor
      have hemittedTime :
          cursor.time.val + emitted.visit.steps =
            crossing.sourceTime.val + 1 := by
        simpa [emitted, timedAlphaScheduledVisitAtCrossing] using
          emitted.visit.entryTime_add_steps
      have hnextConfigEq :
          runFrom machine input config emitted.visit.steps =
            run machine input (crossing.sourceTime.val + 1) := by
        rw [hconfig]
        calc
          runFrom machine input (run machine input cursor.time.val)
              emitted.visit.steps =
              runFrom machine input (initialConfiguration machine)
                (cursor.time.val + emitted.visit.steps) := by
            simpa [run] using
              (runFrom_add_eq_runFrom_runFrom machine input
                (initialConfiguration machine) cursor.time.val
                emitted.visit.steps).symm
          _ = run machine input (crossing.sourceTime.val + 1) := by
            simp [run, hemittedTime]
      have hone := fixedAlphaAcceptedVisit_globalStep
        machine input alpha store emitted config haccepted.1
          hemittedEntry hstore
      have hnextCursor : ConfigurationMatchesFixedAlphaEndpoint
          (timedAlphaVisitCursorAfterCrossing alpha crossing).endpoint
          (runFrom machine input config emitted.visit.steps) := by
        simpa [emitted, timedAlphaScheduledVisitAtCrossing,
          timedAlphaVisitCursorAfterCrossing] using hone.1
      exact ih
        (store := updateFixedAlphaSlabStore machine input alpha store emitted)
        (config := runFrom machine input config emitted.visit.steps)
        (suffix := suffix) haccepted.2 hnextCursor hnextConfigEq hone.2

/-- A sublist of a timed-token list is the whole list when the ordered source
times agree.  Source-time nodup eliminates the only possible ambiguity in a
plain membership subset. -/
theorem timedCanonicalCrossingTokenList_eq_of_sourceTimes_eq_of_subset
    {State : Type} {T b : Nat}
    (left right : List (TimedCanonicalCrossingToken State T b))
    (htimes : left.map TimedCanonicalCrossingToken.sourceTime =
      right.map TimedCanonicalCrossingToken.sourceTime)
    (hrightNodup :
      (right.map TimedCanonicalCrossingToken.sourceTime).Nodup)
    (hsubset : left ⊆ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at htimes
  | cons head tail ih =>
      cases right with
      | nil => simp at htimes
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at htimes
          rw [List.map_cons, List.nodup_cons] at hrightNodup
          have hheadMem : head ∈ other :: rest := hsubset (by simp)
          have hhead : head = other := by
            simp only [List.mem_cons] at hheadMem
            rcases hheadMem with hhead | hheadTail
            · exact hhead
            · exfalso
              apply hrightNodup.1
              have : head.sourceTime ∈
                  rest.map TimedCanonicalCrossingToken.sourceTime :=
                List.mem_map_of_mem hheadTail
              simpa [htimes.1] using this
          subst other
          congr 1
          apply ih rest htimes.2 hrightNodup.2
          intro candidate hcandidate
          have hmem := hsubset (List.mem_cons_of_mem head hcandidate)
          simp only [List.mem_cons] at hmem
          rcases hmem with hsame | hrest
          · exfalso
            apply hrightNodup.1
            have hsourceMem : candidate.sourceTime ∈
                tail.map TimedCanonicalCrossingToken.sourceTime :=
              List.mem_map_of_mem hcandidate
            rw [hsame, htimes.2] at hsourceMem
            exact hsourceMem
          · exact hrest

/-- An accepted positive finish visit contains no selected-boundary crossing.
All of its pre-transition heads are confined to the final cursor block, and
the finish predicate puts the terminal head in that same block. -/
theorem acceptedTimedAlphaFinalVisit_no_selectedCrossing
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hoffsets : alpha.offsets = canonicalCutOffsets machine input T b hb)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (htime : cursor.time.val < T)
    (hterminalHead : WorkCellInSlab
      (advertisedBlockLower alpha.offsets cursor.block)
      (advertisedBlockWidth alpha.offsets cursor.block)
      alpha.terminal.workHead.val)
    (store : FixedAlphaSlabStore alpha)
    (config : Configuration machine.State)
    (hvalid : FixedAlphaBlockVisitValid machine input alpha cursor.block
      (timedAlphaFinalScheduledVisit alpha cursor htime).visit
      (store cursor.block))
    (hcursor : ConfigurationMatchesFixedAlphaEndpoint cursor.endpoint config)
    (hconfig : config = run machine input cursor.time.val)
    (hstore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target) config.workTape =
        store target)
    (time : Nat) (hlower : cursor.time.val <= time) (hupper : time < T) :
    ¬ ∃ boundary : Fin (T / b),
      WorkBoundaryCrossingAt machine input time
        (canonicalBoundary hb
          (actualWorkBoundaryCounts machine input T) boundary).val := by
  let finalVisit := timedAlphaFinalScheduledVisit alpha cursor htime
  have hentry : ConfigurationMatchesFixedAlphaEndpoint
      finalVisit.visit.entry config := by
    simpa [finalVisit, timedAlphaFinalScheduledVisit] using hcursor
  have hvisitTime : cursor.time.val + finalVisit.visit.steps = T := by
    simpa [finalVisit, timedAlphaFinalScheduledVisit] using
      finalVisit.visit.entryTime_add_steps
  have hnextConfigEq :
      runFrom machine input config finalVisit.visit.steps =
        run machine input T := by
    rw [hconfig]
    calc
      runFrom machine input (run machine input cursor.time.val)
          finalVisit.visit.steps =
          runFrom machine input (initialConfiguration machine)
            (cursor.time.val + finalVisit.visit.steps) := by
        simpa [run] using
          (runFrom_add_eq_runFrom_runFrom machine input
            (initialConfiguration machine) cursor.time.val
            finalVisit.visit.steps).symm
      _ = run machine input T := by simp [run, hvisitTime]
  have hone := fixedAlphaAcceptedVisit_globalStep
    machine input alpha store finalVisit config hvalid hentry hstore
  have hinsideAbsolute : ∀ current,
      cursor.time.val <= current -> current < T ->
      WorkCellInSlab
        (advertisedBlockLower alpha.offsets cursor.block)
        (advertisedBlockWidth alpha.offsets cursor.block)
        (run machine input current).workHead := by
    intro current hcurrentLower hcurrentUpper
    let relative := current - cursor.time.val
    have hrelative : relative < finalVisit.visit.steps := by
      dsimp [relative]
      omega
    have hinside := fixedAlphaAcceptedVisit_concreteInside
      machine input alpha store finalVisit config hvalid hentry hstore
      relative hrelative
    have hrun : runFrom machine input config relative =
        run machine input current := by
      rw [hconfig]
      calc
        runFrom machine input (run machine input cursor.time.val) relative =
            runFrom machine input (initialConfiguration machine)
              (cursor.time.val + relative) := by
          simpa [run] using
            (runFrom_add_eq_runFrom_runFrom machine input
              (initialConfiguration machine) cursor.time.val relative).symm
        _ = run machine input current := by
          have hadd : cursor.time.val + relative = current := by
            dsimp [relative]
            omega
          simp [run, hadd]
    simpa [finalVisit, timedAlphaFinalScheduledVisit, hrun] using hinside
  have hlabel : ∀ current,
      cursor.time.val <= current -> current < T ->
      actualCanonicalWorkBlockAtTime machine input T b hb current =
        cursor.block := by
    intro current hcurrentLower hcurrentUpper
    apply actualCanonicalWorkBlockAtTime_eq_of_advertisedSlab
      machine input T b hb alpha hoffsets current (by omega) cursor.block
    exact hinsideAbsolute current hcurrentLower hcurrentUpper
  have hterminalHeadEq : alpha.terminal.workHead.val =
      (run machine input T).workHead := by
    have hhead := hone.1.2.2
    rw [hnextConfigEq] at hhead
    simpa [finalVisit, timedAlphaFinalScheduledVisit] using hhead
  have hterminalLabel :
      actualCanonicalWorkBlockAtTime machine input T b hb T = cursor.block := by
    apply actualCanonicalWorkBlockAtTime_eq_of_advertisedSlab
      machine input T b hb alpha hoffsets T (by omega) cursor.block
    rw [← hterminalHeadEq]
    exact hterminalHead
  intro hcross
  have hchange :=
    (actualCanonicalWorkBlockAtTime_change_iff_selectedCrossing
      machine input T b hb time).2 hcross
  apply hchange
  have hcurrent := hlabel time hlower hupper
  by_cases hnext : time + 1 < T
  · exact hcurrent.trans (hlabel (time + 1) (by omega) hnext).symm
  · have heq : time + 1 = T := by omega
    rw [heq]
    exact hcurrent.trans hterminalLabel.symm

/-- Relational canonicality of the decoded timed word.  Exact local replay,
global interleaving, and canonical offsets leave neither spurious nor omitted
crossing tokens. -/
theorem timedAlphaVisitScheduleValid_allBlockVisitsAccepted_decode_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits)
    (hoffsets : alpha.offsets = canonicalCutOffsets machine input T b hb) :
    decodePaddedWord (T / b) alpha.word =
      chronologicalTimedCanonicalCrossingTokens machine input T b hb := by
  classical
  let tokens := decodePaddedWord (T / b) alpha.word
  let blankStore := blankFixedAlphaSlabStore alpha
  have hsequential : AllScheduledVisitsReplayAccepted machine input alpha
      blankStore visits := by
    exact allScheduledVisitsReplayAccepted_fromBlank_of_allBlockLists
      machine input alpha visits haccepted
  have hinitial : ConfigurationMatchesFixedAlphaEndpoint
      (initialTimedAlphaVisitCursor machine T b).endpoint
      (initialConfiguration machine) := by
    exact ⟨rfl, rfl, rfl⟩
  have hinitialRun : initialConfiguration machine = run machine input 0 := by
    rfl
  have hblankStore : ∀ target,
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets target)
          (advertisedBlockWidth alpha.offsets target)
          (initialConfiguration machine).workTape = blankStore target := by
    intro target
    simp [blankStore, blankFixedAlphaSlabStore, initialConfiguration]
  rcases hschedule with
    ⟨hword, finalCursor, visitsSoFar, hfold, hfinish, hchained⟩
  have hfull :
      (∀ time : Fin T,
        ((∃ boundary : Fin (T / b),
            WorkBoundaryCrossingAt machine input time.val
              (canonicalBoundary hb
                (actualWorkBoundaryCounts machine input T) boundary).val) ↔
          ∃ crossing ∈ tokens,
            crossing.sourceTime.val = time.val)) ∧
        ∀ crossing ∈ tokens,
          ∃ entry ∈ chronologicalCanonicalCrossingEntries
              machine input T b hb,
            crossing = timedCanonicalCrossingTokenOfEntry entry := by
    cases hfinish with
    | atTerminal hterminalTime hterminalEndpoint =>
        have hfoldResult := hfold.actualCrossingsExactly
          machine input hb alpha hoffsets blankStore
          (initialConfiguration machine) [] (by simpa [blankStore] using hsequential)
          hinitial hinitialRun hblankStore
        constructor
        · intro time
          have hresult := hfoldResult.1 time.val (by
            simp [initialTimedAlphaVisitCursor]) (by omega)
          simpa [tokens] using hresult
        · simpa [tokens] using hfoldResult.2
    | finalVisit hfinalTime hterminalHead =>
        let finalVisit := timedAlphaFinalScheduledVisit
          alpha finalCursor hfinalTime
        have hfoldResult := hfold.actualCrossingsExactly
          machine input hb alpha hoffsets blankStore
          (initialConfiguration machine) [finalVisit]
          (by simpa [blankStore, finalVisit] using hsequential)
          hinitial hinitialRun hblankStore
        obtain ⟨finalStore, finalConfig, hfinalAccepted,
            hfinalCursor, hfinalConfig, hfinalStore⟩ :=
          hfold.advanceAccepted machine input alpha blankStore
            (initialConfiguration machine) [finalVisit]
            (by simpa [blankStore, finalVisit] using hsequential)
            hinitial hinitialRun hblankStore
        have hfinalValid : FixedAlphaBlockVisitValid machine input alpha
            finalCursor.block finalVisit.visit
            (finalStore finalCursor.block) := by
          simpa [AllScheduledVisitsReplayAccepted, finalVisit] using
            hfinalAccepted.1
        constructor
        · intro time
          by_cases hbefore : time.val < finalCursor.time.val
          · have hresult := hfoldResult.1 time.val (by
                simp [initialTimedAlphaVisitCursor]) hbefore
            simpa [tokens] using hresult
          · have hnoCross := acceptedTimedAlphaFinalVisit_no_selectedCrossing
              machine input T b hb alpha hoffsets finalCursor hfinalTime
              hterminalHead finalStore finalConfig hfinalValid hfinalCursor
              hfinalConfig hfinalStore time.val (by omega) time.isLt
            constructor
            · intro hcross
              exact False.elim (hnoCross hcross)
            · rintro ⟨crossing, hcrossing, hcrossingTime⟩
              have htokenBefore := hfold.sourceTime_lt_finalCursor
                crossing (by simpa [tokens] using hcrossing)
              omega
        · simpa [tokens] using hfoldResult.2
  have hsourceMem : ∀ time : Fin T,
      time ∈ tokens.map TimedCanonicalCrossingToken.sourceTime ↔
        time ∈ actualSelectedBoundaryCrossingTimes machine input T b hb := by
    intro time
    rw [mem_actualSelectedBoundaryCrossingTimes_iff]
    constructor
    · intro htime
      obtain ⟨crossing, hcrossing, hsource⟩ := List.mem_map.mp htime
      apply (hfull.1 time).2
      exact ⟨crossing, hcrossing, by
        exact congrArg Fin.val hsource⟩
    · intro htime
      obtain ⟨crossing, hcrossing, hsource⟩ := (hfull.1 time).1 htime
      apply List.mem_map.mpr
      refine ⟨crossing, hcrossing, ?_⟩
      exact Fin.ext hsource
  have hsourceTimes :
      tokens.map TimedCanonicalCrossingToken.sourceTime =
        actualSelectedBoundaryCrossingTimes machine input T b hb := by
    exact List.Sorted.eq_of_mem_iff
      (r := fun earlier later : Fin T => earlier < later)
      hword.2
      (actualSelectedBoundaryCrossingTimes_pairwise_lt
        machine input T b hb) hsourceMem
  have hactualSourceTimes :
      (chronologicalTimedCanonicalCrossingTokens machine input T b hb).map
          TimedCanonicalCrossingToken.sourceTime =
        actualSelectedBoundaryCrossingTimes machine input T b hb :=
    map_sourceTime_chronologicalTimedCanonicalCrossingTokens
      machine input T b hb
  have htimes :
      tokens.map TimedCanonicalCrossingToken.sourceTime =
        (chronologicalTimedCanonicalCrossingTokens machine input T b hb).map
          TimedCanonicalCrossingToken.sourceTime :=
    hsourceTimes.trans hactualSourceTimes.symm
  have hrightNodup :
      ((chronologicalTimedCanonicalCrossingTokens machine input T b hb).map
        TimedCanonicalCrossingToken.sourceTime).Nodup := by
    rw [hactualSourceTimes]
    exact actualSelectedBoundaryCrossingTimes_nodup machine input T b hb
  have hsubset : tokens ⊆
      chronologicalTimedCanonicalCrossingTokens machine input T b hb := by
    intro crossing hcrossing
    obtain ⟨entry, hentry, heq⟩ := hfull.2 crossing hcrossing
    rw [heq]
    exact List.mem_map_of_mem hentry
  exact timedCanonicalCrossingTokenList_eq_of_sourceTimes_eq_of_subset
    tokens (chronologicalTimedCanonicalCrossingTokens machine input T b hb)
    htimes hrightNodup hsubset

/-- Executable replay plus exact canonical offsets determines every field of
the ambient alpha, not only its terminal endpoint. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCheck_eq_chronologicalAlpha
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (hoffsets : alpha.offsets = canonicalCutOffsets machine input T b hb) :
    alpha = chronologicalTimedCanonicalAlpha machine input T b hb := by
  have hreflect :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input alpha visits).1 hcheck
  have hdecode :=
    timedAlphaVisitScheduleValid_allBlockVisitsAccepted_decode_eq_actual
      machine input T b hb alpha visits hreflect.1 hreflect.2 hoffsets
  have hdecodeCanonical := decode_chronologicalTimedCanonicalAlpha_word
    machine input T b hb
  have hword : alpha.word =
      (chronologicalTimedCanonicalAlpha machine input T b hb).word := by
    apply timedAlphaWord_eq_of_prefixShaped_of_decode_eq hreflect.1.1.1
      (chronologicalTimedCanonicalAlpha_word_prefixShaped
        machine input T b hb)
    exact hdecode.trans hdecodeCanonical.symm
  have hterminal : alpha.terminal =
      (chronologicalTimedCanonicalAlpha machine input T b hb).terminal := by
    have hglue := timedAlphaVisitScheduleAllBlockVisitsCheck_globalGlue
      machine input alpha visits hcheck
    exact hglue
  apply (ambientTimedCanonicalAlphaEquiv machine.State T b).injective
  apply Prod.ext
  · exact hoffsets
  · apply Prod.ext
    · exact hword
    · exact hterminal

/-- Direct semantic-cut-check corollary. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCheck_cutCheck_eq_chronologicalAlpha
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha visits = true)
    (hcuts : advertisedTimedAlphaCutMinimalityCheck
      machine input alpha = true) :
    alpha = chronologicalTimedCanonicalAlpha machine input T b hb := by
  apply timedAlphaVisitScheduleAllBlockVisitsCheck_eq_chronologicalAlpha
    machine input T b hb alpha visits hschedule
  exact (advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
    machine input T b hb alpha).1 hcuts

/-- **Executable accepted-alpha uniqueness.**  The single combined checkpoint
uses crossing counters accumulated by the same locally replayed schedule; if
it accepts, the advertised alpha is exactly the chronological canonical alpha
of the deterministic blank-start run. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
      machine input alpha visits = true) :
    alpha = chronologicalTimedCanonicalAlpha machine input T b hb := by
  have hreflect :=
    (timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true_iff
      machine input T b hb alpha visits).1 hcheck
  exact timedAlphaVisitScheduleAllBlockVisitsCheck_eq_chronologicalAlpha
    machine input T b hb alpha visits hreflect.1 hreflect.2

/-- Consequently two ambient alphas accepted by the combined checker (with
possibly different exposed schedules) are equal. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_unique
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (left right : AmbientTimedCanonicalAlpha machine.State T b)
    (leftVisits rightVisits :
      List (TimedAlphaScheduledVisit machine.State T b))
    (hleft : timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
      machine input left leftVisits = true)
    (hright : timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
      machine input right rightVisits = true) :
    left = right := by
  rw [timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
      machine input T b hb left leftVisits hleft,
    timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
      machine input T b hb right rightVisits hright]

end OneTapeMagnification
end Frontier
end Pnp4
