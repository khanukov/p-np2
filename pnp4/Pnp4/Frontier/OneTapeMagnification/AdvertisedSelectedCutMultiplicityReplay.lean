import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.SelectedCutMultiplicity

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Selected-cut multiplicity from arbitrary-alpha replay

A valid advertised timed-alpha schedule already fixes the number of crossings
of every advertised selected cut.  This fact is independent of whether the
advertised offsets are canonical leftmost minima.

Every token-emitted visit stays in its source slab until its last transition.
That transition crosses exactly the cut named by the token.  A positive final
visit stays in one advertised slab through its terminal endpoint and therefore
crosses no advertised selected cut.  Summing these local facts along the token
fold identifies the actual selected-cut count with the token multiplicity in
the alpha word, without assuming `alpha.offsets = canonicalCutOffsets ...`.
-/

/-- Two work-head positions in one advertised slab cannot cross any advertised
selected cut. -/
theorem not_crosses_advertisedCut_of_same_slab
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (cut : Fin (T / b))
    (fromHead toHead : Nat)
    (hfrom : WorkCellInSlab
      (advertisedBlockLower offsets block)
      (advertisedBlockWidth offsets block) fromHead)
    (hto : WorkCellInSlab
      (advertisedBlockLower offsets block)
      (advertisedBlockWidth offsets block) toHead) :
    ¬ CrossesWorkBoundary
      (cutDescriptionOfOffsets offsets cut).val fromHead toHead := by
  intro hcross
  have hleft := advertisedPhysicalCut_mem_leftBlockSlab offsets cut
  have hright := advertisedPhysicalCut_succ_mem_rightBlockSlab offsets cut
  rcases hcross with hcross | hcross
  · rcases hcross with ⟨hfromEq, htoEq⟩
    subst fromHead
    subst toHead
    have hblockLeft : block = advertisedCutLeftBlock cut := by
      by_contra hne
      exact advertisedBlockSlabsDisjoint_of_ne offsets block
        (advertisedCutLeftBlock cut) hne _ hfrom hleft
    have hblockRight : block = advertisedCutRightBlock cut := by
      by_contra hne
      exact advertisedBlockSlabsDisjoint_of_ne offsets block
        (advertisedCutRightBlock cut) hne _ hto hright
    have hvals := congrArg Fin.val (hblockLeft.symm.trans hblockRight)
    simp at hvals
  · rcases hcross with ⟨hfromEq, htoEq⟩
    subst fromHead
    subst toHead
    have hblockRight : block = advertisedCutRightBlock cut := by
      by_contra hne
      exact advertisedBlockSlabsDisjoint_of_ne offsets block
        (advertisedCutRightBlock cut) hne _ hfrom hright
    have hblockLeft : block = advertisedCutLeftBlock cut := by
      by_contra hne
      exact advertisedBlockSlabsDisjoint_of_ne offsets block
        (advertisedCutLeftBlock cut) hne _ hto hleft
    have hvals := congrArg Fin.val (hblockRight.symm.trans hblockLeft)
    simp at hvals

/-- A run segment whose configurations all remain in one advertised slab has
zero crossings at every advertised selected cut. -/
theorem streamingWorkBoundaryCrossingCountFrom_eq_zero_of_inside_advertisedSlab
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (cut : Fin (T / b))
    (config : Configuration machine.State) (steps : Nat)
    (hinside : ∀ time, time ≤ steps →
      WorkCellInSlab
        (advertisedBlockLower offsets block)
        (advertisedBlockWidth offsets block)
        (runFrom machine input config time).workHead) :
    streamingWorkBoundaryCrossingCountFrom machine input config steps
      (cutDescriptionOfOffsets offsets cut).val = 0 := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      have hnow := hinside 0 (by omega)
      have hnext := hinside 1 (by omega)
      have hno : ¬ CrossesWorkBoundary
          (cutDescriptionOfOffsets offsets cut).val config.workHead
          (step machine input config).workHead := by
        apply not_crosses_advertisedCut_of_same_slab offsets block cut
        · simpa using hnow
        · simpa [runFrom] using hnext
      have htailInside : ∀ time, time ≤ steps →
          WorkCellInSlab
            (advertisedBlockLower offsets block)
            (advertisedBlockWidth offsets block)
            (runFrom machine input
              (step machine input config) time).workHead := by
        intro time htime
        simpa [runFrom] using hinside (time + 1) (by omega)
      rw [streamingWorkBoundaryCrossingCountFrom, if_neg hno,
        ih (step machine input config) htailInside]

/-- Equality of one token's advertised physical cut with a selected cut is
equivalent to equality of their bucket labels. -/
theorem advertisedTimedCrossingPhysicalCut_eq_fullBucketBoundary_iff
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b)
    (bucket : Fin (T / b)) :
    advertisedTimedCrossingPhysicalCut alpha crossing =
        fullBucketBoundary bucket (alpha.offsets bucket) ↔
      crossing.token.1 = bucket := by
  constructor
  · intro heq
    have hpairs :
        (crossing.token.1, alpha.offsets crossing.token.1) =
          (bucket, alpha.offsets bucket) := by
      exact fullBucketBoundary_injective heq
    exact congrArg Prod.fst hpairs
  · intro heq
    subst bucket
    rfl

/-- The last transition of a valid token-emitted visit crosses exactly the
physical cut advertised by that token. -/
theorem timedAlphaScheduledVisitAtCrossing_last_crosses_advertisedCut
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (crossing : TimedCanonicalCrossingToken machine.State T b)
    (htime : cursor.time.val ≤ crossing.sourceTime.val)
    (hsource : cursor.block = advertisedTimedCrossingSourceBlock crossing)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets cursor.block))
    (hvalid : FixedAlphaBlockVisitValid machine input alpha cursor.block
      (timedAlphaScheduledVisitAtCrossing alpha cursor crossing htime).visit
      carried) :
    let visit := (timedAlphaScheduledVisitAtCrossing
      alpha cursor crossing htime).visit
    let entry := fixedAlphaBlockVisitEntryConfiguration
      alpha cursor.block visit carried
    let lastConfig := runFrom machine input entry (visit.steps - 1)
    CrossesWorkBoundary
      (advertisedTimedCrossingPhysicalCut alpha crossing).val
      lastConfig.workHead (step machine input lastConfig).workHead := by
  dsimp only
  let visit := (timedAlphaScheduledVisitAtCrossing
    alpha cursor crossing htime).visit
  let entry := fixedAlphaBlockVisitEntryConfiguration
    alpha cursor.block visit carried
  let lastConfig := runFrom machine input entry (visit.steps - 1)
  change CrossesWorkBoundary
    (advertisedTimedCrossingPhysicalCut alpha crossing).val
    lastConfig.workHead (step machine input lastConfig).workHead
  have hstepsPos : 0 < visit.steps := FixedAlphaBlockVisit.steps_pos visit
  have hlastLt : visit.steps - 1 < visit.steps := by omega
  have hpreInside : WorkCellInSlab
      (advertisedBlockLower alpha.offsets cursor.block)
      (advertisedBlockWidth alpha.offsets cursor.block)
      lastConfig.workHead := by
    simpa [visit, entry, lastConfig] using hvalid.1 ⟨_, hlastLt⟩
  have hpostAtSteps :
      (runFrom machine input entry visit.steps).workHead =
        (advertisedTimedCrossingPostWorkHead alpha crossing).val := by
    have hexit := hvalid.2.2.2
    symm
    simpa [visit, entry, fixedAlphaBlockVisitRun,
      timedAlphaScheduledVisitAtCrossing,
      advertisedTimedCrossingPostEndpoint] using hexit
  have hsteps : visit.steps - 1 + 1 = visit.steps := by omega
  have hpost : (step machine input lastConfig).workHead =
      (advertisedTimedCrossingPostWorkHead alpha crossing).val := by
    rw [← runFrom_succ_eq_step_runFrom]
    simpa [lastConfig, hsteps] using hpostAtSteps
  have hcases := workHead_step_cases machine input lastConfig
  cases hdirection : crossing.token.2.direction with
  | leftToRight =>
      have hsource' :
          cursor.block = advertisedCutLeftBlock crossing.token.1 := by
        simpa [advertisedTimedCrossingSourceBlock, hdirection] using hsource
      have hleftLt :
          (advertisedCutLeftBlock crossing.token.1).val < T / b := by
        simp
      have hpreUpper : lastConfig.workHead <
          (advertisedTimedCrossingPhysicalCut alpha crossing).val + 1 := by
        have h := hpreInside.2
        rw [advertisedBlockLower_add_width_eq_upperExclusive,
          hsource', advertisedBlockUpperExclusive_of_val_lt _ _ hleftLt] at h
        simpa [advertisedTimedCrossingPhysicalCut,
          physicalCutOfCanonicalToken] using h
      have hpost' : (step machine input lastConfig).workHead =
          (advertisedTimedCrossingPhysicalCut alpha crossing).val + 1 := by
        simpa [advertisedTimedCrossingPostWorkHead, hdirection] using hpost
      rcases hcases with hmove | hrest
      · omega
      · rcases hrest with hstay | hmove
        · omega
        · unfold CrossesWorkBoundary
          exact Or.inl ⟨by omega, by omega⟩
  | rightToLeft =>
      have hsource' :
          cursor.block = advertisedCutRightBlock crossing.token.1 := by
        simpa [advertisedTimedCrossingSourceBlock, hdirection] using hsource
      have hrightPos :
          0 < (advertisedCutRightBlock crossing.token.1).val := by simp
      have hpreLower :
          (advertisedTimedCrossingPhysicalCut alpha crossing).val + 1 ≤
            lastConfig.workHead := by
        have h := hpreInside.1
        rw [hsource',
          advertisedBlockLower_of_val_pos _ _ hrightPos] at h
        simpa [advertisedTimedCrossingPhysicalCut,
          physicalCutOfCanonicalToken] using h
      have hpost' : (step machine input lastConfig).workHead =
          (advertisedTimedCrossingPhysicalCut alpha crossing).val := by
        simpa [advertisedTimedCrossingPostWorkHead, hdirection] using hpost
      rcases hcases with hmove | hrest
      · unfold CrossesWorkBoundary
        exact Or.inr ⟨by omega, by omega⟩
      · rcases hrest with hstay | hmove <;> omega

/-- A valid token-emitted visit contributes one crossing to the selected cut
of `bucket` exactly when the token carries that bucket label. -/
theorem timedAlphaScheduledVisitAtCrossing_streamingCount_selectedCut
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (crossing : TimedCanonicalCrossingToken machine.State T b)
    (htime : cursor.time.val ≤ crossing.sourceTime.val)
    (hsource : cursor.block = advertisedTimedCrossingSourceBlock crossing)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets cursor.block))
    (hvalid : FixedAlphaBlockVisitValid machine input alpha cursor.block
      (timedAlphaScheduledVisitAtCrossing alpha cursor crossing htime).visit
      carried)
    (bucket : Fin (T / b)) :
    streamingWorkBoundaryCrossingCountFrom machine input
      (fixedAlphaBlockVisitEntryConfiguration alpha cursor.block
        (timedAlphaScheduledVisitAtCrossing alpha cursor crossing htime).visit
        carried)
      (timedAlphaScheduledVisitAtCrossing
        alpha cursor crossing htime).visit.steps
      (fullBucketBoundary bucket (alpha.offsets bucket)).val =
        if crossing.token.1 = bucket then 1 else 0 := by
  let visit := (timedAlphaScheduledVisitAtCrossing
    alpha cursor crossing htime).visit
  let entry := fixedAlphaBlockVisitEntryConfiguration
    alpha cursor.block visit carried
  let lastConfig := runFrom machine input entry (visit.steps - 1)
  change streamingWorkBoundaryCrossingCountFrom machine input entry visit.steps
      (fullBucketBoundary bucket (alpha.offsets bucket)).val = _
  have hstepsPos : 0 < visit.steps := FixedAlphaBlockVisit.steps_pos visit
  have hsplit : visit.steps - 1 + 1 = visit.steps := by omega
  have hprefixInside : ∀ time, time ≤ visit.steps - 1 →
      WorkCellInSlab
        (advertisedBlockLower alpha.offsets cursor.block)
        (advertisedBlockWidth alpha.offsets cursor.block)
        (runFrom machine input entry time).workHead := by
    intro time htime'
    have hlt : time < visit.steps := by omega
    simpa [visit, entry] using hvalid.1 ⟨_, hlt⟩
  have hprefixZero :
      streamingWorkBoundaryCrossingCountFrom machine input entry
          (visit.steps - 1)
          (fullBucketBoundary bucket (alpha.offsets bucket)).val = 0 := by
    exact
      streamingWorkBoundaryCrossingCountFrom_eq_zero_of_inside_advertisedSlab
        machine input alpha.offsets cursor.block bucket entry
          (visit.steps - 1) hprefixInside
  have hlastOwn :=
    timedAlphaScheduledVisitAtCrossing_last_crosses_advertisedCut
      machine input alpha cursor crossing htime hsource carried hvalid
  have hlastIff :
      CrossesWorkBoundary
          (fullBucketBoundary bucket (alpha.offsets bucket)).val
          lastConfig.workHead (step machine input lastConfig).workHead ↔
        crossing.token.1 = bucket := by
    constructor
    · intro hquery
      have hval := crossesWorkBoundary_unique hlastOwn hquery
      have hcut : advertisedTimedCrossingPhysicalCut alpha crossing =
          fullBucketBoundary bucket (alpha.offsets bucket) := Fin.ext hval
      exact
        (advertisedTimedCrossingPhysicalCut_eq_fullBucketBoundary_iff
          alpha crossing bucket).mp hcut
    · intro hbucket
      have hcut :=
        (advertisedTimedCrossingPhysicalCut_eq_fullBucketBoundary_iff
          alpha crossing bucket).mpr hbucket
      simpa [hcut] using hlastOwn
  rw [← hsplit, streamingWorkBoundaryCrossingCountFrom_add, hprefixZero]
  change 0 + streamingWorkBoundaryCrossingCountFrom machine input lastConfig 1
      (fullBucketBoundary bucket (alpha.offsets bucket)).val = _
  rw [streamingWorkBoundaryCrossingCountFrom]
  rw [if_congr hlastIff rfl rfl]
  simp [streamingWorkBoundaryCrossingCountFrom]

/-- A valid positive final visit contributes zero crossings to every
advertised selected cut. -/
theorem timedAlphaFinalScheduledVisit_streamingCount_selectedCut_eq_zero
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (cursor : TimedAlphaVisitCursor machine.State T b)
    (htime : cursor.time.val < T)
    (hterminalHead : WorkCellInSlab
      (advertisedBlockLower alpha.offsets cursor.block)
      (advertisedBlockWidth alpha.offsets cursor.block)
      alpha.terminal.workHead.val)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets cursor.block))
    (hvalid : FixedAlphaBlockVisitValid machine input alpha cursor.block
      (timedAlphaFinalScheduledVisit alpha cursor htime).visit carried)
    (bucket : Fin (T / b)) :
    streamingWorkBoundaryCrossingCountFrom machine input
      (fixedAlphaBlockVisitEntryConfiguration alpha cursor.block
        (timedAlphaFinalScheduledVisit alpha cursor htime).visit carried)
      (timedAlphaFinalScheduledVisit alpha cursor htime).visit.steps
      (fullBucketBoundary bucket (alpha.offsets bucket)).val = 0 := by
  let visit := (timedAlphaFinalScheduledVisit alpha cursor htime).visit
  let entry := fixedAlphaBlockVisitEntryConfiguration
    alpha cursor.block visit carried
  change streamingWorkBoundaryCrossingCountFrom machine input entry visit.steps
    (fullBucketBoundary bucket (alpha.offsets bucket)).val = 0
  have hinside : ∀ time, time ≤ visit.steps →
      WorkCellInSlab
        (advertisedBlockLower alpha.offsets cursor.block)
        (advertisedBlockWidth alpha.offsets cursor.block)
        (runFrom machine input entry time).workHead := by
    intro time hle
    by_cases hlt : time < visit.steps
    · simpa [visit, entry] using hvalid.1 ⟨_, hlt⟩
    · have heq : time = visit.steps := by omega
      subst time
      have hrunHead : (runFrom machine input entry visit.steps).workHead =
          alpha.terminal.workHead.val := by
        have hexit := hvalid.2.2.2
        symm
        simpa [visit, entry, fixedAlphaBlockVisitRun,
          timedAlphaFinalScheduledVisit] using hexit
      rw [hrunHead]
      exact hterminalHead
  exact
    streamingWorkBoundaryCrossingCountFrom_eq_zero_of_inside_advertisedSlab
      machine input alpha.offsets cursor.block bucket entry visit.steps hinside

/-- A token fold contributes the multiplicity of each bucket label, plus the
crossing count of an arbitrary accepted suffix from the returned slab store. -/
theorem TimedAlphaTokenVisitFold.streamingCount_selectedCut_append
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    {cursor : TimedAlphaVisitCursor machine.State T b}
    {tokens : List (TimedCanonicalCrossingToken machine.State T b)}
    {visits : List (TimedAlphaScheduledVisit machine.State T b)}
    {finalCursor : TimedAlphaVisitCursor machine.State T b}
    (hfold : TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor)
    (store : FixedAlphaSlabStore alpha)
    (suffix : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllScheduledVisitsReplayAccepted machine input alpha store
      (visits ++ suffix))
    (bucket : Fin (T / b)) :
    ∃ finalStore : FixedAlphaSlabStore alpha,
      AllScheduledVisitsReplayAccepted machine input alpha finalStore suffix ∧
      fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha store
          (visits ++ suffix)
          (fullBucketBoundary bucket (alpha.offsets bucket)).val =
        List.countP (fun crossing => decide (crossing.token.1 = bucket)) tokens +
          fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha
            finalStore suffix
            (fullBucketBoundary bucket (alpha.offsets bucket)).val := by
  induction hfold generalizing store suffix with
  | nil cursor =>
      refine ⟨store, haccepted, ?_⟩
      simp
  | @cons cursor crossing rest visits finalCursor htime hsource htail ih =>
      let emitted := timedAlphaScheduledVisitAtCrossing
        alpha cursor crossing htime
      change FixedAlphaBlockVisitValid machine input alpha emitted.block
          emitted.visit (store emitted.block) ∧
        AllScheduledVisitsReplayAccepted machine input alpha
          (updateFixedAlphaSlabStore machine input alpha store emitted)
          (visits ++ suffix) at haccepted
      obtain ⟨finalStore, hfinalAccepted, hrec⟩ := ih
        (store := updateFixedAlphaSlabStore
          machine input alpha store emitted)
        (suffix := suffix) haccepted.2
      refine ⟨finalStore, hfinalAccepted, ?_⟩
      have hone : streamingWorkBoundaryCrossingCountFrom machine input
          (fixedAlphaBlockVisitEntryConfiguration alpha emitted.block
            emitted.visit (store emitted.block)) emitted.visit.steps
          (fullBucketBoundary bucket (alpha.offsets bucket)).val =
            if crossing.token.1 = bucket then 1 else 0 := by
        exact timedAlphaScheduledVisitAtCrossing_streamingCount_selectedCut
          machine input alpha cursor crossing htime hsource
            (store cursor.block) (by simpa [emitted] using haccepted.1) bucket
      simp only [List.cons_append,
        fixedAlphaScheduledVisitsStreamingCrossingCount, List.countP_cons]
      rw [hone, hrec]
      by_cases heq : crossing.token.1 = bucket
      · simp [heq, Nat.add_comm, Nat.add_left_comm]
      · simp [heq]

/-- **Noncircular advertised selected-cut multiplicity.**

Schedule validity and accepted local replay alone force the actual crossing
count at every advertised selected cut to equal its bucket-label multiplicity
in the hardwired alpha word.  No canonical-offset equality is assumed. -/
theorem advertisedSelectedCutMultiplicity_eq_actual_of_scheduleReplay
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits)
    (bucket : Fin (T / b)) :
    advertisedSelectedCutMultiplicity alpha bucket =
      workBoundaryCrossingCount machine input T
        (fullBucketBoundary bucket (alpha.offsets bucket)).val := by
  have hprofile := congrFun
    (fixedAlphaScheduledVisitsStreamingCrossingProfile_eq_actual
      machine input alpha visits hschedule haccepted)
    (fullBucketBoundary bucket (alpha.offsets bucket))
  change fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha
      (blankFixedAlphaSlabStore alpha) visits
      (fullBucketBoundary bucket (alpha.offsets bucket)).val =
    workBoundaryCrossingCount machine input T
      (fullBucketBoundary bucket (alpha.offsets bucket)).val at hprofile
  have hsequential :=
    allScheduledVisitsReplayAccepted_fromBlank_of_allBlockLists
      machine input alpha visits haccepted
  rcases hschedule with ⟨_hword, finalCursor, visitsSoFar,
    hfold, hfinish, _hchained⟩
  cases hfinish with
  | atTerminal htime hendpoint =>
      obtain ⟨finalStore, _hfinalAccepted, hreplay⟩ :=
        hfold.streamingCount_selectedCut_append
          machine input alpha (blankFixedAlphaSlabStore alpha) []
            (by simpa using hsequential) bucket
      simp at hreplay
      unfold advertisedSelectedCutMultiplicity
      exact hreplay.symm.trans hprofile
  | finalVisit htime hterminalHead =>
      let finalVisit := timedAlphaFinalScheduledVisit alpha finalCursor htime
      obtain ⟨finalStore, hfinalAccepted, hreplay⟩ :=
        hfold.streamingCount_selectedCut_append
          machine input alpha (blankFixedAlphaSlabStore alpha) [finalVisit]
            (by simpa [finalVisit] using hsequential) bucket
      have hvalid : FixedAlphaBlockVisitValid machine input alpha
          finalCursor.block finalVisit.visit
          (finalStore finalCursor.block) := by
        simpa [AllScheduledVisitsReplayAccepted, finalVisit] using
          hfinalAccepted
      have hzero :=
        timedAlphaFinalScheduledVisit_streamingCount_selectedCut_eq_zero
          machine input alpha finalCursor htime hterminalHead
            (finalStore finalCursor.block)
            (by simpa [finalVisit] using hvalid) bucket
      change fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha
          (blankFixedAlphaSlabStore alpha) (visitsSoFar ++ [finalVisit])
          (fullBucketBoundary bucket (alpha.offsets bucket)).val =
        List.countP (fun crossing => decide (crossing.token.1 = bucket))
            (decodePaddedWord (T / b) alpha.word) +
          (streamingWorkBoundaryCrossingCountFrom machine input
              (fixedAlphaBlockVisitEntryConfiguration alpha finalCursor.block
                finalVisit.visit (finalStore finalCursor.block))
              finalVisit.visit.steps
              (fullBucketBoundary bucket (alpha.offsets bucket)).val + 0) at hreplay
      rw [hzero] at hreplay
      unfold advertisedSelectedCutMultiplicity
      have hreplay' :
          List.countP (fun crossing => decide (crossing.token.1 = bucket))
              (decodePaddedWord (T / b) alpha.word) =
            fixedAlphaScheduledVisitsStreamingCrossingCount machine input alpha
              (blankFixedAlphaSlabStore alpha) (visitsSoFar ++ [finalVisit])
              (fullBucketBoundary bucket (alpha.offsets bucket)).val := by
        simpa [finalVisit] using hreplay.symm
      exact hreplay'.trans hprofile

end OneTapeMagnification
end Frontier
end Pnp4
