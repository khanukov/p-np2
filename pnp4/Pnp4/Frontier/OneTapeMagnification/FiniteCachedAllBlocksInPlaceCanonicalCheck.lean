import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksOuterCompiler
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceRollingFold

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

local instance cachedInputMachineStateDecidableEqForAllBlocksCanonicalCheck
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-!
# Total finite-cached all-block in-place canonical check

This module combines the total adaptive outer compiler with the full finite
cached rolling two-window fold.  The outer program is the replay-acceptance
gate.  On executable entry geometry, the rolling fold supplies both accumulated
flags and the complete bounded counter state used to close canonical cuts.

No operational reflection proposition is an input to the checker or its
correctness theorem.  On the canonical finite view of a valid schedule, outer
acceptance itself yields every blank-slab replay certificate; schedule validity
adds chronological order, after which the full finite-cached fold is exactly
the established semantic in-place fold.
-/

/-- Boolean projection of the full finite-cached rolling fold.  The fold still
computes and transports its complete counter vector; this projection is taken
only after all advertised blocks have been processed. -/
def finiteCachedAllBlocksInPlaceRollingFoldCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) : Bool :=
  let folded := finiteCachedAllBlocksInPlaceRollingFold machine input alpha
    blockVisits hentries
  folded.allBlockVisitsValid && folded.allClosedCutsValid

/-- Total schedule-level checker.  Invalid entry geometry rejects before the
proof-indexed rolling fold is initialized.  For valid geometry, replay is
checked by the compiled outer program and flags/counters by the full finite
cached in-place fold. -/
def finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) : Bool :=
  let blockVisits := fun block => timedAlphaBlockVisits block scheduled
  let outerAccepted :=
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index)
  if hgeometry : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true then
    let hentries :=
      (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
        alpha blockVisits).1 hgeometry
    (timedAlphaVisitScheduleCheck
        (cachedInputMachine machine) alpha scheduled && outerAccepted) &&
      finiteCachedAllBlocksInPlaceRollingFoldCheck machine input alpha
        blockVisits hentries
  else
    false

/-- Under simultaneous blank-slab acceptance, the finite-cached fold Boolean
is exactly the existing semantic in-place fold Boolean.  The proof uses the
full-state equality, including the shifted counter vector. -/
theorem finiteCachedAllBlocksInPlaceRollingFoldCheck_eq_timedAlpha_of_accepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
        (timedAlphaBlockVisits block scheduled)) :
    let blockVisits := fun block => timedAlphaBlockVisits block scheduled
    let hentries := fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
    finiteCachedAllBlocksInPlaceRollingFoldCheck machine input alpha
        blockVisits hentries =
      timedAlphaInPlaceTwoWindowFoldCheck
        (cachedInputMachine machine) input alpha scheduled := by
  dsimp only
  have hfold :=
    finiteCachedAllBlocksInPlaceRollingFold_eq_inPlace_of_acceptedFromBlank
      machine input alpha
        (fun block => timedAlphaBlockVisits block scheduled) haccepted
  unfold finiteCachedAllBlocksInPlaceRollingFoldCheck
    timedAlphaInPlaceTwoWindowFoldCheck
  rw [hfold]
  unfold timedScheduleBlankBlockSlabs timedScheduleBlockVisitFamily
  rfl

/-- For a valid advertised schedule on its canonical finite input view, the
new total finite-cached checker is extensionally identical to the established
in-place canonical-cut checkpoint.  No reflection premise is required. -/
theorem finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck_eq_existing_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hvalid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck
        machine input alpha scheduled =
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) input alpha scheduled := by
  let blockVisits := fun block => timedAlphaBlockVisits block scheduled
  let outerAccepted :=
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index)
  have hschedule : timedAlphaVisitScheduleCheck
      (cachedInputMachine machine) alpha scheduled = true :=
    (timedAlphaVisitScheduleCheck_eq_true_iff
      (cachedInputMachine machine) alpha scheduled).2 hvalid
  by_cases houter : outerAccepted = true
  · have houter' :
        (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
          (n := input.length) machine alpha scheduled).eval
            (fun index => input.get index) = true := by
      simpa [outerAccepted] using houter
    have hreplay : forall block : Fin (T / b + 1),
        FixedAlphaBlockVisitReplayAccepted
          (cachedInputMachine machine) input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) := by
      apply (compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval_eq_true_iff_replayAccepted
        machine input alpha blockVisits).1
      simpa [blockVisits,
        compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks] using houter'
    have haccepted : forall block : Fin (T / b + 1),
        FixedAlphaBlockVisitListAcceptedFromBlank
          (cachedInputMachine machine) input alpha block
          (blockVisits block) := by
      intro block
      exact ⟨hvalid.blockVisitsChronological
        (cachedInputMachine machine) block, hreplay block⟩
    let hentries := fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
    have hgeometry : fixedAlphaAllBlockVisitEntriesInsideCheck
        alpha blockVisits = true :=
      (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
        alpha blockVisits).2 hentries
    have hfiniteFold : finiteCachedAllBlocksInPlaceRollingFoldCheck
        machine input alpha blockVisits hentries =
      timedAlphaInPlaceTwoWindowFoldCheck
        (cachedInputMachine machine) input alpha scheduled := by
      simpa [blockVisits, hentries] using
        finiteCachedAllBlocksInPlaceRollingFoldCheck_eq_timedAlpha_of_accepted
          machine input alpha scheduled (by
            simpa [blockVisits] using haccepted)
    have hallCheck : timedAlphaAllBlockVisitsCheckFromBlank
        (cachedInputMachine machine) input alpha scheduled = true :=
      (timedAlphaAllBlockVisitsCheckFromBlank_eq_true_iff
        (cachedInputMachine machine) input alpha scheduled).2 (by
          simpa [blockVisits] using haccepted)
    unfold finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      timedAlphaVisitScheduleAllBlockVisitsCheck
    simp only [hschedule, hallCheck, Bool.true_and]
    rw [dif_pos hgeometry]
    rw [houter']
    simpa [blockVisits] using hfiniteFold
  · have hreflect :=
      compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_eval_eq_allBlockVisitsCheck_of_valid
        machine input alpha scheduled hvalid
    have hallCheck : timedAlphaAllBlockVisitsCheckFromBlank
        (cachedInputMachine machine) input alpha scheduled = false := by
      cases hsemantic : timedAlphaAllBlockVisitsCheckFromBlank
          (cachedInputMachine machine) input alpha scheduled with
      | false => rfl
      | true =>
          exfalso
          apply houter
          have : outerAccepted =
              timedAlphaAllBlockVisitsCheckFromBlank
                (cachedInputMachine machine) input alpha scheduled := by
            simpa [outerAccepted] using hreflect
          exact this.trans hsemantic
    have houterFalse :
        (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
          (n := input.length) machine alpha scheduled).eval
            (fun index => input.get index) = false :=
      hreflect.trans hallCheck
    unfold finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      timedAlphaVisitScheduleAllBlockVisitsCheck
    simp only [hschedule, hallCheck, Bool.and_false, Bool.false_and]
    rw [houterFalse]
    split <;> simp

/-- Exact canonical-cut semantics of the new finite-cached combined checker
for valid schedules. -/
theorem finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck_eq_true_iff_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hvalid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck
        machine input alpha scheduled = true ↔
      timedAlphaVisitScheduleAllBlockVisitsCheck
          (cachedInputMachine machine) input alpha scheduled = true ∧
        alpha.offsets = canonicalCutOffsets
          (cachedInputMachine machine) input T b hb := by
  rw [finiteCachedTimedAlphaScheduleAllBlocksInPlaceCanonicalCheck_eq_existing_of_valid
    machine input alpha scheduled hvalid]
  exact timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
    (cachedInputMachine machine) input T b hb alpha scheduled

end OneTapeMagnification
end Frontier
end Pnp4
