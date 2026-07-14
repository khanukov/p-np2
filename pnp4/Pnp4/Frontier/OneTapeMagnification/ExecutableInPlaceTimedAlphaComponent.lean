import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaComponent
import Pnp4.Frontier.OneTapeMagnification.InPlaceTwoWindowScheduleClosure

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Schedule-free canonical components with an in-place two-window cut check

This file replaces the full replayed crossing-profile checkpoint in one
fixed-alpha component by the proved left-to-right rolling fold.  The
executable fold keeps only the two `b`-windows adjacent to the block currently
being replayed.  Its schedule-level reflection is now unconditional once the
existing schedule/all-block check succeeds.

The result is still a semantic component checker, not yet a single finite
branching program: the remaining construction must carry this fold state
through the compiled multi-visit verifier.
-/

/-- The two Boolean flags produced by the rolling `2b` fold for one schedule. -/
def timedAlphaInPlaceTwoWindowFoldCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) : Bool :=
  let folded := inPlaceTwoWindowBlockFold machine input alpha
    (timedScheduleBlankBlockSlabs alpha)
    (timedScheduleBlockVisitFamily scheduled)
  folded.allBlockVisitsValid && folded.allClosedCutsValid

/-- Under the executable schedule/all-block checkpoint, the rolling flags
reflect the actual leftmost-minimum condition with no residual locality
premise. -/
theorem timedAlphaInPlaceTwoWindowFoldCheck_eq_true_iff_actualCuts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha scheduled = true) :
    timedAlphaInPlaceTwoWindowFoldCheck machine input alpha scheduled = true <->
      AdvertisedTimedAlphaCutsAreLeftmostMinimum machine input alpha := by
  simpa [timedAlphaInPlaceTwoWindowFoldCheck,
    AdvertisedTimedAlphaCutsAreLeftmostMinimum] using
    (timedAlphaVisitScheduleAllBlockVisitsCheck_inPlaceTwoWindowFold_iff_actualCuts
      machine input alpha scheduled hcheck)

/-- The rolling flags therefore force exactly the canonical offset vector. -/
theorem timedAlphaInPlaceTwoWindowFoldCheck_eq_true_iff_offsets_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha scheduled = true) :
    timedAlphaInPlaceTwoWindowFoldCheck machine input alpha scheduled = true <->
      alpha.offsets = canonicalCutOffsets machine input T b hb := by
  rw [timedAlphaInPlaceTwoWindowFoldCheck_eq_true_iff_actualCuts
    machine input alpha scheduled hcheck]
  simpa [AdvertisedTimedAlphaCutsAreLeftmostMinimum,
    actualWorkBoundaryCrossingProfile, canonicalCutOffsets] using
    (advertisedCutOffsetsAreLeftmostMinimum_iff_eq_canonical hb
      (actualWorkBoundaryCrossingProfile machine input T) alpha.offsets)

/-- One executable schedule checkpoint using only the rolling cut carrier. -/
def timedAlphaVisitScheduleInPlaceCanonicalCutCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) : Bool :=
  timedAlphaVisitScheduleAllBlockVisitsCheck machine input alpha scheduled &&
    timedAlphaInPlaceTwoWindowFoldCheck machine input alpha scheduled

/-- Exact schedule-level semantics of the in-place canonical checkpoint. -/
theorem timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) :
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        machine input alpha scheduled = true <->
      timedAlphaVisitScheduleAllBlockVisitsCheck
          machine input alpha scheduled = true /\
        alpha.offsets = canonicalCutOffsets machine input T b hb := by
  constructor
  · intro hcombined
    rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck,
      Bool.and_eq_true] at hcombined
    exact ⟨hcombined.1,
      (timedAlphaInPlaceTwoWindowFoldCheck_eq_true_iff_offsets_eq
        machine input T b hb alpha scheduled hcombined.1).1 hcombined.2⟩
  · rintro ⟨hbase, hoffsets⟩
    rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck,
      Bool.and_eq_true]
    exact ⟨hbase,
      (timedAlphaInPlaceTwoWindowFoldCheck_eq_true_iff_offsets_eq
        machine input T b hb alpha scheduled hbase).2 hoffsets⟩

/-- The in-place schedule checkpoint has the same exact semantics as the
former full-profile checkpoint. -/
theorem timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) :
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        machine input alpha scheduled = true <->
      timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
        machine input alpha scheduled = true := by
  rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
      machine input T b hb alpha scheduled,
    timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true_iff
      machine input T b hb alpha scheduled]

/-- Run the deterministic schedule builder internally and use the rolling
`2b` checkpoint for one ambient alpha. -/
def timedAlphaInPlaceCanonicalComponentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (_hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) : Bool :=
  match buildTimedAlphaVisitSchedule machine alpha with
  | none => false
  | some scheduled =>
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        machine input alpha scheduled

/-- The schedule-free rolling component accepts exactly the chronological
canonical transcript. -/
theorem timedAlphaInPlaceCanonicalComponentCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    timedAlphaInPlaceCanonicalComponentCheck
        machine input T b hb alpha = true <->
      alpha = chronologicalTimedCanonicalAlpha machine input T b hb := by
  constructor
  · intro hcheck
    unfold timedAlphaInPlaceCanonicalComponentCheck at hcheck
    split at hcheck
    · simp at hcheck
    · rename_i scheduled hbuild
      have hreplayed :
          timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
            machine input alpha scheduled = true :=
        (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
          machine input T b hb alpha scheduled).1 hcheck
      exact
        timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
          machine input T b hb alpha scheduled hreplayed
  · intro halpha
    subst alpha
    obtain ⟨scheduled, hreplayed⟩ :=
      exists_actualTimedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true
        machine input T b hb
    have hinPlace : timedAlphaVisitScheduleInPlaceCanonicalCutCheck machine
        input (chronologicalTimedCanonicalAlpha machine input T b hb)
        scheduled = true :=
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
        machine input T b hb
        (chronologicalTimedCanonicalAlpha machine input T b hb) scheduled).2
        hreplayed
    have hbase : timedAlphaVisitScheduleAllBlockVisitsCheck machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) scheduled =
          true := by
      exact (timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true_iff
        machine input T b hb
        (chronologicalTimedCanonicalAlpha machine input T b hb) scheduled).1
          hreplayed |>.1
    have hschedule : timedAlphaVisitScheduleCheck machine
        (chronologicalTimedCanonicalAlpha machine input T b hb) scheduled =
          true := by
      have hparts :
          timedAlphaVisitScheduleCheck machine
                (chronologicalTimedCanonicalAlpha machine input T b hb)
                scheduled = true /\
            timedAlphaAllBlockVisitsCheckFromBlank machine input
                (chronologicalTimedCanonicalAlpha machine input T b hb)
                scheduled = true := by
        simpa [timedAlphaVisitScheduleAllBlockVisitsCheck] using hbase
      exact hparts.1
    have hbuild : buildTimedAlphaVisitSchedule machine
        (chronologicalTimedCanonicalAlpha machine input T b hb) =
          some scheduled := by
      have hparts :
          timedAlphaWordSyntacticCheck
                (chronologicalTimedCanonicalAlpha machine input T b hb) =
              true /\
            decide (buildTimedAlphaVisitSchedule machine
                (chronologicalTimedCanonicalAlpha machine input T b hb) =
              some scheduled) = true := by
        simpa [timedAlphaVisitScheduleCheck] using hschedule
      exact of_decide_eq_true hparts.2
    simp [timedAlphaInPlaceCanonicalComponentCheck, hbuild, hinPlace]

/-- Acceptance-gated in-place component. -/
def timedAlphaInPlaceAcceptingComponentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) : Bool :=
  timedAlphaInPlaceCanonicalComponentCheck machine input T b hb alpha &&
    decide (machine.halt alpha.terminal.state = some .accept)

/-- Exact accepting semantics of the rolling component. -/
theorem timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    timedAlphaInPlaceAcceptingComponentCheck
        machine input T b hb alpha = true <->
      alpha = chronologicalTimedCanonicalAlpha machine input T b hb /\
        IsAccepting machine (run machine input T) := by
  rw [timedAlphaInPlaceAcceptingComponentCheck, Bool.and_eq_true,
    timedAlphaInPlaceCanonicalComponentCheck_eq_true_iff]
  constructor
  · rintro ⟨halpha, haccept⟩
    subst alpha
    refine ⟨rfl, ?_⟩
    have := of_decide_eq_true haccept
    simpa [IsAccepting, outcome, chronologicalTimedCanonicalAlpha] using this
  · rintro ⟨halpha, haccept⟩
    subst alpha
    refine ⟨rfl, decide_eq_true ?_⟩
    simpa [IsAccepting, outcome, chronologicalTimedCanonicalAlpha] using
      haccept

/-- The coherent union of the in-place components is exactly deterministic
acceptance at the fixed horizon. -/
theorem exists_timedAlphaInPlaceAcceptingComponentCheck_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (∃ alpha : AmbientTimedCanonicalAlpha machine.State T b,
      timedAlphaInPlaceAcceptingComponentCheck
        machine input T b hb alpha = true) <->
      IsAccepting machine (run machine input T) := by
  constructor
  · rintro ⟨alpha, hcheck⟩
    exact (timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
      machine input T b hb alpha).1 hcheck |>.2
  · intro haccept
    exact ⟨chronologicalTimedCanonicalAlpha machine input T b hb,
      (timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
        machine input T b hb _).2 ⟨rfl, haccept⟩⟩

/-- Distinct in-place components have disjoint accepting fibers. -/
theorem timedAlphaInPlaceAcceptingComponents_disjoint
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : AmbientTimedCanonicalAlpha machine.State T b}
    (hne : left ≠ right) :
    ¬ (timedAlphaInPlaceAcceptingComponentCheck
          machine input T b hb left = true /\
      timedAlphaInPlaceAcceptingComponentCheck
          machine input T b hb right = true) := by
  rintro ⟨hleft, hright⟩
  apply hne
  exact ((timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
      machine input T b hb left).1 hleft).1.trans
    ((timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
      machine input T b hb right).1 hright).1.symm

end OneTapeMagnification
end Frontier
end Pnp4
