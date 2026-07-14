import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaCanonicality

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Executable canonical timed-alpha components

The preceding checker still exposes the visit schedule as a separate argument.
For a fixed timed alpha that schedule is deterministic, so this file runs the
builder internally and obtains one Boolean component predicate depending only
on the machine input and the ambient alpha.

The acceptance-gated version is the exact lower semantic statement used in a
Viola-style decomposition: at a fixed horizon an accepting deterministic run
has exactly one accepting alpha component, while a nonaccepting run has none.
This is an executable finite decomposition theorem, not a branching-program
width bound or a generator.
-/

/-- Run the unique advertised schedule, all local block replays, and the
replayed leftmost-minimum cut check for one ambient alpha. -/
def timedAlphaCanonicalComponentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (_hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) : Bool :=
  match buildTimedAlphaVisitSchedule machine alpha with
  | none => false
  | some visits =>
      timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
        machine input alpha visits

/-- The schedule-free component accepts exactly the chronological canonical
alpha of the supplied deterministic run. -/
theorem timedAlphaCanonicalComponentCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    timedAlphaCanonicalComponentCheck machine input T b hb alpha = true ↔
      alpha = chronologicalTimedCanonicalAlpha machine input T b hb := by
  constructor
  · intro hcheck
    unfold timedAlphaCanonicalComponentCheck at hcheck
    split at hcheck
    · simp at hcheck
    · rename_i visits hbuild
      exact
        timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
          machine input T b hb alpha visits hcheck
  · intro halpha
    subst alpha
    obtain ⟨visits, hcheck⟩ :=
      exists_actualTimedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true
        machine input T b hb
    have hbase : timedAlphaVisitScheduleAllBlockVisitsCheck machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) visits = true := by
      have hparts :
          timedAlphaVisitScheduleAllBlockVisitsCheck machine input
                (chronologicalTimedCanonicalAlpha machine input T b hb) visits =
              true ∧
            replayedTimedAlphaCutMinimalityCheck machine input
                (chronologicalTimedCanonicalAlpha machine input T b hb) visits =
              true := by
        simpa [timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck] using hcheck
      exact hparts.1
    have hschedule : timedAlphaVisitScheduleCheck machine
        (chronologicalTimedCanonicalAlpha machine input T b hb) visits = true := by
      have hparts :
          timedAlphaVisitScheduleCheck machine
                (chronologicalTimedCanonicalAlpha machine input T b hb) visits =
              true ∧
            timedAlphaAllBlockVisitsCheckFromBlank machine input
                (chronologicalTimedCanonicalAlpha machine input T b hb) visits =
              true := by
        simpa [timedAlphaVisitScheduleAllBlockVisitsCheck] using hbase
      exact hparts.1
    have hbuild : buildTimedAlphaVisitSchedule machine
        (chronologicalTimedCanonicalAlpha machine input T b hb) = some visits := by
      have hparts :
          timedAlphaWordSyntacticCheck
                (chronologicalTimedCanonicalAlpha machine input T b hb) = true ∧
            decide (buildTimedAlphaVisitSchedule machine
                (chronologicalTimedCanonicalAlpha machine input T b hb) =
              some visits) = true := by
        simpa [timedAlphaVisitScheduleCheck] using hschedule
      exact of_decide_eq_true hparts.2
    simp [timedAlphaCanonicalComponentCheck, hbuild, hcheck]

/-- Every input has exactly one alpha accepted by the schedule-free canonical
component checker.  This statement authenticates a run transcript; it does not
yet require the run to accept. -/
theorem existsUnique_timedAlphaCanonicalComponentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    ∃! alpha : AmbientTimedCanonicalAlpha machine.State T b,
      timedAlphaCanonicalComponentCheck machine input T b hb alpha = true := by
  refine ⟨chronologicalTimedCanonicalAlpha machine input T b hb,
    (timedAlphaCanonicalComponentCheck_eq_true_iff
      machine input T b hb _).2 rfl, ?_⟩
  intro alpha hcheck
  exact (timedAlphaCanonicalComponentCheck_eq_true_iff
    machine input T b hb alpha).1 hcheck

/-- Add the deterministic machine's accepting outcome to one canonical alpha
component. -/
def timedAlphaAcceptingComponentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) : Bool :=
  timedAlphaCanonicalComponentCheck machine input T b hb alpha &&
    decide (machine.halt alpha.terminal.state = some .accept)

/-- Exact reflection of an accepting component: both the transcript and the
terminal outcome are forced by the deterministic run. -/
theorem timedAlphaAcceptingComponentCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    timedAlphaAcceptingComponentCheck machine input T b hb alpha = true ↔
      alpha = chronologicalTimedCanonicalAlpha machine input T b hb ∧
        IsAccepting machine (run machine input T) := by
  rw [timedAlphaAcceptingComponentCheck, Bool.and_eq_true,
    timedAlphaCanonicalComponentCheck_eq_true_iff]
  constructor
  · rintro ⟨halpha, haccept⟩
    subst alpha
    refine ⟨rfl, ?_⟩
    have := of_decide_eq_true haccept
    simpa [IsAccepting, outcome, chronologicalTimedCanonicalAlpha] using this
  · rintro ⟨halpha, haccept⟩
    subst alpha
    refine ⟨rfl, decide_eq_true ?_⟩
    simpa [IsAccepting, outcome, chronologicalTimedCanonicalAlpha] using haccept

/-- The union of all accepting alpha components is exactly deterministic
acceptance at the fixed horizon. -/
theorem exists_timedAlphaAcceptingComponentCheck_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (∃ alpha : AmbientTimedCanonicalAlpha machine.State T b,
      timedAlphaAcceptingComponentCheck machine input T b hb alpha = true) ↔
        IsAccepting machine (run machine input T) := by
  constructor
  · rintro ⟨alpha, hcheck⟩
    exact (timedAlphaAcceptingComponentCheck_eq_true_iff
      machine input T b hb alpha).1 hcheck |>.2
  · intro haccept
    refine ⟨chronologicalTimedCanonicalAlpha machine input T b hb, ?_⟩
    exact (timedAlphaAcceptingComponentCheck_eq_true_iff
      machine input T b hb _).2 ⟨rfl, haccept⟩

/-- An accepting run has exactly one accepting alpha component. -/
theorem accepting_run_has_unique_timedAlphaComponent
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (haccept : IsAccepting machine (run machine input T)) :
    ∃! alpha : AmbientTimedCanonicalAlpha machine.State T b,
      timedAlphaAcceptingComponentCheck machine input T b hb alpha = true := by
  refine ⟨chronologicalTimedCanonicalAlpha machine input T b hb,
    (timedAlphaAcceptingComponentCheck_eq_true_iff
      machine input T b hb _).2 ⟨rfl, haccept⟩, ?_⟩
  intro alpha hcheck
  exact (timedAlphaAcceptingComponentCheck_eq_true_iff
    machine input T b hb alpha).1 hcheck |>.1

/-- A nonaccepting run has no accepting alpha component. -/
theorem nonaccepting_run_has_no_timedAlphaComponent
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (hreject : ¬ IsAccepting machine (run machine input T)) :
    ¬ ∃ alpha : AmbientTimedCanonicalAlpha machine.State T b,
      timedAlphaAcceptingComponentCheck machine input T b hb alpha = true := by
  intro hexists
  exact hreject ((exists_timedAlphaAcceptingComponentCheck_iff
    machine input T b hb).1 hexists)

/-- The finite sum of all fixed-alpha accepting components is exactly the
acceptance bit.  Thus the semantic union is unambiguous: its multiplicity is
never larger than one.  This identity does not yet compile the individual
components to read-once branching programs. -/
noncomputable def timedAlphaAcceptingComponentMultiplicity
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) : Nat := by
  letI : Fintype machine.State := machine.stateFintype
  exact ∑ alpha : AmbientTimedCanonicalAlpha machine.State T b,
    if timedAlphaAcceptingComponentCheck machine input T b hb alpha = true
    then 1 else 0

/-- Exact sum form of the accepting-component decomposition. -/
theorem timedAlphaAcceptingComponentMultiplicity_eq_acceptanceBit
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    timedAlphaAcceptingComponentMultiplicity machine input T b hb =
      if machine.halt (run machine input T).state = some .accept then 1 else 0 := by
  classical
  letI : Fintype machine.State := machine.stateFintype
  by_cases haccept : IsAccepting machine (run machine input T)
  · have hhalt : machine.halt (run machine input T).state = some .accept := by
      simpa [IsAccepting, outcome] using haccept
    simp [timedAlphaAcceptingComponentMultiplicity,
      timedAlphaAcceptingComponentCheck_eq_true_iff, haccept, hhalt]
  · have hhalt : machine.halt (run machine input T).state ≠ some .accept := by
      simpa [IsAccepting, outcome] using haccept
    simp [timedAlphaAcceptingComponentMultiplicity,
      timedAlphaAcceptingComponentCheck_eq_true_iff, haccept, hhalt]

/-- Distinct alpha components have disjoint accepting fibers. -/
theorem timedAlphaAcceptingComponents_disjoint
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : AmbientTimedCanonicalAlpha machine.State T b}
    (hne : left ≠ right) :
    ¬ (timedAlphaAcceptingComponentCheck machine input T b hb left = true ∧
      timedAlphaAcceptingComponentCheck machine input T b hb right = true) := by
  rintro ⟨hleft, hright⟩
  apply hne
  exact ((timedAlphaAcceptingComponentCheck_eq_true_iff
      machine input T b hb left).1 hleft).1.trans
    ((timedAlphaAcceptingComponentCheck_eq_true_iff
      machine input T b hb right).1 hright).1.symm

end OneTapeMagnification
end Frontier
end Pnp4
