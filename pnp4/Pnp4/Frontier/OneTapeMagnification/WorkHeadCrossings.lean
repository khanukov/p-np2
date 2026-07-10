import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.OneTapeMachine
import Pnp4.Frontier.OneTapeMagnification.CanonicalBoundarySelection

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Work-head trajectories and crossing counts

This file connects the abstract crossing-count input of
`CanonicalBoundarySelection` to an actual run of the deterministic one-tape
machine in `OneTapeMachine`.

A boundary numbered `j` separates work-tape cells `j` and `j + 1`.  A
transition crosses it precisely when its two work-head positions are those two
cells in either order.  Consequently a stay move, a halted stuttering step,
and the clamped left move from cell zero contribute no crossing.

For a run of `steps` transitions from work-head position `h`, every crossed
boundary lies in `Fin (h + steps)`.  Since one legal transition can cross at
most one boundary, the sum of all crossing counts in this complete reachable
range is at most `steps`.  Specializing to the blank-start run, whose initial
head is zero, supplies exactly the `Fin steps -> Nat` hypothesis needed by
`sum_canonicalBoundary_le_div`.
-/

/-- Work-head position after exactly `time` transitions from `config`. -/
def workHeadTrajectoryFrom (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time : Nat) : Nat :=
  (runFrom machine input config time).workHead

/-- Work-head position after exactly `time` transitions of the blank-start run. -/
def workHeadTrajectory (machine : DeterministicMachine) (input : List Bool)
    (time : Nat) : Nat :=
  workHeadTrajectoryFrom machine input (initialConfiguration machine) time

@[simp]
theorem workHeadTrajectoryFrom_zero (machine : DeterministicMachine)
    (input : List Bool) (config : Configuration machine.State) :
    workHeadTrajectoryFrom machine input config 0 = config.workHead :=
  rfl

@[simp]
theorem workHeadTrajectory_zero (machine : DeterministicMachine)
    (input : List Bool) :
    workHeadTrajectory machine input 0 = 0 :=
  rfl

/-- Iterating a deterministic step `time + 1` times is the same as stepping
once after the first `time` iterations. -/
theorem runFrom_succ_eq_step_runFrom
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time : Nat) :
    runFrom machine input config (time + 1) =
      step machine input (runFrom machine input config time) := by
  induction time generalizing config with
  | zero => rfl
  | succ time ih =>
      simpa only [Nat.succ_eq_add_one, runFrom_succ] using
        (ih (config := step machine input config))

/-- One small step moves the work head left once, stays, or moves right once.
The left alternative uses truncated subtraction and therefore includes the
clamped move from zero. -/
theorem workHead_step_cases
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    (step machine input config).workHead = config.workHead - 1 ∨
      (step machine input config).workHead = config.workHead ∨
      (step machine input config).workHead = config.workHead + 1 := by
  unfold step
  split
  · exact Or.inr (Or.inl rfl)
  · dsimp only [applyInstruction]
    cases (machine.transition config.state
      (readOnlySymbol input config.inputHead)
      (WorkTape.read config.workTape config.workHead)).workMove <;>
      simp [moveWorkHead]

/-- In one transition the work head increases by at most one. -/
theorem workHead_step_le_succ
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    (step machine input config).workHead ≤ config.workHead + 1 := by
  rcases workHead_step_cases machine input config with h | h | h <;>
    omega

/-- After `time` transitions from head position `h`, the head is at most
`h + time`. -/
theorem workHeadTrajectoryFrom_le_initial_add
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time : Nat) :
    workHeadTrajectoryFrom machine input config time ≤ config.workHead + time := by
  induction time generalizing config with
  | zero => simp
  | succ time ih =>
      calc
        workHeadTrajectoryFrom machine input config (Nat.succ time) =
            workHeadTrajectoryFrom machine input
              (step machine input config) time := by
                rfl
        _ ≤ (step machine input config).workHead + time := ih _
        _ ≤ (config.workHead + 1) + time :=
          Nat.add_le_add_right (workHead_step_le_succ machine input config) time
        _ = config.workHead + Nat.succ time := by omega

/-- For the blank-start run, the work head never lies to the right of the
current time. -/
theorem workHeadTrajectory_le_time
    (machine : DeterministicMachine) (input : List Bool) (time : Nat) :
    workHeadTrajectory machine input time ≤ time := by
  simpa [workHeadTrajectory, initialConfiguration] using
    (workHeadTrajectoryFrom_le_initial_add machine input
      (initialConfiguration machine) time)

/-- Boundary `j` (between cells `j` and `j + 1`) is crossed by a transition
from `fromHead` to `toHead`. -/
def CrossesWorkBoundary (j fromHead toHead : Nat) : Prop :=
  (fromHead = j ∧ toHead = j + 1) ∨
    (fromHead = j + 1 ∧ toHead = j)

instance decidableCrossesWorkBoundary (j fromHead toHead : Nat) :
    Decidable (CrossesWorkBoundary j fromHead toHead) := by
  unfold CrossesWorkBoundary
  infer_instance

/-- A stay move crosses no work-tape boundary. -/
@[simp]
theorem not_crossesWorkBoundary_stay (j head : Nat) :
    ¬ CrossesWorkBoundary j head head := by
  simp only [CrossesWorkBoundary]
  omega

/-- A right move from `head` crosses exactly boundary `head`. -/
theorem crossesWorkBoundary_right_iff (j head : Nat) :
    CrossesWorkBoundary j head (head + 1) ↔ j = head := by
  simp only [CrossesWorkBoundary]
  omega

/-- A left move crosses exactly the boundary immediately to its left, unless
the head is at zero, where the machine's left move is clamped and crosses
nothing. -/
theorem crossesWorkBoundary_left_iff (j head : Nat) :
    CrossesWorkBoundary j head (head - 1) ↔ 0 < head ∧ j = head - 1 := by
  simp only [CrossesWorkBoundary]
  omega

/-- A pair of head positions cannot cross two distinct boundaries.  This is a
property of the exact crossing predicate and needs no machine assumption. -/
theorem crossesWorkBoundary_unique
    {fromHead toHead j k : Nat}
    (hj : CrossesWorkBoundary j fromHead toHead)
    (hk : CrossesWorkBoundary k fromHead toHead) :
    j = k := by
  rcases hj with hj | hj <;> rcases hk with hk | hk <;> omega

/-- The transition at time `time` crosses work boundary `j`. -/
def WorkBoundaryCrossingAtFrom (machine : DeterministicMachine)
    (input : List Bool) (config : Configuration machine.State)
    (time j : Nat) : Prop :=
  CrossesWorkBoundary j
    (workHeadTrajectoryFrom machine input config time)
    (workHeadTrajectoryFrom machine input config (time + 1))

instance decidableWorkBoundaryCrossingAtFrom
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time j : Nat) :
    Decidable (WorkBoundaryCrossingAtFrom machine input config time j) := by
  unfold WorkBoundaryCrossingAtFrom
  infer_instance

/-- Blank-start specialization of `WorkBoundaryCrossingAtFrom`. -/
def WorkBoundaryCrossingAt (machine : DeterministicMachine)
    (input : List Bool) (time j : Nat) : Prop :=
  WorkBoundaryCrossingAtFrom machine input (initialConfiguration machine) time j

/-- Consecutive positions in an actual trajectory are related by one of the
three legal work-head moves. -/
theorem workHeadTrajectoryFrom_step_cases
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time : Nat) :
    workHeadTrajectoryFrom machine input config (time + 1) =
        workHeadTrajectoryFrom machine input config time - 1 ∨
      workHeadTrajectoryFrom machine input config (time + 1) =
        workHeadTrajectoryFrom machine input config time ∨
      workHeadTrajectoryFrom machine input config (time + 1) =
        workHeadTrajectoryFrom machine input config time + 1 := by
  rw [workHeadTrajectoryFrom, runFrom_succ_eq_step_runFrom]
  exact workHead_step_cases machine input (runFrom machine input config time)

/-- At a fixed transition of a real run, two crossed-boundary witnesses name
the same boundary. -/
theorem workBoundaryCrossingAtFrom_unique
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time : Nat) {j k : Nat}
    (hj : WorkBoundaryCrossingAtFrom machine input config time j)
    (hk : WorkBoundaryCrossingAtFrom machine input config time k) :
    j = k :=
  crossesWorkBoundary_unique hj hk

/-- Every boundary crossed during the first `steps` transitions belongs to
the complete reachable range `Fin (config.workHead + steps)`. -/
theorem crossedWorkBoundary_lt_initial_add_steps
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) {time steps j : Nat}
    (htime : time < steps)
    (hcross : WorkBoundaryCrossingAtFrom machine input config time j) :
    j < config.workHead + steps := by
  have hhead := workHeadTrajectoryFrom_le_initial_add machine input config time
  rcases hcross with hcross | hcross <;> omega

/-- The same reachable-boundary fact in the addition order used by the finite
summation type below. -/
theorem crossedWorkBoundary_lt_steps_add_initial
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) {time steps j : Nat}
    (htime : time < steps)
    (hcross : WorkBoundaryCrossingAtFrom machine input config time j) :
    j < steps + config.workHead := by
  simpa [Nat.add_comm] using
    crossedWorkBoundary_lt_initial_add_steps machine input config htime hcross

/-- Number of transitions among `0, ..., steps - 1` which cross boundary `j`,
starting from an arbitrary configuration. -/
def workBoundaryCrossingCountFrom (machine : DeterministicMachine)
    (input : List Bool) (config : Configuration machine.State)
    (steps j : Nat) : Nat :=
  ∑ time : Fin steps,
    if WorkBoundaryCrossingAtFrom machine input config time.val j then 1 else 0

/-- Crossing count for the blank-start run. -/
def workBoundaryCrossingCount (machine : DeterministicMachine)
    (input : List Bool) (steps j : Nat) : Nat :=
  workBoundaryCrossingCountFrom machine input
    (initialConfiguration machine) steps j

private theorem sum_crossingIndicators_le_one
    (bound fromHead toHead : Nat) :
    (∑ j : Fin bound,
      if CrossesWorkBoundary j.val fromHead toHead then 1 else 0) ≤ 1 := by
  classical
  rw [Finset.sum_boole]
  apply Finset.card_le_one.mpr
  intro j hj k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
  exact Fin.ext (crossesWorkBoundary_unique hj hk)

/-- Summed over the complete reachable boundary range, crossing counts of a
run from `config` total at most the number of transitions. -/
theorem sum_workBoundaryCrossingCountFrom_le_steps
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps : Nat) :
    (∑ j : Fin (steps + config.workHead),
      workBoundaryCrossingCountFrom machine input config steps j.val) ≤ steps := by
  classical
  simp only [workBoundaryCrossingCountFrom]
  rw [Finset.sum_comm]
  calc
    (∑ time : Fin steps,
        ∑ j : Fin (steps + config.workHead),
          if WorkBoundaryCrossingAtFrom machine input config time.val j.val
            then 1 else 0) ≤
        ∑ _time : Fin steps, 1 := by
      apply Finset.sum_le_sum
      intro time _
      exact sum_crossingIndicators_le_one
        (steps + config.workHead)
        (workHeadTrajectoryFrom machine input config time.val)
        (workHeadTrajectoryFrom machine input config (time.val + 1))
    _ = steps := by simp

/-- In a blank-start run the complete reachable boundary range is `Fin steps`. -/
theorem sum_workBoundaryCrossingCount_le_steps
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    (∑ j : Fin steps, workBoundaryCrossingCount machine input steps j.val) ≤
      steps := by
  simpa [workBoundaryCrossingCount, initialConfiguration] using
    (sum_workBoundaryCrossingCountFrom_le_steps machine input
      (initialConfiguration machine) steps)

/-- Actual blank-start work-head crossings instantiate the canonical-boundary
charging lemma at every positive scale `b`. -/
theorem sum_canonicalWorkBoundaryCrossings_le_div
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) :
    (∑ i : Fin (steps / b),
      workBoundaryCrossingCount machine input steps
        (canonicalBoundary hb
          (fun j : Fin steps =>
            workBoundaryCrossingCount machine input steps j.val) i).val) ≤
      steps / b := by
  exact sum_canonicalBoundary_le_div hb
    (fun j : Fin steps => workBoundaryCrossingCount machine input steps j.val)
    (sum_workBoundaryCrossingCount_le_steps machine input steps)

end OneTapeMagnification
end Frontier
end Pnp4
