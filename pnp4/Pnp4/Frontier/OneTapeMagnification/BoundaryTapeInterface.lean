import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.WorkHeadCrossings

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact finite work-tape interfaces

A blank-start run lasting at most `T` transitions can write only cells
`0, ..., T - 1`.  This file therefore records cells `0, ..., T` in a finite
Boolean vector, proves that extending the vector by blanks reconstructs the
entire work tape exactly, and packages that vector together with the control
state and both head positions.

The resulting boundary interface is sufficient to restart and glue an exact
suffix of the deterministic computation.  It is deliberately the coarse,
lossless interface: its work-tape component alone has `2^(T+1)` possible
values.  No small-width branching program, rectangle decomposition, or
compression of this valuation is claimed here.
-/

/-- The complete work-tape prefix through cell `T`. -/
abbrev BoundedWorkTape (T : Nat) := Fin (T + 1) → Bool

namespace BoundedWorkTape

/-- The carrier contains every Boolean valuation of the represented prefix.
This is a cardinality statement about the coarse interface carrier, not a
lower bound on the number of interfaces reachable by one fixed machine. -/
theorem card (T : Nat) :
    Fintype.card (BoundedWorkTape T) = 2 ^ (T + 1) := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Restrict an infinite work tape to cells `0, ..., T`. -/
def restrict (T : Nat) (tape : WorkTape) : BoundedWorkTape T :=
  fun i => tape i.val

/-- Extend a bounded tape by the blank symbol outside its represented prefix. -/
def extend (T : Nat) (tape : BoundedWorkTape T) : WorkTape :=
  fun i => if h : i < T + 1 then tape ⟨i, h⟩ else false

/-- Update one represented cell. -/
def write {T : Nat} (tape : BoundedWorkTape T) (head : Fin (T + 1))
    (value : Bool) : BoundedWorkTape T :=
  fun i => if i = head then value else tape i

@[simp]
theorem restrict_extend (T : Nat) (tape : BoundedWorkTape T) :
    restrict T (extend T tape) = tape := by
  funext i
  simp [restrict, extend]

@[simp]
theorem write_same {T : Nat} (tape : BoundedWorkTape T)
    (head : Fin (T + 1)) (value : Bool) :
    write tape head value head = value := by
  simp [write]

theorem write_of_ne {T : Nat} (tape : BoundedWorkTape T)
    (head other : Fin (T + 1)) (value : Bool) (h : other ≠ head) :
    write tape head value other = tape other := by
  simp [write, h]

/-- Restriction commutes exactly with a write whose head is represented. -/
theorem restrict_workTape_write {T : Nat} (tape : WorkTape)
    (head : Fin (T + 1)) (value : Bool) :
    restrict T (WorkTape.write tape head.val value) =
      write (restrict T tape) head value := by
  funext i
  by_cases h : i = head
  · subst i
    simp [restrict, write, WorkTape.write]
  · have hval : i.val ≠ head.val := by
      intro hEq
      exact h (Fin.ext hEq)
    simp [restrict, write, WorkTape.write, h, hval]

end BoundedWorkTape

/-- The tape is blank strictly above the represented endpoint `T`. -/
def WorkTapeBlankAbove (T : Nat) (tape : WorkTape) : Prop :=
  ∀ cell, T < cell → tape cell = false

/-- Blank extension is a left inverse on tapes that are blank above `T`. -/
theorem BoundedWorkTape.extend_restrict_of_blankAbove
    {T : Nat} {tape : WorkTape} (hBlank : WorkTapeBlankAbove T tape) :
    BoundedWorkTape.extend T (BoundedWorkTape.restrict T tape) = tape := by
  funext cell
  by_cases hcell : cell < T + 1
  · simp [BoundedWorkTape.extend, BoundedWorkTape.restrict, hcell]
  · have hAbove : T < cell := by omega
    simp [BoundedWorkTape.extend, hcell, hBlank cell hAbove]

/-- A step writes no cell other than the current work-head cell. -/
theorem workTape_step_eq_of_ne
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (cell : Nat)
    (hcell : cell ≠ config.workHead) :
    (step machine input config).workTape cell = config.workTape cell := by
  unfold step
  split
  · rfl
  · simp [applyInstruction, WorkTape.write, hcell]

/-- During `steps` transitions from `config`, no cell at or to the right of
`config.workHead + steps` can be modified. -/
theorem runFrom_workTape_eq_of_initial_add_steps_le
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps cell : Nat)
    (hcell : config.workHead + steps ≤ cell) :
    (runFrom machine input config steps).workTape cell = config.workTape cell := by
  induction steps generalizing config with
  | zero => simp
  | succ steps ih =>
      rw [runFrom_succ]
      calc
        (runFrom machine input (step machine input config) steps).workTape cell =
            (step machine input config).workTape cell := by
          apply ih
          have hStep := workHead_step_le_succ machine input config
          omega
        _ = config.workTape cell := by
          apply workTape_step_eq_of_ne
          omega

/-- In a blank-start run, every cell whose index is at least the elapsed time
is still blank.  The endpoint is included because the first `time` writes
occur from head positions strictly below `time`. -/
theorem run_workTape_eq_blank_of_time_le_cell
    (machine : DeterministicMachine) (input : List Bool) (time cell : Nat)
    (hcell : time ≤ cell) :
    (run machine input time).workTape cell = false := by
  simpa [run, initialConfiguration, WorkTape.blank] using
    (runFrom_workTape_eq_of_initial_add_steps_le machine input
      (initialConfiguration machine) time cell (by
        change 0 + time ≤ cell
        simpa using hcell))

/-- Every blank-start configuration at time at most `T` has no nonblank work
cell outside the finite prefix through `T`. -/
theorem run_workTape_blankAbove_of_time_le
    (machine : DeterministicMachine) (input : List Bool) {time T : Nat}
    (htime : time ≤ T) :
    WorkTapeBlankAbove T (run machine input time).workTape := by
  intro cell hAbove
  apply run_workTape_eq_blank_of_time_le_cell machine input
  omega

/-- One input-head step advances by at most one cell. -/
theorem inputHead_step_le_succ_for_interface
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) :
    (step machine input config).inputHead ≤ config.inputHead + 1 := by
  rcases inputHead_step_cases machine input config with h | h <;> omega

/-- The blank-start input head is bounded by elapsed time. -/
theorem inputHead_run_le_time_for_interface
    (machine : DeterministicMachine) (input : List Bool) (time : Nat) :
    (run machine input time).inputHead ≤ time := by
  change (runFrom machine input (initialConfiguration machine) time).inputHead ≤ time
  have hGeneral : ∀ (config : Configuration machine.State) (steps : Nat),
      (runFrom machine input config steps).inputHead ≤ config.inputHead + steps := by
    intro config steps
    induction steps generalizing config with
    | zero => simp
    | succ steps ih =>
        rw [runFrom_succ]
        calc
          (runFrom machine input (step machine input config) steps).inputHead ≤
              (step machine input config).inputHead + steps := ih _
          _ ≤ (config.inputHead + 1) + steps :=
            Nat.add_le_add_right
              (inputHead_step_le_succ_for_interface machine input config) steps
          _ = config.inputHead + Nat.succ steps := by omega
  simpa [initialConfiguration] using
    (hGeneral (initialConfiguration machine) time)

/-- A lossless finite configuration interface for a horizon `T`.

The two heads and every work cell through `T` are represented exactly. -/
structure BoundaryTapeInterface (State : Type) (T : Nat) where
  state : State
  inputHead : Fin (T + 1)
  workHead : Fin (T + 1)
  workTape : BoundedWorkTape T
deriving Fintype

/-- The coarse interface is equivalent to the direct product of its four
fields.  This equivalence is used only to count the full carrier. -/
def boundaryTapeInterfaceEquiv (State : Type) (T : Nat) :
    BoundaryTapeInterface State T ≃
      State × Fin (T + 1) × Fin (T + 1) × BoundedWorkTape T where
  toFun interface :=
    (interface.state, interface.inputHead, interface.workHead, interface.workTape)
  invFun fields :=
    { state := fields.1
      inputHead := fields.2.1
      workHead := fields.2.2.1
      workTape := fields.2.2.2 }
  left_inv interface := by cases interface; rfl
  right_inv fields := by rcases fields with ⟨state, inputHead, workHead, workTape⟩; rfl

/-- Exact cardinality of the full coarse interface carrier.  In particular,
the formula counts all tape valuations, including ones unreachable in a
particular run. -/
theorem card_boundaryTapeInterface (State : Type) [Fintype State] (T : Nat) :
    Fintype.card (BoundaryTapeInterface State T) =
      Fintype.card State * (T + 1) * (T + 1) * 2 ^ (T + 1) := by
  rw [Fintype.card_congr (boundaryTapeInterfaceEquiv State T)]
  simp [Fintype.card_prod, Nat.mul_assoc]

/-- The machine's finite state enumeration makes the complete interface type
finite for each horizon. -/
noncomputable def boundaryTapeInterfaceFintype
    (machine : DeterministicMachine) (T : Nat) :
    Fintype (BoundaryTapeInterface machine.State T) := by
  letI : Fintype machine.State := machine.stateFintype
  exact inferInstance

/-- Machine-specialized carrier count using the finite enumeration stored in
the machine. -/
theorem card_machineBoundaryTapeInterface
    (machine : DeterministicMachine) (T : Nat) :
    letI : Fintype machine.State := machine.stateFintype
    Fintype.card (BoundaryTapeInterface machine.State T) =
      Fintype.card machine.State * (T + 1) * (T + 1) * 2 ^ (T + 1) := by
  letI : Fintype machine.State := machine.stateFintype
  exact card_boundaryTapeInterface machine.State T

/-- Decode an interface by extending its bounded work tape with blanks. -/
def BoundaryTapeInterface.decode {State : Type} {T : Nat}
    (interface : BoundaryTapeInterface State T) : Configuration State where
  state := interface.state
  inputHead := interface.inputHead.val
  workHead := interface.workHead.val
  workTape := BoundedWorkTape.extend T interface.workTape

/-- Extract the exact finite interface at a time within the horizon. -/
def boundaryTapeInterfaceAt (machine : DeterministicMachine)
    (input : List Bool) (T : Nat) (time : Fin (T + 1)) :
    BoundaryTapeInterface machine.State T :=
  let config := run machine input time.val
  { state := config.state
    inputHead :=
      ⟨config.inputHead,
        Nat.lt_succ_of_le ((inputHead_run_le_time_for_interface
          machine input time.val).trans (Nat.le_of_lt_succ time.isLt))⟩
    workHead :=
      ⟨config.workHead,
        Nat.lt_succ_of_le ((workHeadTrajectory_le_time
          machine input time.val).trans (Nat.le_of_lt_succ time.isLt))⟩
    workTape := BoundedWorkTape.restrict T config.workTape }

/-- The finite interface reconstructs the entire blank-start configuration,
not merely the cells that it explicitly stores. -/
theorem decode_boundaryTapeInterfaceAt_eq_run
    (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (time : Fin (T + 1)) :
    (boundaryTapeInterfaceAt machine input T time).decode =
      run machine input time.val := by
  let config := run machine input time.val
  have hTape : BoundedWorkTape.extend T
      (BoundedWorkTape.restrict T config.workTape) = config.workTape :=
    BoundedWorkTape.extend_restrict_of_blankAbove
      (run_workTape_blankAbove_of_time_le machine input
        (Nat.le_of_lt_succ time.isLt))
  change
    { state := config.state
      inputHead := config.inputHead
      workHead := config.workHead
      workTape := BoundedWorkTape.extend T
        (BoundedWorkTape.restrict T config.workTape) } = config
  rw [hTape]

/-- Exact semigroup law for deterministic execution from an arbitrary
configuration. -/
theorem runFrom_add
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (firstSteps suffix : Nat) :
    runFrom machine input config (firstSteps + suffix) =
      runFrom machine input (runFrom machine input config firstSteps) suffix := by
  induction suffix with
  | zero => simp
  | succ suffix ih =>
      rw [show firstSteps + Nat.succ suffix = (firstSteps + suffix) + 1 by omega,
        runFrom_succ_eq_step_runFrom,
        runFrom_succ_eq_step_runFrom, ih]

/-- Gluing through the exact boundary interface reproduces every suffix of
the original run.  The immutable input is intentionally shared on both sides. -/
theorem run_split_through_boundaryTapeInterface
    (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (cut : Fin (T + 1)) (suffix : Nat) :
    run machine input (cut.val + suffix) =
      runFrom machine input
        (boundaryTapeInterfaceAt machine input T cut).decode suffix := by
  rw [decode_boundaryTapeInterfaceAt_eq_run]
  exact runFrom_add machine input (initialConfiguration machine) cut.val suffix

/-- Consecutive extracted interfaces are compatible after decoding with one
actual machine step. -/
theorem boundaryTapeInterfaceAt_succ_compatible
    (machine : DeterministicMachine) (input : List Bool)
    {T : Nat} (time : Fin T) :
    (boundaryTapeInterfaceAt machine input T
        ⟨time.val + 1, by omega⟩).decode =
      step machine input
        (boundaryTapeInterfaceAt machine input T
          ⟨time.val, by omega⟩).decode := by
  rw [decode_boundaryTapeInterfaceAt_eq_run,
    decode_boundaryTapeInterfaceAt_eq_run]
  exact runFrom_succ_eq_step_runFrom machine input
    (initialConfiguration machine) time.val

end OneTapeMagnification
end Frontier
end Pnp4
