import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.InputCacheNormalization
import Pnp4.Frontier.OneTapeMagnification.LocalBlockStateCount

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A finite local step for the cached-input machine

This file turns the already-counted `LocalReplayState` into one executable
local transition.  The transition is parameterized by the absolute base of a
width-`w` work slab and by the next unread input symbol.  It returns a new
local state exactly when the current state is nonhalting, the successor input
head is still at most the horizon `H`, and the successor work head is still
inside the same slab.

All other cases are explicit finite results: an actual machine halt, a work
head exit, or an input-horizon violation.  Thus this module does not silently
totalize a failed replay step.  It also does not construct or claim a
read-once/query program.
-/

/-- The interval predicate used by the executable local step is decidable. -/
instance workCellInSlabDecidable (base width cell : Nat) :
    Decidable (WorkCellInSlab base width cell) := by
  unfold WorkCellInSlab
  infer_instance

/-- Explicit finite result of attempting one local cached-machine step. -/
inductive FiniteLocalStepResult (State : Type) (H w : Nat) where
  | inside (state : LocalReplayState State H w)
  | halted (outcome : HaltOutcome)
  | workHeadExit
  | inputHorizonExceeded
deriving Fintype

/-- The result type is a disjoint sum of the next-state carrier, the two
machine outcomes, and two explicit replay failures. -/
def finiteLocalStepResultEquiv (State : Type) (H w : Nat) :
    FiniteLocalStepResult State H w ≃
      Sum (LocalReplayState State H w) (Sum HaltOutcome Bool) where
  toFun
    | .inside state => .inl state
    | .halted outcome => .inr (.inl outcome)
    | .workHeadExit => .inr (.inr false)
    | .inputHorizonExceeded => .inr (.inr true)
  invFun
    | .inl state => .inside state
    | .inr (.inl outcome) => .halted outcome
    | .inr (.inr false) => .workHeadExit
    | .inr (.inr true) => .inputHorizonExceeded
  left_inv result := by cases result <;> rfl
  right_inv result := by
    rcases result with state | outcomeOrFailure
    · rfl
    · rcases outcomeOrFailure with outcome | failure
      · rfl
      · cases failure <;> rfl

/-- Exact cardinality of the local result carrier. -/
theorem card_finiteLocalStepResult (State : Type) [Fintype State]
    (H w : Nat) :
    Fintype.card (FiniteLocalStepResult State H w) =
      Fintype.card State * (H + 1) * w * 2 ^ w + 4 := by
  rw [Fintype.card_congr (finiteLocalStepResultEquiv State H w)]
  rw [Fintype.card_sum, Fintype.card_sum]
  rw [Fintype.card_congr (localReplayStateEquiv State H w)]
  have hOutcomes : Fintype.card HaltOutcome = 2 := by decide
  simp [hOutcomes, Nat.mul_assoc]

/-- Finite endpoint retained by a permitted final step.  Unlike
`LocalReplayState`, the work head is absolute: the final transition may have
left the slab.  Both heads are still explicitly bounded by the horizon. -/
structure FiniteLocalFinalState (State : Type) (H w : Nat) where
  control : State
  inputHead : Fin (H + 1)
  workHead : Fin (H + 1)
  workSlab : WorkSlab w
deriving Fintype

/-- Product presentation of the retained final endpoint. -/
def finiteLocalFinalStateEquiv (State : Type) (H w : Nat) :
    FiniteLocalFinalState State H w ≃
      State × Fin (H + 1) × Fin (H + 1) × WorkSlab w where
  toFun state :=
    (state.control, state.inputHead, state.workHead, state.workSlab)
  invFun fields :=
    ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  left_inv state := by cases state; rfl
  right_inv fields := by
    rcases fields with ⟨control, inputHead, workHead, workSlab⟩
    rfl

/-- Exact cardinality of the retained final endpoint. -/
theorem card_finiteLocalFinalState (State : Type) [Fintype State]
    (H w : Nat) :
    Fintype.card (FiniteLocalFinalState State H w) =
      Fintype.card State * (H + 1) * (H + 1) * 2 ^ w := by
  rw [Fintype.card_congr (finiteLocalFinalStateEquiv State H w)]
  simp [Nat.mul_assoc]

/-- Explicit result of the final-step API.  A nonhalting step retains its
post-state even when its work head has left the slab.  Only failure of a head
to fit the declared absolute horizon discards that endpoint. -/
inductive FiniteLocalFinalStepResult (State : Type) (H w : Nat) where
  | stepped (state : FiniteLocalFinalState State H w)
  | halted (outcome : HaltOutcome)
  | inputHorizonExceeded
  | workHorizonExceeded
deriving Fintype

/-- Disjoint-sum presentation of the final-step result. -/
def finiteLocalFinalStepResultEquiv (State : Type) (H w : Nat) :
    FiniteLocalFinalStepResult State H w ≃
      Sum (FiniteLocalFinalState State H w) (Sum HaltOutcome Bool) where
  toFun
    | .stepped state => .inl state
    | .halted outcome => .inr (.inl outcome)
    | .inputHorizonExceeded => .inr (.inr false)
    | .workHorizonExceeded => .inr (.inr true)
  invFun
    | .inl state => .stepped state
    | .inr (.inl outcome) => .halted outcome
    | .inr (.inr false) => .inputHorizonExceeded
    | .inr (.inr true) => .workHorizonExceeded
  left_inv result := by cases result <;> rfl
  right_inv result := by
    rcases result with state | outcomeOrFailure
    · rfl
    · rcases outcomeOrFailure with outcome | failure
      · rfl
      · cases failure <;> rfl

/-- Exact cardinality of the final-step result carrier. -/
theorem card_finiteLocalFinalStepResult (State : Type) [Fintype State]
    (H w : Nat) :
    Fintype.card (FiniteLocalFinalStepResult State H w) =
      Fintype.card State * (H + 1) * (H + 1) * 2 ^ w + 4 := by
  rw [Fintype.card_congr (finiteLocalFinalStepResultEquiv State H w)]
  rw [Fintype.card_sum, Fintype.card_sum]
  rw [card_finiteLocalFinalState]
  have hOutcomes : Fintype.card HaltOutcome = 2 := by decide
  simp [hOutcomes]

/-- Extend a finite slab to a full work tape by filling cells outside the
slab with blanks.  This canonical extension is used only to state exact
correspondence with the global small-step semantics. -/
def materializeWorkSlab (base : Nat) {w : Nat} (slab : WorkSlab w) :
    WorkTape := fun cell =>
  if hcell : WorkCellInSlab base w cell then
    slab (workCellIndex hcell)
  else
    false

/-- Materialize a finite local state as a global configuration whose
out-of-slab cells are blank. -/
def materializeLocalReplayState {State : Type} {H w : Nat} (base : Nat)
    (state : LocalReplayState State H w) : Configuration State where
  state := state.control
  inputHead := state.inputHead.val
  workHead := base + state.relativeWorkHead.val
  workTape := materializeWorkSlab base state.workSlab

/-- Materialize a retained final endpoint.  Its absolute work head need not
belong to the slab; the slab still records the write performed at the old,
inside head. -/
def materializeFiniteLocalFinalState {State : Type} {H w : Nat} (base : Nat)
    (state : FiniteLocalFinalState State H w) : Configuration State where
  state := state.control
  inputHead := state.inputHead.val
  workHead := state.workHead.val
  workTape := materializeWorkSlab base state.workSlab

@[simp]
theorem materializeWorkSlab_at_relative {base w : Nat}
    (slab : WorkSlab w) (head : Fin w) :
    materializeWorkSlab base slab (base + head.val) = slab head := by
  have hcell : WorkCellInSlab base w (base + head.val) := by
    constructor <;> omega
  simp only [materializeWorkSlab, dif_pos hcell]
  congr 1
  apply Fin.ext
  simp only [workCellIndex]
  omega

@[simp]
theorem materializeLocalReplayState_work_read
    {State : Type} {H w base : Nat}
    (state : LocalReplayState State H w) :
    WorkTape.read (materializeLocalReplayState base state).workTape
        (materializeLocalReplayState base state).workHead =
      state.workSlab state.relativeWorkHead := by
  change materializeWorkSlab base state.workSlab
      (base + state.relativeWorkHead.val) =
    state.workSlab state.relativeWorkHead
  exact materializeWorkSlab_at_relative state.workSlab state.relativeWorkHead

/-- Updating the scanned local cell and then materializing is exactly the
same full-tape update as writing the corresponding absolute cell. -/
theorem materializeWorkSlab_write {base w : Nat}
    (slab : WorkSlab w) (head : Fin w) (value : Bool) :
    materializeWorkSlab base (writeWorkSlab slab head value) =
      WorkTape.write (materializeWorkSlab base slab)
        (base + head.val) value := by
  funext cell
  by_cases hcell : WorkCellInSlab base w cell
  · have hbase : base ≤ cell := hcell.1
    have hidx : workSlabCell base (workCellIndex hcell) = cell :=
      workSlabCell_workCellIndex hcell
    by_cases heq : workCellIndex hcell = head
    · have habsolute : cell = base + head.val := by
        subst heq
        simpa [workSlabCell] using hidx.symm
      subst cell
      rw [materializeWorkSlab_at_relative]
      simp [WorkTape.write]
    · have habsolute : cell ≠ base + head.val := by
        intro h
        apply heq
        apply Fin.ext
        simp only [workCellIndex]
        omega
      simp [materializeWorkSlab, hcell, writeWorkSlab, heq,
        WorkTape.write, habsolute]
  · have habsolute : cell ≠ base + head.val := by
      intro h
      apply hcell
      subst h
      constructor <;> omega
    simp [materializeWorkSlab, hcell, WorkTape.write, habsolute]

/-- Attempt one exact finite transition of the cached-input machine.

The current work symbol is read from the local slab.  In the successful case
all four finite fields are updated: cached control, bounded input head,
relative work head, and the slab write.  Failure priority is deterministic:
an input-horizon violation is reported before a simultaneous work-head exit.
-/
def finiteLocalCachedStep (machine : DeterministicMachine)
    (H w base : Nat) (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w) :
    FiniteLocalStepResult (cachedInputMachine machine).State H w :=
  match (cachedInputMachine machine).halt state.control with
  | some outcome => .halted outcome
  | none =>
      let instruction := cachedInputTransition machine state.control unread
        (state.workSlab state.relativeWorkHead)
      let nextInput := moveInputHead state.inputHead.val instruction.inputMove
      let nextWork := moveWorkHead (base + state.relativeWorkHead.val)
        instruction.workMove
      if hinput : nextInput < H + 1 then
        if hwork : WorkCellInSlab base w nextWork then
          .inside
            { control := instruction.nextState
              inputHead := ⟨nextInput, hinput⟩
              relativeWorkHead := workCellIndex hwork
              workSlab := writeWorkSlab state.workSlab
                state.relativeWorkHead instruction.write }
        else
          .workHeadExit
      else
        .inputHorizonExceeded

/-- The exact result-carrier size after specializing control to the cached
machine.  The cache has `1 + 3 * |Q|` control states. -/
theorem card_cachedFiniteLocalStepResult (machine : DeterministicMachine)
    (H w : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card
        (FiniteLocalStepResult (cachedInputMachine machine).State H w) =
      (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
          (H + 1) * w * 2 ^ w + 4 := by
  letI := (cachedInputMachine machine).stateFintype
  rw [card_finiteLocalStepResult]
  rw [cachedInputMachine_state_card]

/-- Attempt a permitted last transition of a local visit.

Unlike `finiteLocalCachedStep`, this API does not reject merely because the
successor work head leaves the current slab.  It retains the post control,
both bounded absolute head positions, and the slab after the write.  An
endpoint is rejected only when either absolute head exceeds `H`; input
horizon failure has deterministic priority if both bounds fail. -/
def finiteLocalCachedFinalStep (machine : DeterministicMachine)
    (H w base : Nat) (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w) :
    FiniteLocalFinalStepResult (cachedInputMachine machine).State H w :=
  match (cachedInputMachine machine).halt state.control with
  | some outcome => .halted outcome
  | none =>
      let instruction := cachedInputTransition machine state.control unread
        (state.workSlab state.relativeWorkHead)
      let nextInput := moveInputHead state.inputHead.val instruction.inputMove
      let nextWork := moveWorkHead (base + state.relativeWorkHead.val)
        instruction.workMove
      if hinput : nextInput < H + 1 then
        if hwork : nextWork < H + 1 then
          .stepped
            { control := instruction.nextState
              inputHead := ⟨nextInput, hinput⟩
              workHead := ⟨nextWork, hwork⟩
              workSlab := writeWorkSlab state.workSlab
                state.relativeWorkHead instruction.write }
        else
          .workHorizonExceeded
      else
        .inputHorizonExceeded

/-- Exact final-step result size for the cached machine. -/
theorem card_cachedFiniteLocalFinalStepResult
    (machine : DeterministicMachine) (H w : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card
        (FiniteLocalFinalStepResult
          (cachedInputMachine machine).State H w) =
      (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
          (H + 1) * (H + 1) * 2 ^ w + 4 := by
  letI := (cachedInputMachine machine).stateFintype
  rw [card_finiteLocalFinalStepResult]
  rw [cachedInputMachine_state_card]

/-- A successful local transition materializes to exactly one global
`step` of the cached-input machine.  The unread argument must be the symbol
seen at the materialized input-head position. -/
theorem finiteLocalCachedStep_inside_materialize
    (machine : DeterministicMachine) {H w base : Nat}
    (unread : ReadOnlySymbol)
    (state next :
      LocalReplayState (cachedInputMachine machine).State H w)
    (input : List Bool)
    (hunread :
      readOnlySymbol input state.inputHead.val = unread)
    (hstep :
      finiteLocalCachedStep machine H w base unread state =
        .inside next) :
    materializeLocalReplayState base next =
      step (cachedInputMachine machine) input
        (materializeLocalReplayState base state) := by
  unfold finiteLocalCachedStep at hstep
  split at hstep
  · contradiction
  · rename_i hnonhalting
    dsimp only at hstep
    split at hstep
    · rename_i hinput
      split at hstep
      · rename_i hwork
        cases hstep
        have hglobalStep :
            step (cachedInputMachine machine) input
                (materializeLocalReplayState base state) =
              applyInstruction (materializeLocalReplayState base state)
                (cachedInputTransition machine state.control unread
                  (state.workSlab state.relativeWorkHead)) := by
          unfold step
          change
            (match (cachedInputMachine machine).halt state.control with
            | some _ => materializeLocalReplayState base state
            | none =>
                applyInstruction (materializeLocalReplayState base state)
                  ((cachedInputMachine machine).transition state.control
                    (readOnlySymbol input state.inputHead.val)
                    (WorkTape.read
                      (materializeLocalReplayState base state).workTape
                      (materializeLocalReplayState base state).workHead))) = _
          rw [hnonhalting]
          change
            applyInstruction (materializeLocalReplayState base state)
                (cachedInputTransition machine state.control
                  (readOnlySymbol input state.inputHead.val)
                  (WorkTape.read
                    (materializeLocalReplayState base state).workTape
                    (materializeLocalReplayState base state).workHead)) = _
          rw [hunread, materializeLocalReplayState_work_read]
        rw [hglobalStep]
        have hhead := workSlabCell_workCellIndex hwork
        change base + (workCellIndex hwork).val = _ at hhead
        simp only [materializeLocalReplayState, applyInstruction]
        rw [hhead, materializeWorkSlab_write]
      · contradiction
    · contradiction

/-- A retained final endpoint exposes exactly the post-transition fields,
including the absolute work head even when it lies outside the slab. -/
theorem finiteLocalCachedFinalStep_stepped_endpoint
    (machine : DeterministicMachine) {H w base : Nat}
    (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (next : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (hstep :
      finiteLocalCachedFinalStep machine H w base unread state =
        .stepped next) :
    next.control =
        (cachedInputTransition machine state.control unread
          (state.workSlab state.relativeWorkHead)).nextState ∧
      next.inputHead.val =
        moveInputHead state.inputHead.val
          (cachedInputTransition machine state.control unread
            (state.workSlab state.relativeWorkHead)).inputMove ∧
      next.workHead.val =
        moveWorkHead (base + state.relativeWorkHead.val)
          (cachedInputTransition machine state.control unread
            (state.workSlab state.relativeWorkHead)).workMove ∧
      next.workSlab =
        writeWorkSlab state.workSlab state.relativeWorkHead
          (cachedInputTransition machine state.control unread
            (state.workSlab state.relativeWorkHead)).write := by
  unfold finiteLocalCachedFinalStep at hstep
  split at hstep
  · contradiction
  · dsimp only at hstep
    split at hstep
    · split at hstep
      · cases hstep
        exact ⟨rfl, rfl, rfl, rfl⟩
      · contradiction
    · contradiction

/-- A retained final endpoint is exactly the endpoint of one global cached
machine step.  This remains true when the successor work head is outside the
local slab: the old head, where the write occurs, was inside and the endpoint
stores the new absolute head separately. -/
theorem finiteLocalCachedFinalStep_stepped_materialize
    (machine : DeterministicMachine) {H w base : Nat}
    (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (next : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (input : List Bool)
    (hunread :
      readOnlySymbol input state.inputHead.val = unread)
    (hstep :
      finiteLocalCachedFinalStep machine H w base unread state =
        .stepped next) :
    materializeFiniteLocalFinalState base next =
      step (cachedInputMachine machine) input
        (materializeLocalReplayState base state) := by
  unfold finiteLocalCachedFinalStep at hstep
  split at hstep
  · contradiction
  · rename_i hnonhalting
    dsimp only at hstep
    split at hstep
    · split at hstep
      · cases hstep
        have hglobalStep :
            step (cachedInputMachine machine) input
                (materializeLocalReplayState base state) =
              applyInstruction (materializeLocalReplayState base state)
                (cachedInputTransition machine state.control unread
                  (state.workSlab state.relativeWorkHead)) := by
          unfold step
          change
            (match (cachedInputMachine machine).halt state.control with
            | some _ => materializeLocalReplayState base state
            | none =>
                applyInstruction (materializeLocalReplayState base state)
                  ((cachedInputMachine machine).transition state.control
                    (readOnlySymbol input state.inputHead.val)
                    (WorkTape.read
                      (materializeLocalReplayState base state).workTape
                      (materializeLocalReplayState base state).workHead))) = _
          rw [hnonhalting]
          change
            applyInstruction (materializeLocalReplayState base state)
                (cachedInputTransition machine state.control
                  (readOnlySymbol input state.inputHead.val)
                  (WorkTape.read
                    (materializeLocalReplayState base state).workTape
                    (materializeLocalReplayState base state).workHead)) = _
          rw [hunread, materializeLocalReplayState_work_read]
        rw [hglobalStep]
        simp only [materializeFiniteLocalFinalState,
          materializeLocalReplayState, applyInstruction]
        rw [materializeWorkSlab_write]
      · contradiction
    · contradiction

/-- Stay-move unread-symbol independence also holds for the endpoint-retaining
final-step API. -/
theorem finiteLocalCachedFinalStep_stay_independent
    (machine : DeterministicMachine) {H w base : Nat}
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (originalState : machine.State) (cached : ReadOnlySymbol)
    (hcontrol : state.control = some (originalState, cached))
    (unread₁ unread₂ : ReadOnlySymbol)
    (hStay :
      (machine.transition originalState cached
        (state.workSlab state.relativeWorkHead)).inputMove = .stay) :
    finiteLocalCachedFinalStep machine H w base unread₁ state =
      finiteLocalCachedFinalStep machine H w base unread₂ state := by
  have hinstruction := cachedInputTransition_stay_independent_general
    machine originalState cached
      (state.workSlab state.relativeWorkHead) unread₁ unread₂ hStay
  unfold finiteLocalCachedFinalStep
  rw [hcontrol]
  simp only [cachedInputMachine]
  split
  · rfl
  · rw [hinstruction]

/-- On a cached simulated state whose original input move is `stay`, the
entire finite local result is independent of the next unread symbol. -/
theorem finiteLocalCachedStep_stay_independent
    (machine : DeterministicMachine) {H w base : Nat}
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (originalState : machine.State) (cached : ReadOnlySymbol)
    (hcontrol : state.control = some (originalState, cached))
    (unread₁ unread₂ : ReadOnlySymbol)
    (hStay :
      (machine.transition originalState cached
        (state.workSlab state.relativeWorkHead)).inputMove = .stay) :
    finiteLocalCachedStep machine H w base unread₁ state =
      finiteLocalCachedStep machine H w base unread₂ state := by
  have hinstruction := cachedInputTransition_stay_independent_general
    machine originalState cached
      (state.workSlab state.relativeWorkHead) unread₁ unread₂ hStay
  unfold finiteLocalCachedStep
  rw [hcontrol]
  simp only [cachedInputMachine]
  split
  · rfl
  · rw [hinstruction]

end OneTapeMagnification
end Frontier
end Pnp4
