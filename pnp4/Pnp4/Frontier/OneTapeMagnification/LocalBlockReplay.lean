import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.BoundaryTapeInterface

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact replay inside a consecutive work-tape slab

This file isolates the machine-level locality fact needed before a Viola-style
replay argument can be attempted.  A slab with base `base` and width `width`
stores exactly the work cells

`base, base + 1, ..., base + width - 1`.

If two configurations have the same control state and head positions, see the
same current input symbol, and agree on a slab containing the scanned work
cell, then one deterministic nonhalting transition has the same control/head
result on both sides and leaves the two slab restrictions equal.  The write is
performed at the old head, hence inside the slab.  The new work head is allowed
to leave the slab; another replay step then requires a fresh inside-slab
hypothesis.

The finite-run theorem below makes the exact induction invariant explicit:
before every replayed transition the first work head is inside the slab, and
the two runs see the same current input symbol.  No branching-program width,
transcript count, or compression statement is asserted.
-/

/-- A Boolean valuation of a consecutive work-tape slab of length `width`. -/
abbrev WorkSlab (width : Nat) := Fin width → Bool

/-- Cell `i` of a slab based at `base` denotes absolute work-tape cell
`base + i`. -/
def workSlabCell (base : Nat) {width : Nat} (i : Fin width) : Nat :=
  base + i.val

/-- Restrict an infinite work tape to one consecutive finite slab. -/
def restrictWorkSlab (base width : Nat) (tape : WorkTape) : WorkSlab width :=
  fun i => tape (workSlabCell base i)

/-- Update one cell of a finite slab. -/
def writeWorkSlab {width : Nat} (tape : WorkSlab width) (head : Fin width)
    (value : Bool) : WorkSlab width :=
  fun i => if i = head then value else tape i

/-- An absolute work-tape cell belongs to the half-open slab
`[base, base + width)`. -/
def WorkCellInSlab (base width cell : Nat) : Prop :=
  base ≤ cell ∧ cell < base + width

/-- The finite index of an absolute cell known to lie in the slab. -/
def workCellIndex {base width cell : Nat}
    (hcell : WorkCellInSlab base width cell) : Fin width :=
  ⟨cell - base, by
    unfold WorkCellInSlab at hcell
    omega⟩

@[simp]
theorem workSlabCell_workCellIndex {base width cell : Nat}
    (hcell : WorkCellInSlab base width cell) :
    workSlabCell base (workCellIndex hcell) = cell := by
  change base + (cell - base) = cell
  unfold WorkCellInSlab at hcell
  omega

@[simp]
theorem restrictWorkSlab_apply_workCellIndex {base width cell : Nat}
    (tape : WorkTape) (hcell : WorkCellInSlab base width cell) :
    restrictWorkSlab base width tape (workCellIndex hcell) = tape cell := by
  simp [restrictWorkSlab]

@[simp]
theorem writeWorkSlab_same {width : Nat} (tape : WorkSlab width)
    (head : Fin width) (value : Bool) :
    writeWorkSlab tape head value head = value := by
  simp [writeWorkSlab]

theorem writeWorkSlab_of_ne {width : Nat} (tape : WorkSlab width)
    (head other : Fin width) (value : Bool) (h : other ≠ head) :
    writeWorkSlab tape head value other = tape other := by
  simp [writeWorkSlab, h]

/-- Restricting an arbitrary work-tape write has the expected pointwise
description, whether or not the written cell belongs to the slab. -/
theorem restrictWorkSlab_workTape_write_apply
    (base width : Nat) (tape : WorkTape) (head : Nat) (value : Bool)
    (i : Fin width) :
    restrictWorkSlab base width (WorkTape.write tape head value) i =
      if workSlabCell base i = head then value
      else restrictWorkSlab base width tape i := by
  rfl

/-- Restriction commutes exactly with a write whose cell lies in the slab. -/
theorem restrictWorkSlab_workTape_write_of_mem
    {base width head : Nat} (tape : WorkTape) (value : Bool)
    (hhead : WorkCellInSlab base width head) :
    restrictWorkSlab base width (WorkTape.write tape head value) =
      writeWorkSlab (restrictWorkSlab base width tape)
        (workCellIndex hhead) value := by
  funext i
  by_cases hi : i = workCellIndex hhead
  · subst i
    simp [WorkTape.write]
  · have hcell : workSlabCell base i ≠ head := by
      intro hEq
      apply hi
      apply Fin.ext
      have hbase : base ≤ head := hhead.1
      simp only [workSlabCell] at hEq
      simp only [workCellIndex]
      omega
    simp [restrictWorkSlab_workTape_write_apply, writeWorkSlab, hi, hcell]

/-- A write outside the slab does not change its restriction. -/
theorem restrictWorkSlab_workTape_write_of_not_mem
    {base width head : Nat} (tape : WorkTape) (value : Bool)
    (hhead : ¬ WorkCellInSlab base width head) :
    restrictWorkSlab base width (WorkTape.write tape head value) =
      restrictWorkSlab base width tape := by
  funext i
  rw [restrictWorkSlab_workTape_write_apply]
  split
  · rename_i hEq
    exfalso
    apply hhead
    constructor
    · unfold workSlabCell at hEq
      omega
    · have hi := i.isLt
      unfold workSlabCell at hEq
      omega
  · rfl

/-- Two configurations have the same finite information visible to a replay
inside a fixed work slab.  Their work tapes may differ outside the slab. -/
def SameOnWorkSlab {State : Type} (base width : Nat)
    (left right : Configuration State) : Prop :=
  left.state = right.state ∧
    left.inputHead = right.inputHead ∧
    left.workHead = right.workHead ∧
    restrictWorkSlab base width left.workTape =
      restrictWorkSlab base width right.workTape

namespace SameOnWorkSlab

theorem refl {State : Type} (base width : Nat)
    (config : Configuration State) :
    SameOnWorkSlab base width config config := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem symm {State : Type} {base width : Nat}
    {left right : Configuration State}
    (h : SameOnWorkSlab base width left right) :
    SameOnWorkSlab base width right left := by
  rcases h with ⟨hstate, hinput, hwork, htape⟩
  exact ⟨hstate.symm, hinput.symm, hwork.symm, htape.symm⟩

theorem trans {State : Type} {base width : Nat}
    {first second third : Configuration State}
    (h₁₂ : SameOnWorkSlab base width first second)
    (h₂₃ : SameOnWorkSlab base width second third) :
    SameOnWorkSlab base width first third := by
  rcases h₁₂ with ⟨hstate₁, hinput₁, hwork₁, htape₁⟩
  rcases h₂₃ with ⟨hstate₂, hinput₂, hwork₂, htape₂⟩
  exact ⟨hstate₁.trans hstate₂, hinput₁.trans hinput₂,
    hwork₁.trans hwork₂, htape₁.trans htape₂⟩

end SameOnWorkSlab

/-- Agreement on a slab containing the common head determines the work symbol
read by the two configurations. -/
theorem workTape_read_eq_of_sameOnWorkSlab
    {State : Type} {base width : Nat}
    {left right : Configuration State}
    (hsame : SameOnWorkSlab base width left right)
    (hinside : WorkCellInSlab base width left.workHead) :
    WorkTape.read left.workTape left.workHead =
      WorkTape.read right.workTape right.workHead := by
  rcases hsame with ⟨_, _, hwork, htape⟩
  have hAt := congrFun htape (workCellIndex hinside)
  simpa [WorkTape.read, hwork] using hAt

/-- Applying the same instruction preserves slab agreement when the old
common work head lies inside the slab.  The new work head may lie outside. -/
theorem applyInstruction_sameOnWorkSlab
    {State : Type} {base width : Nat}
    {left right : Configuration State}
    (instruction : Instruction State)
    (hsame : SameOnWorkSlab base width left right)
    (hinside : WorkCellInSlab base width left.workHead) :
    SameOnWorkSlab base width
      (applyInstruction left instruction)
      (applyInstruction right instruction) := by
  rcases hsame with ⟨hstate, hinput, hwork, htape⟩
  constructor
  · rfl
  constructor
  · simp [applyInstruction, hinput]
  constructor
  · simp [applyInstruction, hwork]
  · dsimp only [applyInstruction]
    rw [restrictWorkSlab_workTape_write_of_mem left.workTape
      instruction.write hinside]
    have hinsideRight : WorkCellInSlab base width right.workHead := by
      simpa [hwork] using hinside
    rw [restrictWorkSlab_workTape_write_of_mem right.workTape
      instruction.write hinsideRight]
    have hindex : workCellIndex hinside = workCellIndex hinsideRight := by
      apply Fin.ext
      simp only [workCellIndex]
      omega
    rw [hindex, htape]

/-- Exact one-step local replay for a nonhalting configuration.  Equal current
input observations and equal slab-local work observations force the same
instruction; the shared write then preserves slab agreement. -/
theorem step_sameOnWorkSlab_of_nonhalting
    (machine : DeterministicMachine)
    {leftInput rightInput : List Bool} {base width : Nat}
    {left right : Configuration machine.State}
    (hsame : SameOnWorkSlab base width left right)
    (hinside : WorkCellInSlab base width left.workHead)
    (hinputSymbol :
      readOnlySymbol leftInput left.inputHead =
        readOnlySymbol rightInput right.inputHead)
    (hnonhalting : machine.halt left.state = none) :
    SameOnWorkSlab base width
      (step machine leftInput left) (step machine rightInput right) := by
  rcases hsame with ⟨hstate, hinputHead, hworkHead, htape⟩
  have hsame : SameOnWorkSlab base width left right :=
    ⟨hstate, hinputHead, hworkHead, htape⟩
  have hworkSymbol := workTape_read_eq_of_sameOnWorkSlab hsame hinside
  have hnonhaltingRight : machine.halt right.state = none := by
    simpa [← hstate] using hnonhalting
  have hinstruction :
      machine.transition left.state
          (readOnlySymbol leftInput left.inputHead)
          (WorkTape.read left.workTape left.workHead) =
        machine.transition right.state
          (readOnlySymbol rightInput right.inputHead)
          (WorkTape.read right.workTape right.workHead) := by
    rw [hstate, hinputSymbol, hworkSymbol]
  simp only [step, hnonhalting, hnonhaltingRight]
  rw [hinstruction]
  exact applyInstruction_sameOnWorkSlab
    (machine.transition right.state
      (readOnlySymbol rightInput right.inputHead)
      (WorkTape.read right.workTape right.workHead)) hsame hinside

/-- The same local replay statement also covers halted stuttering steps.  In
that case the current input symbol is irrelevant; the common-state hypothesis
ensures that both configurations stutter. -/
theorem step_sameOnWorkSlab
    (machine : DeterministicMachine)
    {leftInput rightInput : List Bool} {base width : Nat}
    {left right : Configuration machine.State}
    (hsame : SameOnWorkSlab base width left right)
    (hinside : WorkCellInSlab base width left.workHead)
    (hinputSymbol :
      readOnlySymbol leftInput left.inputHead =
        readOnlySymbol rightInput right.inputHead) :
    SameOnWorkSlab base width
      (step machine leftInput left) (step machine rightInput right) := by
  rcases hsame with ⟨hstate, hinputHead, hworkHead, htape⟩
  have hsame : SameOnWorkSlab base width left right :=
    ⟨hstate, hinputHead, hworkHead, htape⟩
  cases hhalt : machine.halt left.state with
  | none =>
      exact step_sameOnWorkSlab_of_nonhalting machine hsame hinside
        hinputSymbol hhalt
  | some outcome =>
      have hhaltRight : machine.halt right.state = some outcome := by
        simpa [← hstate] using hhalt
      rw [step_of_halted machine leftInput left outcome hhalt,
        step_of_halted machine rightInput right outcome hhaltRight]
      exact hsame

/-- Exact hypotheses required to replay a finite run inside one slab.  The
head is required to be inside before every transition, not after the final
transition, so the last step is allowed to exit the slab. -/
def WorkSlabReplayCompatibleThrough
    (machine : DeterministicMachine)
    (leftInput rightInput : List Bool) (base width : Nat)
    (left right : Configuration machine.State) (steps : Nat) : Prop :=
  ∀ time, time < steps →
    WorkCellInSlab base width
        (runFrom machine leftInput left time).workHead ∧
      readOnlySymbol leftInput
          (runFrom machine leftInput left time).inputHead =
        readOnlySymbol rightInput
          (runFrom machine rightInput right time).inputHead

/-- Finite exact replay under the explicit per-time locality invariant.  This
is an induction of the one-step theorem, not a small-width simulation claim. -/
theorem runFrom_sameOnWorkSlab
    (machine : DeterministicMachine)
    {leftInput rightInput : List Bool} {base width : Nat}
    {left right : Configuration machine.State} {steps : Nat}
    (hsame : SameOnWorkSlab base width left right)
    (hcompatible : WorkSlabReplayCompatibleThrough machine
      leftInput rightInput base width left right steps) :
    SameOnWorkSlab base width
      (runFrom machine leftInput left steps)
      (runFrom machine rightInput right steps) := by
  induction steps with
  | zero => simpa using hsame
  | succ steps ih =>
      have hprefix : WorkSlabReplayCompatibleThrough machine
          leftInput rightInput base width left right steps := by
        intro time htime
        exact hcompatible time (by omega)
      have hsameAt := ih hprefix
      have hlast := hcompatible steps (by omega)
      rw [runFrom_succ_eq_step_runFrom, runFrom_succ_eq_step_runFrom]
      exact step_sameOnWorkSlab machine hsameAt hlast.1 hlast.2

/-- For two runs on the same immutable input, equality of input-head positions
from `SameOnWorkSlab` supplies the per-step input-observation agreement.  Thus
only the inside-slab condition must be stated separately. -/
theorem runFrom_sameOnWorkSlab_same_input
    (machine : DeterministicMachine) (input : List Bool)
    {base width : Nat} {left right : Configuration machine.State} {steps : Nat}
    (hsame : SameOnWorkSlab base width left right)
    (hinside : ∀ time, time < steps →
      WorkCellInSlab base width
        (runFrom machine input left time).workHead) :
    SameOnWorkSlab base width
      (runFrom machine input left steps)
      (runFrom machine input right steps) := by
  induction steps with
  | zero => simpa using hsame
  | succ steps ih =>
      have hinsidePrefix : ∀ time, time < steps →
          WorkCellInSlab base width
            (runFrom machine input left time).workHead := by
        intro time htime
        exact hinside time (by omega)
      have hsameAt := ih hinsidePrefix
      rw [runFrom_succ_eq_step_runFrom, runFrom_succ_eq_step_runFrom]
      apply step_sameOnWorkSlab machine hsameAt (hinside steps (by omega))
      exact congrArg (fun head => readOnlySymbol input head) hsameAt.2.1

end OneTapeMagnification
end Frontier
end Pnp4
