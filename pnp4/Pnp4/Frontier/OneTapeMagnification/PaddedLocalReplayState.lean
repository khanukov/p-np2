import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutBlockSlabs
import Pnp4.Frontier.OneTapeMagnification.FiniteLocalCachedStep

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Padding heterogeneous local replay states to one width

Advertised work blocks have widths that depend on the block, although every
such width is at most `2 * b`.  A layered branching program needs one carrier
at each layer rather than a different type for every block.  This file gives
the missing lossless embedding into a common width.

The added cells are blank.  Consequently padding preserves not only the
original slab coordinates but also the canonical full-tape materialization:
the original materialization was already blank outside its shorter slab.
-/

/-- The order-preserving inclusion of a shorter finite interval into a
longer one. -/
def padFin {w W : Nat} (h : w ≤ W) (i : Fin w) : Fin W :=
  ⟨i.val, i.isLt.trans_le h⟩

@[simp]
theorem padFin_val {w W : Nat} (h : w ≤ W) (i : Fin w) :
    (padFin h i).val = i.val := rfl

theorem padFin_injective {w W : Nat} (h : w ≤ W) :
    Function.Injective (padFin h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun k : Fin W => k.val) hij

/-- Pad a slab on the right, filling every unused coordinate with blank. -/
def padWorkSlab {w W : Nat} (_h : w ≤ W) (slab : WorkSlab w) :
    WorkSlab W := fun i =>
  if hi : i.val < w then slab ⟨i.val, hi⟩ else false

/-- Restrict a width-`W` slab to its first `w` coordinates. -/
def truncateWorkSlab {w W : Nat} (h : w ≤ W) (slab : WorkSlab W) :
    WorkSlab w := fun i => slab (padFin h i)

@[simp]
theorem padWorkSlab_at_padFin {w W : Nat} (h : w ≤ W)
    (slab : WorkSlab w) (i : Fin w) :
    padWorkSlab h slab (padFin h i) = slab i := by
  simp [padWorkSlab, padFin]

theorem padWorkSlab_eq_false_of_not_lt {w W : Nat} (h : w ≤ W)
    (slab : WorkSlab w) (i : Fin W) (hi : ¬ i.val < w) :
    padWorkSlab h slab i = false := by
  simp [padWorkSlab, hi]

@[simp]
theorem truncateWorkSlab_padWorkSlab {w W : Nat} (h : w ≤ W)
    (slab : WorkSlab w) :
    truncateWorkSlab h (padWorkSlab h slab) = slab := by
  funext i
  exact padWorkSlab_at_padFin h slab i

theorem padWorkSlab_injective {w W : Nat} (h : w ≤ W) :
    Function.Injective (padWorkSlab h) := by
  intro left right heq
  have hrestricted := congrArg (truncateWorkSlab h) heq
  simpa using hrestricted

/-- Padding commutes with a write to an original coordinate. -/
theorem padWorkSlab_write {w W : Nat} (h : w ≤ W)
    (slab : WorkSlab w) (head : Fin w) (value : Bool) :
    padWorkSlab h (writeWorkSlab slab head value) =
      writeWorkSlab (padWorkSlab h slab) (padFin h head) value := by
  funext i
  by_cases heq : i = padFin h head
  · subst i
    simp
  · by_cases hi : i.val < w
    · let small : Fin w := ⟨i.val, hi⟩
      have hs : small ≠ head := by
        intro hsmall
        apply heq
        apply Fin.ext
        change i.val = head.val
        have hval := congrArg (fun k : Fin w => k.val) hsmall
        simpa [small] using hval
      simp [padWorkSlab, hi, writeWorkSlab, heq, hs, small]
    · simp [padWorkSlab, hi, writeWorkSlab, heq]

/-- Pad all width-dependent fields of a local replay state. -/
def padLocalReplayState {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : LocalReplayState State H w) : LocalReplayState State H W where
  control := state.control
  inputHead := state.inputHead
  relativeWorkHead := padFin h state.relativeWorkHead
  workSlab := padWorkSlab h state.workSlab

/-- Restrict a padded local state whose head is known to remain in the
original prefix. -/
def truncateLocalReplayState {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : LocalReplayState State H W)
    (hhead : state.relativeWorkHead.val < w) :
    LocalReplayState State H w where
  control := state.control
  inputHead := state.inputHead
  relativeWorkHead := ⟨state.relativeWorkHead.val, hhead⟩
  workSlab := truncateWorkSlab h state.workSlab

@[simp]
theorem padLocalReplayState_control {State : Type} {H w W : Nat}
    (h : w ≤ W) (state : LocalReplayState State H w) :
    (padLocalReplayState h state).control = state.control := rfl

@[simp]
theorem padLocalReplayState_inputHead {State : Type} {H w W : Nat}
    (h : w ≤ W) (state : LocalReplayState State H w) :
    (padLocalReplayState h state).inputHead = state.inputHead := rfl

@[simp]
theorem padLocalReplayState_relativeWorkHead_val
    {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : LocalReplayState State H w) :
    (padLocalReplayState h state).relativeWorkHead.val =
      state.relativeWorkHead.val := rfl

@[simp]
theorem padLocalReplayState_workSlab_at_head
    {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : LocalReplayState State H w) :
    (padLocalReplayState h state).workSlab
        (padLocalReplayState h state).relativeWorkHead =
      state.workSlab state.relativeWorkHead := by
  exact padWorkSlab_at_padFin h state.workSlab state.relativeWorkHead

/-- Restricting a padded state recovers the source state exactly. -/
@[simp]
theorem truncateLocalReplayState_padLocalReplayState
    {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : LocalReplayState State H w) :
    truncateLocalReplayState h (padLocalReplayState h state)
        (by exact state.relativeWorkHead.isLt) = state := by
  cases state
  simp [truncateLocalReplayState, padLocalReplayState]

theorem padLocalReplayState_injective
    {State : Type} {H w W : Nat} (h : w ≤ W) :
    Function.Injective
      (padLocalReplayState (State := State) (H := H) h) := by
  intro left right heq
  cases left with
  | mk leftControl leftInput leftHead leftSlab =>
      cases right with
      | mk rightControl rightInput rightHead rightSlab =>
          simp only [padLocalReplayState, LocalReplayState.mk.injEq] at heq ⊢
          exact ⟨heq.1, heq.2.1,
            padFin_injective h heq.2.2.1,
            padWorkSlab_injective h heq.2.2.2⟩

/-- Padding realizes the elementary homogeneous-carrier cardinal bound. -/
theorem card_localReplayState_le_of_width_le
    (State : Type) [Fintype State] (H : Nat) {w W : Nat} (h : w ≤ W) :
    Fintype.card (LocalReplayState State H w) ≤
      Fintype.card (LocalReplayState State H W) := by
  exact Fintype.card_le_of_injective
    (padLocalReplayState (State := State) (H := H) h)
    (padLocalReplayState_injective h)

/-- Padding does not change the canonical full work tape: the cells added on
the right are blank, just like all cells outside the original materialized
slab. -/
theorem materializeWorkSlab_padWorkSlab
    {w W base : Nat} (h : w ≤ W) (slab : WorkSlab w) :
    materializeWorkSlab base (padWorkSlab h slab) =
      materializeWorkSlab base slab := by
  funext cell
  by_cases hsmall : WorkCellInSlab base w cell
  · have hlarge : WorkCellInSlab base W cell := by
      unfold WorkCellInSlab at hsmall ⊢
      omega
    simp only [materializeWorkSlab, dif_pos hsmall, dif_pos hlarge]
    have hindex : workCellIndex hlarge =
        padFin h (workCellIndex hsmall) := by
      apply Fin.ext
      simp only [padFin, workCellIndex]
    rw [hindex, padWorkSlab_at_padFin]
  · by_cases hlarge : WorkCellInSlab base W cell
    · have hge : w ≤ cell - base := by
        unfold WorkCellInSlab at hsmall hlarge
        omega
      simp only [materializeWorkSlab, dif_neg hsmall, dif_pos hlarge]
      apply padWorkSlab_eq_false_of_not_lt h
      simp only [workCellIndex]
      omega
    · simp [materializeWorkSlab, hsmall, hlarge]

/-- Therefore padding a local state preserves its complete canonical
materialization, not merely its observations on the original slab. -/
theorem materializeLocalReplayState_padLocalReplayState
    {State : Type} {H w W base : Nat} (h : w ≤ W)
    (state : LocalReplayState State H w) :
    materializeLocalReplayState base (padLocalReplayState h state) =
      materializeLocalReplayState base state := by
  cases state with
  | mk control inputHead relativeWorkHead workSlab =>
      simp only [padLocalReplayState, materializeLocalReplayState,
        padFin_val]
      rw [materializeWorkSlab_padWorkSlab h workSlab]

/-- The local read used by the finite cached transition is unchanged by
padding. -/
theorem paddedLocalReplayState_work_read
    {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : LocalReplayState State H w) :
    (padLocalReplayState h state).workSlab
        (padLocalReplayState h state).relativeWorkHead =
      state.workSlab state.relativeWorkHead := by
  exact padLocalReplayState_workSlab_at_head h state

/-- If the successor head is still in the original slab, the finite cached
step on the homogeneous padded carrier is exactly the padding of the shorter
step.  This is the transition-level compatibility needed when a block visit
is run in the common carrier. -/
theorem finiteLocalCachedStep_pad_of_original_next
    (machine : DeterministicMachine) {H w W base : Nat} (h : w ≤ W)
    (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (hnonhalting : (cachedInputMachine machine).halt state.control = none)
    (hinput :
      moveInputHead state.inputHead.val
          (cachedInputTransition machine state.control unread
            (state.workSlab state.relativeWorkHead)).inputMove < H + 1)
    (hwork : WorkCellInSlab base w
      (moveWorkHead (base + state.relativeWorkHead.val)
        (cachedInputTransition machine state.control unread
          (state.workSlab state.relativeWorkHead)).workMove)) :
    ∃ next : LocalReplayState (cachedInputMachine machine).State H w,
      finiteLocalCachedStep machine H w base unread state = .inside next ∧
      finiteLocalCachedStep machine H W base unread
          (padLocalReplayState h state) =
        .inside (padLocalReplayState h next) := by
  let instruction := cachedInputTransition machine state.control unread
    (state.workSlab state.relativeWorkHead)
  let nextInput := moveInputHead state.inputHead.val instruction.inputMove
  let nextWork := moveWorkHead (base + state.relativeWorkHead.val)
    instruction.workMove
  let next : LocalReplayState (cachedInputMachine machine).State H w :=
    { control := instruction.nextState
      inputHead := ⟨nextInput, by simpa [instruction, nextInput] using hinput⟩
      relativeWorkHead :=
        workCellIndex (by simpa [instruction, nextWork] using hwork)
      workSlab := writeWorkSlab state.workSlab state.relativeWorkHead
        instruction.write }
  refine ⟨next, ?_, ?_⟩
  · simp [finiteLocalCachedStep, hnonhalting, instruction, nextInput,
      hinput, hwork, next]
  · have hlarge : WorkCellInSlab base W nextWork := by
      have hsmall : WorkCellInSlab base w nextWork := by
        simpa [instruction, nextWork] using hwork
      unfold WorkCellInSlab at hsmall ⊢
      omega
    unfold finiteLocalCachedStep
    simp only [padLocalReplayState_control, padLocalReplayState_inputHead,
      padLocalReplayState_relativeWorkHead_val,
      padLocalReplayState_workSlab_at_head, hnonhalting]
    simp only [instruction, nextWork, hinput, hlarge, dite_true]
    apply congrArg FiniteLocalStepResult.inside
    cases state with
    | mk control inputHead relativeWorkHead workSlab =>
        simp only [next, padLocalReplayState]
        have hsmall : WorkCellInSlab base w nextWork := by
          simpa [instruction, nextWork] using hwork
        have hindex : workCellIndex hlarge =
            padFin h (workCellIndex hsmall) := by
          apply Fin.ext
          simp only [padFin, workCellIndex]
        rw [padWorkSlab_write]
        congr 1

/-- Pad the slab field of a retained final endpoint.  The final work head is
absolute and is deliberately left unchanged, so it may lie outside the
original slab. -/
def padFiniteLocalFinalState {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : FiniteLocalFinalState State H w) :
    FiniteLocalFinalState State H W where
  control := state.control
  inputHead := state.inputHead
  workHead := state.workHead
  workSlab := padWorkSlab h state.workSlab

/-- Map every final-step result into the homogeneous result carrier. -/
def padFiniteLocalFinalStepResult {State : Type} {H w W : Nat}
    (h : w ≤ W) :
    FiniteLocalFinalStepResult State H w →
      FiniteLocalFinalStepResult State H W
  | .stepped state => .stepped (padFiniteLocalFinalState h state)
  | .halted outcome => .halted outcome
  | .inputHorizonExceeded => .inputHorizonExceeded
  | .workHorizonExceeded => .workHorizonExceeded

@[simp]
theorem padFiniteLocalFinalState_control
    {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : FiniteLocalFinalState State H w) :
    (padFiniteLocalFinalState h state).control = state.control := rfl

@[simp]
theorem padFiniteLocalFinalState_inputHead
    {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : FiniteLocalFinalState State H w) :
    (padFiniteLocalFinalState h state).inputHead = state.inputHead := rfl

@[simp]
theorem padFiniteLocalFinalState_workHead
    {State : Type} {H w W : Nat} (h : w ≤ W)
    (state : FiniteLocalFinalState State H w) :
    (padFiniteLocalFinalState h state).workHead = state.workHead := rfl

/-- Padding also preserves the global configuration represented by a final
endpoint, including an absolute work head outside the original slab. -/
theorem materializeFiniteLocalFinalState_padFiniteLocalFinalState
    {State : Type} {H w W base : Nat} (h : w ≤ W)
    (state : FiniteLocalFinalState State H w) :
    materializeFiniteLocalFinalState base (padFiniteLocalFinalState h state) =
      materializeFiniteLocalFinalState base state := by
  cases state with
  | mk control inputHead workHead workSlab =>
      simp only [padFiniteLocalFinalState, materializeFiniteLocalFinalState]
      rw [materializeWorkSlab_padWorkSlab]

/-- The final-step API commutes unconditionally with slab padding.  In the
successful case the post control and both absolute heads are identical and
the written slab is padded.  In particular, this remains true when the final
work head has exited the original width. -/
theorem finiteLocalCachedFinalStep_pad
    (machine : DeterministicMachine) {H w W base : Nat} (h : w ≤ W)
    (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w) :
    finiteLocalCachedFinalStep machine H W base unread
        (padLocalReplayState h state) =
      padFiniteLocalFinalStepResult h
        (finiteLocalCachedFinalStep machine H w base unread state) := by
  unfold finiteLocalCachedFinalStep
  simp only [padLocalReplayState_control, padLocalReplayState_inputHead,
    padLocalReplayState_relativeWorkHead_val,
    padLocalReplayState_workSlab_at_head]
  split
  · rfl
  · split
    · split
      · simp only [padFiniteLocalFinalStepResult,
          padFiniteLocalFinalState, padLocalReplayState]
        rw [padWorkSlab_write]
      · rfl
    · rfl

/-- Successful final steps are therefore preserved verbatim apart from
right-padding the updated slab. -/
theorem finiteLocalCachedFinalStep_pad_stepped
    (machine : DeterministicMachine) {H w W base : Nat} (h : w ≤ W)
    (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (next : FiniteLocalFinalState (cachedInputMachine machine).State H w)
    (hstep : finiteLocalCachedFinalStep machine H w base unread state =
      .stepped next) :
    finiteLocalCachedFinalStep machine H W base unread
        (padLocalReplayState h state) =
      .stepped (padFiniteLocalFinalState h next) := by
  rw [finiteLocalCachedFinalStep_pad, hstep]
  rfl

/-- Every advertised block state embeds into the single width-`2*b`
carrier. -/
def padAdvertisedLocalReplayState
    {State : Type} {T b H : Nat} (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1))
    (state : LocalReplayState State H (advertisedBlockWidth offsets block)) :
    LocalReplayState State H (2 * b) :=
  padLocalReplayState
    (advertisedBlockWidth_le_two_mul hb offsets block) state

theorem padAdvertisedLocalReplayState_injective
    {State : Type} {T b H : Nat} (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    Function.Injective
      (padAdvertisedLocalReplayState
        (State := State) (H := H) hb offsets block) := by
  exact padLocalReplayState_injective
    (advertisedBlockWidth_le_two_mul hb offsets block)

/-- Uniform cardinality bound obtained from the explicit advertised-block
embedding rather than by comparing cardinality formulae abstractly. -/
theorem advertisedLocalReplayState_card_le_padded
    (State : Type) [Fintype State] {T b : Nat} (H : Nat) (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    Fintype.card
        (LocalReplayState State H (advertisedBlockWidth offsets block)) ≤
      Fintype.card (LocalReplayState State H (2 * b)) := by
  exact Fintype.card_le_of_injective
    (padAdvertisedLocalReplayState
      (State := State) (H := H) hb offsets block)
    (padAdvertisedLocalReplayState_injective hb offsets block)

end OneTapeMagnification
end Frontier
end Pnp4
