import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualRunInputOrder
import Pnp4.Frontier.OneTapeMagnification.CanonicalWorkBlocks
import Pnp4.Frontier.OneTapeMagnification.StableGroupingRoutingGridBarrier

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# An actual one-tape realization of the stable-routing grid schedule

This file closes the geometry obligation left explicit in
`StableGroupingRoutingGridBarrier` for one concrete family.  For every
positive number `K` of visited work blocks, a finite-control one-tape machine
walks through the cells

`0, 1, ..., K - 1, K - 1, ..., 1, 0, 0, 1, ...`.

The repeated endpoint is one legal stay transition.  Simultaneously, the
read-only input head moves right at every transition.  Thus the first `R*K`
actual input-read events are exactly `R` serpentine sweeps of `K` blocks.

We use canonical scale `b = 1`.  This is not a favorable-cut assumption: a
full bucket has a unique boundary, so its canonical boundary is forced.  The
actual canonical work-block label is consequently the current work-head cell.
The resulting event schedule is identified with `StableRoutingVertex R K`,
and the chronological-plus-stable-grouped graph contains the same rectangular
grid as the synthetic obstruction.

This is an architecture-specific infrastructure result.  It is not a generic
pathwidth lower bound for every validator and is not progress on a
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound` obligation.
-/

/-! ## A finite-control serpentine machine -/

/-- One step of the finite control.  `false` means a rightward sweep and
`true` a leftward sweep.  At an endpoint the control changes orientation
without changing its finite block coordinate. -/
def serpentineNextState {K : Nat} (hK : 0 < K) :
    Bool × Fin K → Bool × Fin K
  | (false, block) =>
      if hnext : block.val + 1 < K then
        (false, ⟨block.val + 1, hnext⟩)
      else
        (true, block)
  | (true, block) =>
      if hzero : block.val = 0 then
        (false, block)
      else
        (true, ⟨block.val - 1, by omega⟩)

/-- Work-head move synchronized with `serpentineNextState`. -/
def serpentineWorkMove {K : Nat} (hK : 0 < K) :
    Bool × Fin K → WorkMove
  | (false, block) =>
      if block.val + 1 < K then .right else .stay
  | (true, block) =>
      if block.val = 0 then .stay else .left

/-- The scheduled control state after `time` transitions. -/
def serpentineStateAt {K : Nat} (hK : 0 < K) : Nat → Bool × Fin K
  | 0 => (false, ⟨0, hK⟩)
  | time + 1 => serpentineNextState hK (serpentineStateAt hK time)

/-- A machine whose finite state records the current orientation and block.
It ignores both symbols, preserves the blank work tape, and advances the
input head at every transition. -/
def serpentineSweepMachine (K : Nat) (hK : 0 < K) : DeterministicMachine where
  State := Bool × Fin K
  stateFintype := inferInstance
  startState := (false, ⟨0, hK⟩)
  halt := fun _ => none
  transition := fun state _input work =>
    { nextState := serpentineNextState hK state
      write := work
      inputMove := .right
      workMove := serpentineWorkMove hK state }

/-- Closed form of the whole configuration in terms of the recursive
serpentine control schedule. -/
def serpentineConfigurationAt {K : Nat} (hK : 0 < K) (time : Nat) :
    Configuration (Bool × Fin K) where
  state := serpentineStateAt hK time
  inputHead := time
  workHead := (serpentineStateAt hK time).2.val
  workTape := WorkTape.blank

private theorem WorkTape.write_blank_false (head : Nat) :
    WorkTape.write WorkTape.blank head false = WorkTape.blank := by
  funext cell
  simp [WorkTape.write, WorkTape.blank]

@[simp]
theorem step_serpentineConfigurationAt {K : Nat} (hK : 0 < K)
    (input : List Bool) (time : Nat) :
    step (serpentineSweepMachine K hK) input
        (serpentineConfigurationAt hK time) =
      serpentineConfigurationAt hK (time + 1) := by
  rcases hstate : serpentineStateAt hK time with ⟨direction, block⟩
  cases direction <;>
    simp only [step, serpentineSweepMachine,
      serpentineConfigurationAt, hstate, serpentineStateAt,
      applyInstruction, moveInputHead]
  · by_cases hnext : block.val + 1 < K
    · simp [serpentineNextState, serpentineWorkMove, hnext,
        moveWorkHead, WorkTape.write_blank_false]
    · have hlast : block.val + 1 = K := by omega
      simp [serpentineNextState, serpentineWorkMove, hnext,
        moveWorkHead, WorkTape.write_blank_false, hlast]
  · by_cases hzero : block.val = 0
    · simp [serpentineNextState, serpentineWorkMove, hzero,
        moveWorkHead, WorkTape.write_blank_false]
    · simp [serpentineNextState, serpentineWorkMove, hzero,
        moveWorkHead, WorkTape.write_blank_false]

/-- Exact execution theorem, independent of the input contents. -/
theorem run_serpentineSweepMachine {K : Nat} (hK : 0 < K)
    (input : List Bool) (time : Nat) :
    run (serpentineSweepMachine K hK) input time =
      serpentineConfigurationAt hK time := by
  induction time with
  | zero => rfl
  | succ time ih =>
      change runFrom (serpentineSweepMachine K hK) input
          (initialConfiguration (serpentineSweepMachine K hK)) (time + 1) = _
      rw [runFrom_succ_eq_step_runFrom]
      change step (serpentineSweepMachine K hK) input
          (run (serpentineSweepMachine K hK) input time) = _
      rw [ih]
      exact step_serpentineConfigurationAt hK input time

/-! ## Exact rows of the recursive schedule -/

private theorem serpentineStateAt_add {K : Nat} (hK : 0 < K)
    (first later : Nat) :
    serpentineStateAt hK (first + later) =
      (serpentineNextState hK)^[later] (serpentineStateAt hK first) := by
  induction later with
  | zero => simp
  | succ later ih =>
      rw [Nat.add_succ, serpentineStateAt, ih]
      simp [Function.iterate_succ_apply']

private theorem iterate_serpentineNextState_forward {K : Nat} (hK : 0 < K)
    (offset : Nat) (hoffset : offset < K) :
    (serpentineNextState hK)^[offset] (false, ⟨0, hK⟩) =
      (false, ⟨offset, hoffset⟩) := by
  induction offset with
  | zero => rfl
  | succ offset ih =>
      have hprev : offset < K := by omega
      rw [Function.iterate_succ_apply']
      rw [ih hprev]
      simp [serpentineNextState, hoffset]

private theorem iterate_serpentineNextState_forward_full {K : Nat}
    (hK : 0 < K) :
    (serpentineNextState hK)^[K] (false, ⟨0, hK⟩) =
      (true, ⟨K - 1, by omega⟩) := by
  have hlast : K - 1 < K := by omega
  calc
    (serpentineNextState hK)^[K] (false, ⟨0, hK⟩) =
        (serpentineNextState hK)^[(K - 1) + 1] (false, ⟨0, hK⟩) := by
          congr 2 <;> omega
    _ = serpentineNextState hK
        ((serpentineNextState hK)^[K - 1] (false, ⟨0, hK⟩)) := by
          rw [Function.iterate_succ_apply']
    _ = serpentineNextState hK (false, ⟨K - 1, hlast⟩) := by
          rw [iterate_serpentineNextState_forward hK (K - 1) hlast]
    _ = (true, ⟨K - 1, by omega⟩) := by
          have heq : K - 1 + 1 = K := Nat.sub_add_cancel hK
          simp [serpentineNextState, heq]

private theorem iterate_serpentineNextState_reverse {K : Nat} (hK : 0 < K)
    (offset : Nat) (hoffset : offset < K) :
    (serpentineNextState hK)^[offset] (true, ⟨K - 1, by omega⟩) =
      (true, ⟨K - 1 - offset, by omega⟩) := by
  induction offset with
  | zero =>
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp
  | succ offset ih =>
      have hprev : offset < K := by omega
      rw [Function.iterate_succ_apply']
      rw [ih hprev]
      have hpositive : K - 1 - offset ≠ 0 := by omega
      simp [serpentineNextState, hpositive]
      omega

private theorem iterate_serpentineNextState_reverse_full {K : Nat}
    (hK : 0 < K) :
    (serpentineNextState hK)^[K] (true, ⟨K - 1, by omega⟩) =
      (false, ⟨0, hK⟩) := by
  have hlast : K - 1 < K := by omega
  calc
    (serpentineNextState hK)^[K] (true, ⟨K - 1, by omega⟩) =
        (serpentineNextState hK)^[(K - 1) + 1]
          (true, ⟨K - 1, by omega⟩) := by
            congr 2 <;> omega
    _ = serpentineNextState hK
        ((serpentineNextState hK)^[K - 1]
          (true, ⟨K - 1, by omega⟩)) := by
            rw [Function.iterate_succ_apply']
    _ = serpentineNextState hK (true, ⟨0, by omega⟩) := by
          simpa using
            congrArg (serpentineNextState hK)
              (iterate_serpentineNextState_reverse hK (K - 1) hlast)
    _ = (false, ⟨0, hK⟩) := by
          simp [serpentineNextState]

private theorem iterate_serpentineNextState_period {K : Nat} (hK : 0 < K) :
    (serpentineNextState hK)^[2 * K] (false, ⟨0, hK⟩) =
      (false, ⟨0, hK⟩) := by
  rw [show 2 * K = K + K by omega, Function.iterate_add_apply]
  rw [iterate_serpentineNextState_forward_full hK,
    iterate_serpentineNextState_reverse_full hK]

private theorem serpentineStateAt_even_period {K : Nat} (hK : 0 < K)
    (period : Nat) :
    serpentineStateAt hK (period * (2 * K)) = (false, ⟨0, hK⟩) := by
  induction period with
  | zero => simp [serpentineStateAt]
  | succ period ih =>
      rw [Nat.succ_mul, serpentineStateAt_add, ih]
      exact iterate_serpentineNextState_period hK

/-- Even-numbered rows run through physical blocks from left to right. -/
theorem serpentineStateAt_even_row {K : Nat} (hK : 0 < K)
    (period offset : Nat) (hoffset : offset < K) :
    serpentineStateAt hK ((2 * period) * K + offset) =
      (false, ⟨offset, hoffset⟩) := by
  rw [show (2 * period) * K = period * (2 * K) by ring,
    serpentineStateAt_add, serpentineStateAt_even_period hK]
  exact iterate_serpentineNextState_forward hK offset hoffset

/-- Odd-numbered rows run through physical blocks from right to left. -/
theorem serpentineStateAt_odd_row {K : Nat} (hK : 0 < K)
    (period offset : Nat) (hoffset : offset < K) :
    serpentineStateAt hK ((2 * period + 1) * K + offset) =
      (true, ⟨K - 1 - offset, by omega⟩) := by
  rw [show (2 * period + 1) * K = period * (2 * K) + K by ring,
    show period * (2 * K) + K + offset =
      period * (2 * K) + (offset + K) by omega,
    serpentineStateAt_add, serpentineStateAt_even_period hK,
    Function.iterate_add_apply,
    iterate_serpentineNextState_forward_full hK]
  exact iterate_serpentineNextState_reverse hK offset hoffset

/-! ## Unit-scale canonical blocks -/

/-- At scale one the unique offset in every full bucket is zero. -/
@[simp]
theorem canonicalBoundaryOffset_one {T : Nat} (crossings : Fin T → Nat)
    (bucket : Fin (T / 1)) :
    (canonicalBoundaryOffset (by omega : 0 < 1) crossings bucket).val = 0 := by
  have := (canonicalBoundaryOffset
    (by omega : 0 < 1) crossings bucket).isLt
  omega

/-- Consequently, the unique canonical boundary in bucket `i` is boundary
`i` itself. -/
@[simp]
theorem canonicalBoundary_one_val {T : Nat} (crossings : Fin T → Nat)
    (bucket : Fin (T / 1)) :
    (canonicalBoundary (by omega : 0 < 1) crossings bucket).val = bucket.val := by
  simp [canonicalBoundary_val]

/-- On represented cells `0, ..., T`, the unit-scale canonical block label is
exactly the cell number.  Crossing counts play no role in this identity. -/
theorem workBlockAt_one_val {T cell : Nat} (crossings : Fin T → Nat)
    (hcell : cell ≤ T) :
    (workBlockAt (by omega : 0 < 1) crossings cell).val = cell := by
  let block := workBlockAt (by omega : 0 < 1) crossings cell
  have hblock : block.val ≤ T := by
    have := block.isLt
    simp only [Nat.div_one] at this
    omega
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : cell < block.val := by omega
    let bucket : Fin (T / 1) := ⟨cell, by simp; omega⟩
    have hrank :=
      (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
        (by omega : 0 < 1) crossings bucket cell).mpr hlt
    simp [bucket] at hrank
  · by_contra hnot
    have hlt : block.val < cell := by omega
    let bucket : Fin (T / 1) := ⟨block.val, by simp; omega⟩
    have hrank :=
      (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
        (by omega : 0 < 1) crossings bucket cell).mp (by
          simpa [bucket] using hlt)
    exact (Nat.lt_irrefl block.val hrank)

/-! ## Actual events indexed by the serpentine grid -/

/-- Row parity supplies the orientation used by the synthetic routing graph. -/
def serpentineReverseRow {R : Nat} (row : Fin R) : Bool :=
  decide (row.val % 2 = 1)

/-- The chronological transition time of one `(row, physicalBlock)` event. -/
def serpentineEventTime {R K : Nat} (hK : 0 < K)
    (vertex : StableRoutingVertex R K) : Fin (R * K) := by
  refine ⟨stableRoutingChronologicalIndex serpentineReverseRow vertex, ?_⟩
  unfold stableRoutingChronologicalIndex serpentineReverseRow
  split_ifs
  · have hoffset : K - 1 - vertex.2.val < K := by omega
    calc
      vertex.1.val * K + (K - 1 - vertex.2.val) <
          vertex.1.val * K + K := Nat.add_lt_add_left hoffset _
      _ = (vertex.1.val + 1) * K := by ring
      _ ≤ R * K := Nat.mul_le_mul_right K
        (Nat.succ_le_of_lt vertex.1.isLt)
  · calc
      vertex.1.val * K + vertex.2.val <
          vertex.1.val * K + K :=
            Nat.add_lt_add_left vertex.2.isLt _
      _ = (vertex.1.val + 1) * K := by ring
      _ ≤ R * K := Nat.mul_le_mul_right K
        (Nat.succ_le_of_lt vertex.1.isLt)

@[simp]
theorem serpentineEventTime_val {R K : Nat} (hK : 0 < K)
    (vertex : StableRoutingVertex R K) :
    (serpentineEventTime hK vertex).val =
      stableRoutingChronologicalIndex serpentineReverseRow vertex :=
  rfl

/-- Division by the row length recovers the event's sweep row. -/
theorem serpentineEventTime_div {R K : Nat} (hK : 0 < K)
    (vertex : StableRoutingVertex R K) :
    (serpentineEventTime hK vertex).val / K = vertex.1.val := by
  rw [serpentineEventTime_val]
  unfold stableRoutingChronologicalIndex
  split_ifs with hreverse
  · have hoffset : K - 1 - vertex.2.val < K := by omega
    rw [Nat.mul_comm vertex.1.val K, Nat.mul_add_div hK,
      Nat.div_eq_of_lt hoffset]
    simp
  · rw [Nat.mul_comm vertex.1.val K, Nat.mul_add_div hK,
      Nat.div_eq_of_lt vertex.2.isLt]
    simp

/-- At the mapped transition time, the scheduled physical work block is the
second coordinate of the routing vertex. -/
theorem serpentineStateAt_eventTime_block_val {R K : Nat} (hK : 0 < K)
    (vertex : StableRoutingVertex R K) :
    (serpentineStateAt hK (serpentineEventTime hK vertex).val).2.val =
      vertex.2.val := by
  let row := vertex.1.val
  have hmodlt : row % 2 < 2 := Nat.mod_lt row (by omega)
  have hdecompose := Nat.mod_add_div row 2
  by_cases hodd : row % 2 = 1
  · have hrow : row = 2 * (row / 2) + 1 := by omega
    have hreverse : serpentineReverseRow vertex.1 = true := by
      simp only [serpentineReverseRow, decide_eq_true_eq]
      simpa [row] using hodd
    have htime : (serpentineEventTime hK vertex).val =
        (2 * (row / 2) + 1) * K + (K - 1 - vertex.2.val) := by
      rw [serpentineEventTime_val]
      unfold stableRoutingChronologicalIndex
      rw [if_pos hreverse]
      change row * K + (K - 1 - vertex.2.val) = _
      exact congrArg (fun head => head * K + (K - 1 - vertex.2.val)) hrow
    have hs := serpentineStateAt_odd_row hK (row / 2)
      (K - 1 - vertex.2.val) (by omega)
    have hsval := congrArg (fun state => state.2.val) hs
    rw [htime]
    change (serpentineStateAt hK
      ((2 * (row / 2) + 1) * K + (K - 1 - vertex.2.val))).2.val =
        K - 1 - (K - 1 - vertex.2.val) at hsval
    calc
      _ = K - 1 - (K - 1 - vertex.2.val) := hsval
      _ = vertex.2.val := by omega
  · have heven : row % 2 = 0 := by omega
    have hrow : row = 2 * (row / 2) := by omega
    have hreverse : serpentineReverseRow vertex.1 ≠ true := by
      intro htrue
      have : vertex.1.val % 2 = 1 := by
        simpa only [serpentineReverseRow, decide_eq_true_eq] using htrue
      exact hodd (by simpa [row] using this)
    have htime : (serpentineEventTime hK vertex).val =
        (2 * (row / 2)) * K + vertex.2.val := by
      rw [serpentineEventTime_val]
      unfold stableRoutingChronologicalIndex
      rw [if_neg hreverse]
      change row * K + vertex.2.val = _
      exact congrArg (fun head => head * K + vertex.2.val) hrow
    have hs := serpentineStateAt_even_row hK (row / 2)
      vertex.2.val vertex.2.isLt
    have hsval := congrArg (fun state => state.2.val) hs
    rw [htime]
    simpa using hsval

/-- The actual work head is at the claimed physical block at every mapped
event time. -/
theorem run_serpentineSweepMachine_eventTime_workHead {R K : Nat}
    (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    (run (serpentineSweepMachine K hK) input
      (serpentineEventTime hK vertex).val).workHead = vertex.2.val := by
  rw [run_serpentineSweepMachine hK]
  exact serpentineStateAt_eventTime_block_val hK vertex

/-- The actual input head equals time because every transition moves it
right. -/
theorem run_serpentineSweepMachine_inputHead {K : Nat} (hK : 0 < K)
    (input : List Bool) (time : Nat) :
    (run (serpentineSweepMachine K hK) input time).inputHead = time := by
  rw [run_serpentineSweepMachine hK]
  rfl

/-- The unit-scale canonical label of each mapped actual event is exactly its
physical block coordinate. -/
theorem actualCanonicalWorkBlockAtTime_serpentineEventTime_val
    {R K : Nat} (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    (actualCanonicalWorkBlockAtTime
      (serpentineSweepMachine K hK) input (R * K) 1 (by omega)
      (serpentineEventTime hK vertex).val).val = vertex.2.val := by
  unfold actualCanonicalWorkBlockAtTime canonicalWorkBlockAtTime
  rw [workBlockAt_one_val]
  · exact run_serpentineSweepMachine_eventTime_workHead hK input vertex
  · change
      (run (serpentineSweepMachine K hK) input
        (serpentineEventTime hK vertex).val).workHead ≤ R * K
    rw [run_serpentineSweepMachine_eventTime_workHead hK input vertex]
    have hR : 0 < R := Nat.zero_lt_of_lt vertex.1.isLt
    have hKle : K ≤ R * K := by
      calc
        K = 1 * K := by simp
        _ ≤ R * K := Nat.mul_le_mul_right K hR
    exact vertex.2.isLt.le.trans hKle

/-- The concrete event at a grid vertex. -/
noncomputable def actualSerpentineInputEvent {R K : Nat} (hK : 0 < K)
    (input : List Bool) (vertex : StableRoutingVertex R K) :
    InputReadEvent (R * K / 1 + 1) :=
  actualRunInputEvent (serpentineSweepMachine K hK) input
    (actualCanonicalWorkBlockAtTime
      (serpentineSweepMachine K hK) input (R * K) 1 (by omega))
    (serpentineEventTime hK vertex).val

@[simp]
theorem actualSerpentineInputEvent_chronologicalPosition
    {R K : Nat} (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    (actualSerpentineInputEvent hK input vertex).chronologicalPosition =
      stableRoutingChronologicalIndex serpentineReverseRow vertex :=
  rfl

@[simp]
theorem actualSerpentineInputEvent_workBlock_val
    {R K : Nat} (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    (actualSerpentineInputEvent hK input vertex).workBlock.val =
      vertex.2.val := by
  exact actualCanonicalWorkBlockAtTime_serpentineEventTime_val
    hK input vertex

@[simp]
theorem actualSerpentineInputEvent_inputPosition
    {R K : Nat} (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    (actualSerpentineInputEvent hK input vertex).inputPosition =
      stableRoutingChronologicalIndex serpentineReverseRow vertex := by
  unfold actualSerpentineInputEvent actualRunInputEvent
  rw [run_serpentineSweepMachine_inputHead]
  rfl

@[simp]
theorem actualSerpentineInputEvent_advances
    {R K : Nat} (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    (actualSerpentineInputEvent hK input vertex).advances = true := by
  unfold actualSerpentineInputEvent actualRunInputEvent inputHeadAdvancesAt
  rw [run_serpentineSweepMachine_inputHead,
    run_serpentineSweepMachine_inputHead]
  simp

/-! ## The two actual event orders and the inherited grid -/

/-- The chronological time map enumerates all first `R*K` transition times
without collision. -/
theorem serpentineEventTime_injective {R K : Nat} (hK : 0 < K) :
    Function.Injective (serpentineEventTime (R := R) hK) := by
  intro left right htime
  have hrow : left.1.val = right.1.val := by
    have hquotient := congrArg
      (fun time : Fin (R * K) => time.val / K) htime
    simpa only [serpentineEventTime_div hK] using hquotient
  have hblock : left.2.val = right.2.val := by
    calc
      left.2.val =
          (serpentineStateAt hK
            (serpentineEventTime hK left).val).2.val :=
        (serpentineStateAt_eventTime_block_val hK left).symm
      _ = (serpentineStateAt hK
            (serpentineEventTime hK right).val).2.val := by rw [htime]
      _ = right.2.val :=
        serpentineStateAt_eventTime_block_val hK right
  apply Prod.ext
  · exact Fin.ext hrow
  · exact Fin.ext hblock

/-- Since both finite types have cardinality `R*K`, the chronological map is
in fact a bijection onto all first `R*K` transition times. -/
theorem serpentineEventTime_bijective {R K : Nat} (hK : 0 < K) :
    Function.Bijective (serpentineEventTime (R := R) hK) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact serpentineEventTime_injective hK
  · simp [StableRoutingVertex]

/-- Distinct grid vertices give distinct concrete input-read events. -/
theorem actualSerpentineInputEvent_injective {R K : Nat} (hK : 0 < K)
    (input : List Bool) :
    Function.Injective (actualSerpentineInputEvent (R := R) hK input) := by
  intro left right hevent
  apply serpentineEventTime_injective hK
  apply Fin.ext
  have hchronological := congrArg
    InputReadEvent.chronologicalPosition hevent
  simpa only [actualSerpentineInputEvent_chronologicalPosition,
    serpentineEventTime_val] using hchronological

/-- Chronological index read from the concrete event itself. -/
noncomputable def actualSerpentineChronologicalIndex {R K : Nat}
    (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) : Nat :=
  (actualSerpentineInputEvent hK input vertex).chronologicalPosition

/-- Stable-grouped index read from the event's actual canonical block, with
the sweep row recovered from its actual transition time. -/
noncomputable def actualSerpentineGroupedIndex {R K : Nat}
    (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) : Nat :=
  (actualSerpentineInputEvent hK input vertex).workBlock.val * R +
    (serpentineEventTime hK vertex).val / K

@[simp]
theorem actualSerpentineChronologicalIndex_eq {R K : Nat}
    (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    actualSerpentineChronologicalIndex hK input vertex =
      stableRoutingChronologicalIndex serpentineReverseRow vertex := by
  simp [actualSerpentineChronologicalIndex]

@[simp]
theorem actualSerpentineGroupedIndex_eq {R K : Nat}
    (hK : 0 < K) (input : List Bool)
    (vertex : StableRoutingVertex R K) :
    actualSerpentineGroupedIndex hK input vertex =
      stableRoutingGroupedIndex vertex := by
  unfold actualSerpentineGroupedIndex stableRoutingGroupedIndex
  rw [actualSerpentineInputEvent_workBlock_val,
    serpentineEventTime_div]

/-- Successor relation obtained from the two orders of the concrete actual
events. -/
noncomputable def actualSerpentineEventSuccessor {R K : Nat}
    (hK : 0 < K) (input : List Bool)
    (left right : StableRoutingVertex R K) : Prop :=
  actualSerpentineChronologicalIndex hK input left + 1 =
      actualSerpentineChronologicalIndex hK input right ∨
    actualSerpentineGroupedIndex hK input left + 1 =
      actualSerpentineGroupedIndex hK input right

theorem actualSerpentineEventSuccessor_iff {R K : Nat}
    (hK : 0 < K) (input : List Bool)
    (left right : StableRoutingVertex R K) :
    actualSerpentineEventSuccessor hK input left right ↔
      stableRoutingSuccessor serpentineReverseRow left right := by
  simp only [actualSerpentineEventSuccessor, stableRoutingSuccessor,
    actualSerpentineChronologicalIndex_eq,
    actualSerpentineGroupedIndex_eq]

/-- Literal chronological-plus-stable-grouped graph on the concrete actual
events (represented by their bijective grid coordinates). -/
noncomputable def actualSerpentineTwoOrderRoutingGraph {R K : Nat}
    (hK : 0 < K) (input : List Bool) :
    SimpleGraph (StableRoutingVertex R K) :=
  SimpleGraph.fromRel (actualSerpentineEventSuccessor hK input)

/-- The actual-event graph is exactly the synthetic two-order graph, not only
an abstract graph with the same cardinality. -/
theorem actualSerpentineTwoOrderRoutingGraph_eq {R K : Nat}
    (hK : 0 < K) (input : List Bool) :
    actualSerpentineTwoOrderRoutingGraph (R := R) hK input =
      stableTwoOrderRoutingGraph (roundCount := R) (blockCount := K)
        (serpentineReverseRow (R := R)) := by
  ext left right
  simp only [actualSerpentineTwoOrderRoutingGraph,
    stableTwoOrderRoutingGraph, SimpleGraph.fromRel_adj]
  rw [actualSerpentineEventSuccessor_iff,
    actualSerpentineEventSuccessor_iff]

/-- Main geometry theorem: the rectangular grid occurs in the literal
two-order graph of actual canonical input-read events of the concrete
one-tape machine. -/
theorem stableRoutingGrid_le_actualSerpentineTwoOrderRoutingGraph
    {R K : Nat} (hK : 0 < K) (input : List Bool) :
    SimpleGraph.pathGraph R □ SimpleGraph.pathGraph K ≤
      actualSerpentineTwoOrderRoutingGraph hK input := by
  rw [actualSerpentineTwoOrderRoutingGraph_eq]
  exact stableRoutingGrid_le_twoOrderRoutingGraph
    (serpentineReverseRow (R := R))

/-- Quantitative horizon identity for the realization.  With unit canonical
scale this is the requested `T = R*K = O(R*K*b)` instance at `b = 1`. -/
theorem actualSerpentine_horizon_eq (R K : Nat) :
    R * K = R * K * 1 := by
  omega

end OneTapeMagnification
end Frontier
end Pnp4
