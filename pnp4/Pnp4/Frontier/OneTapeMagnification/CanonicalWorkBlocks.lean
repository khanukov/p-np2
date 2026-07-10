import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalBlockGaps
import Pnp4.Frontier.OneTapeMagnification.WorkHeadCrossings

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Canonical consecutive work blocks

The canonical boundary in bucket `i` separates work cells `cut i` and
`cut i + 1`.  This file turns those ordered cuts into the explicit block
classifier needed by event-level decompositions.  The convention is that a
boundary cell belongs to the block on its left: the block number of a cell is
the number of selected boundaries strictly to its left.

Thus `T / b` cuts induce exactly `T / b + 1` possible block labels.  This
definition remains meaningful when `T / b = 0`: there are no selected cuts
and every cell has label zero.  For represented cells `0, ..., T`, any two
cells with the same label have spatial diameter strictly below `2 * b`.

The final theorems connect an actual one-step work-head move to the selected
cuts.  They do not construct a local simulator, bound branching-program
width, or prove input-independence of a transcript.
-/

/-- Selected cuts lying strictly to the left of `cell`. -/
noncomputable def selectedCanonicalBoundariesBelow {T b : Nat}
    (hb : 0 < b) (crossings : Fin T -> Nat) (cell : Nat) :
    Finset (Fin (T / b)) := by
  classical
  exact Finset.univ.filter fun i =>
    (canonicalBoundary hb crossings i).val < cell

/-- Canonical block containing `cell`.

The classifier is defined on all natural cells so it can be composed directly
with a work-head trajectory.  Diameter statements explicitly restrict to the
represented interval `cell <= T`. -/
noncomputable def workBlockAt {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (cell : Nat) : Fin (T / b + 1) := by
  classical
  refine ⟨(selectedCanonicalBoundariesBelow hb crossings cell).card, ?_⟩
  apply Nat.lt_succ_of_le
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card
      (Finset.filter_subset
        (fun i : Fin (T / b) =>
          (canonicalBoundary hb crossings i).val < cell)
        Finset.univ)

@[simp]
theorem workBlockAt_val {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (cell : Nat) :
    (workBlockAt hb crossings cell).val =
      (selectedCanonicalBoundariesBelow hb crossings cell).card :=
  rfl

/-- Canonical cuts are strictly increasing with their bucket indices. -/
theorem canonicalBoundary_lt_of_index_lt {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) {i j : Fin (T / b)} (hij : i < j) :
    (canonicalBoundary hb crossings i).val <
      (canonicalBoundary hb crossings j).val := by
  have hi := canonicalBoundary_mem_bucket hb crossings i
  have hj := canonicalBoundary_mem_bucket hb crossings j
  have hIndex : i.val + 1 <= j.val := Nat.succ_le_iff.mpr hij
  calc
    (canonicalBoundary hb crossings i).val < (i.val + 1) * b := hi.2
    _ <= j.val * b := Nat.mul_le_mul_right b hIndex
    _ <= (canonicalBoundary hb crossings j).val := hj.1

/-- Weak monotonicity of canonical cuts. -/
theorem canonicalBoundary_le_of_index_le {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) {i j : Fin (T / b)} (hij : i <= j) :
    (canonicalBoundary hb crossings i).val <=
      (canonicalBoundary hb crossings j).val := by
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact Nat.le_of_lt (canonicalBoundary_lt_of_index_lt hb crossings hij)
  · exact Nat.le_refl _

/-- The ordered cuts reflect strict order on bucket indices. -/
theorem canonicalBoundary_lt_iff_index_lt {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (i j : Fin (T / b)) :
    (canonicalBoundary hb crossings i).val <
        (canonicalBoundary hb crossings j).val <-> i < j := by
  constructor
  · intro hCut
    apply lt_of_not_ge
    intro hji
    exact (Nat.not_lt_of_ge
      (canonicalBoundary_le_of_index_le hb crossings hji)) hCut
  · exact canonicalBoundary_lt_of_index_lt hb crossings

/-- The ordered cuts reflect weak order on bucket indices. -/
theorem canonicalBoundary_le_iff_index_le {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (i j : Fin (T / b)) :
    (canonicalBoundary hb crossings i).val <=
        (canonicalBoundary hb crossings j).val <-> i <= j := by
  constructor
  · intro hCut
    apply le_of_not_gt
    intro hji
    exact (Nat.not_lt_of_ge hCut)
      (canonicalBoundary_lt_of_index_lt hb crossings hji)
  · exact canonicalBoundary_le_of_index_le hb crossings

/-- A cut lies to the left of a cell exactly when its index is below the
cell's block number.  This is the rank characterization of `workBlockAt`. -/
theorem canonicalBoundary_lt_cell_iff_index_lt_workBlockAt {T b : Nat}
    (hb : 0 < b) (crossings : Fin T -> Nat) (i : Fin (T / b))
    (cell : Nat) :
    (canonicalBoundary hb crossings i).val < cell <->
      i.val < (workBlockAt hb crossings cell).val := by
  classical
  constructor
  · intro hCut
    have hSubset : Finset.Iic i <=
        selectedCanonicalBoundariesBelow hb crossings cell := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [selectedCanonicalBoundariesBelow, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact lt_of_le_of_lt
        (canonicalBoundary_le_of_index_le hb crossings hj) hCut
    have hCard := Finset.card_le_card hSubset
    have hIic : (Finset.Iic i).card = i.val + 1 := by simp
    rw [hIic] at hCard
    change i.val <
      (selectedCanonicalBoundariesBelow hb crossings cell).card
    omega
  · intro hRank
    by_contra hCut
    have hCellLe : cell <= (canonicalBoundary hb crossings i).val :=
      Nat.le_of_not_gt hCut
    have hSubset : selectedCanonicalBoundariesBelow hb crossings cell <=
        Finset.Iio i := by
      intro j hj
      simp only [selectedCanonicalBoundariesBelow, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      apply lt_of_not_ge
      intro hij
      have hCutLe := canonicalBoundary_le_of_index_le hb crossings hij
      omega
    have hCard := Finset.card_le_card hSubset
    have hIio : (Finset.Iio i).card = i.val := by simp
    rw [hIio] at hCard
    change i.val <
      (selectedCanonicalBoundariesBelow hb crossings cell).card at hRank
    omega

/-- Under the left-cell convention, the cell at cut `i` has block label `i`. -/
theorem workBlockAt_canonicalBoundary_val {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (i : Fin (T / b)) :
    (workBlockAt hb crossings
      (canonicalBoundary hb crossings i).val).val = i.val := by
  classical
  rw [workBlockAt_val]
  have hSet : selectedCanonicalBoundariesBelow hb crossings
      (canonicalBoundary hb crossings i).val = Finset.Iio i := by
    ext j
    simp only [selectedCanonicalBoundariesBelow, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_Iio]
    exact canonicalBoundary_lt_iff_index_lt hb crossings j i
  rw [hSet]
  simp

/-- The cell immediately right of cut `i` has the adjacent label `i + 1`. -/
theorem workBlockAt_canonicalBoundary_succ_val {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (i : Fin (T / b)) :
    (workBlockAt hb crossings
      ((canonicalBoundary hb crossings i).val + 1)).val = i.val + 1 := by
  classical
  rw [workBlockAt_val]
  have hSet : selectedCanonicalBoundariesBelow hb crossings
      ((canonicalBoundary hb crossings i).val + 1) = Finset.Iic i := by
    ext j
    simp only [selectedCanonicalBoundariesBelow, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_Iic]
    rw [Nat.lt_succ_iff]
    exact canonicalBoundary_le_iff_index_le hb crossings j i
  rw [hSet]
  simp

/-- Exact typed left label at a selected cut. -/
theorem workBlockAt_canonicalBoundary {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (i : Fin (T / b)) :
    workBlockAt hb crossings (canonicalBoundary hb crossings i).val =
      Fin.castSucc i := by
  apply Fin.ext
  exact workBlockAt_canonicalBoundary_val hb crossings i

/-- Exact typed right label at a selected cut. -/
theorem workBlockAt_canonicalBoundary_succ {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (i : Fin (T / b)) :
    workBlockAt hb crossings
        ((canonicalBoundary hb crossings i).val + 1) = Fin.succ i := by
  apply Fin.ext
  exact workBlockAt_canonicalBoundary_succ_val hb crossings i

/-- Every selected cut separates two different, adjacent block labels. -/
theorem workBlockAt_canonicalBoundary_ne_succ {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (i : Fin (T / b)) :
    workBlockAt hb crossings (canonicalBoundary hb crossings i).val ≠
      workBlockAt hb crossings
        ((canonicalBoundary hb crossings i).val + 1) := by
  intro hEq
  have hVal := congrArg Fin.val hEq
  rw [workBlockAt_canonicalBoundary_val hb crossings i,
    workBlockAt_canonicalBoundary_succ_val hb crossings i] at hVal
  omega

/-- Membership of a represented work cell in a canonical block. -/
def WorkCellInCanonicalBlock {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (cell : Fin (T + 1))
    (block : Fin (T / b + 1)) : Prop :=
  workBlockAt hb crossings cell.val = block

/-- Every represented cell belongs to exactly one canonical block. -/
theorem workCell_existsUnique_canonicalBlock {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (cell : Fin (T + 1)) :
    ∃! block : Fin (T / b + 1),
      WorkCellInCanonicalBlock hb crossings cell block := by
  refine ⟨workBlockAt hb crossings cell.val, rfl, ?_⟩
  intro block hBlock
  exact hBlock.symm

/-- Ordered cells with the same canonical label are less than `2 * b` apart.
The proof handles the no-full-bucket case separately and otherwise uses the
first, adjacent, and last gap bounds. -/
theorem same_workBlock_gap_lt_two_mul {T b x y : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (hy : y <= T)
    (hSame : workBlockAt hb crossings x = workBlockAt hb crossings y) :
    y < x + 2 * b := by
  have hSameVal := congrArg Fin.val hSame
  by_cases hBlocks : 0 < T / b
  · have hLabelLe : (workBlockAt hb crossings x).val <= T / b := by
      exact Nat.le_of_lt_succ (workBlockAt hb crossings x).isLt
    by_cases hFirst : (workBlockAt hb crossings x).val = 0
    · let first : Fin (T / b) := firstFullBucketIndex hBlocks
      have hNotCut : ¬
          ((canonicalBoundary hb crossings first).val < y) := by
        intro hCut
        have hIndex :=
          (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
            hb crossings first y).mp hCut
        rw [← hSameVal, hFirst] at hIndex
        simp [first, firstFullBucketIndex] at hIndex
      have hyFirst : y <= (canonicalBoundary hb crossings first).val :=
        Nat.le_of_not_gt hNotCut
      have hFirstGap :=
        firstCanonicalBoundary_lt_blockSize hb hBlocks crossings
      change (canonicalBoundary hb crossings first).val < b at hFirstGap
      omega
    · by_cases hLast :
          (workBlockAt hb crossings x).val = T / b
      · let last : Fin (T / b) := lastFullBucketIndex hBlocks
        have hLastIndex : last.val <
            (workBlockAt hb crossings x).val := by
          rw [hLast]
          have hLastVal := lastFullBucketIndex_val_add_one hBlocks
          change last.val + 1 = T / b at hLastVal
          omega
        have hCutX : (canonicalBoundary hb crossings last).val < x :=
          (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
            hb crossings last x).mpr hLastIndex
        have hLastGap :=
          total_lt_lastCanonicalBoundary_add_two_mul hb hBlocks crossings
        change T < (canonicalBoundary hb crossings last).val + 2 * b at hLastGap
        omega
      · have hLabelPos : 0 < (workBlockAt hb crossings x).val := by omega
        have hLabelLt : (workBlockAt hb crossings x).val < T / b := by omega
        let previous : Fin (T / b) :=
          ⟨(workBlockAt hb crossings x).val - 1, by omega⟩
        let next : Fin (T / b) :=
          ⟨(workBlockAt hb crossings x).val, hLabelLt⟩
        have hPreviousIndex : previous.val <
            (workBlockAt hb crossings x).val := by
          simp only [previous]
          omega
        have hPreviousCut :
            (canonicalBoundary hb crossings previous).val < x :=
          (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
            hb crossings previous x).mpr hPreviousIndex
        have hNotNextCut : ¬
            ((canonicalBoundary hb crossings next).val < y) := by
          intro hCut
          have hIndex :=
            (canonicalBoundary_lt_cell_iff_index_lt_workBlockAt
              hb crossings next y).mp hCut
          rw [← hSameVal] at hIndex
          exact (Nat.lt_irrefl _ hIndex)
        have hyNext : y <= (canonicalBoundary hb crossings next).val :=
          Nat.le_of_not_gt hNotNextCut
        have hAdjacent : next.val = previous.val + 1 := by
          simp only [next, previous]
          omega
        have hGap :=
          (canonicalBoundary_adjacent_gap_lt_two_mul
            hb crossings previous next hAdjacent).2
        omega
  · have hNoBlocks : T / b = 0 := Nat.eq_zero_of_not_pos hBlocks
    have hTlt : T < b := Nat.lt_of_div_eq_zero hb hNoBlocks
    omega

/-- Symmetric diameter form for represented natural-number cells. -/
theorem same_workBlock_spatial_diameter_lt_two_mul {T b x y : Nat}
    (hb : 0 < b) (crossings : Fin T -> Nat) (hx : x <= T) (hy : y <= T)
    (hSame : workBlockAt hb crossings x = workBlockAt hb crossings y) :
    x < y + 2 * b /\ y < x + 2 * b := by
  rcases le_total x y with hxy | hyx
  · exact ⟨by omega,
      same_workBlock_gap_lt_two_mul hb crossings hy hSame⟩
  · exact ⟨same_workBlock_gap_lt_two_mul hb crossings hx hSame.symm,
      by omega⟩

/-- Diameter statement directly on the represented finite cell type. -/
theorem workCell_sameBlock_spatial_diameter_lt_two_mul {T b : Nat}
    (hb : 0 < b) (crossings : Fin T -> Nat) {x y : Fin (T + 1)}
    (hSame : workBlockAt hb crossings x.val =
      workBlockAt hb crossings y.val) :
    x.val < y.val + 2 * b /\ y.val < x.val + 2 * b := by
  apply same_workBlock_spatial_diameter_lt_two_mul hb crossings
  · omega
  · omega
  · exact hSame

/-- A right unit move changes block exactly at a selected cut. -/
theorem workBlockAt_right_ne_iff_selectedBoundary {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (cell : Nat) :
    workBlockAt hb crossings cell ≠ workBlockAt hb crossings (cell + 1) <->
      ∃ i : Fin (T / b),
        (canonicalBoundary hb crossings i).val = cell := by
  classical
  constructor
  · intro hNe
    let below := selectedCanonicalBoundariesBelow hb crossings cell
    let belowSucc :=
      selectedCanonicalBoundariesBelow hb crossings (cell + 1)
    have hSubset : below <= belowSucc := by
      intro i hi
      simp only [below, selectedCanonicalBoundariesBelow,
        Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [belowSucc, selectedCanonicalBoundariesBelow,
        Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hSetNe : below ≠ belowSucc := by
      intro hSet
      apply hNe
      apply Fin.ext
      simpa only [workBlockAt_val, below, belowSucc] using
        congrArg Finset.card hSet
    have hWitness : ∃ i, i ∈ belowSucc ∧ i ∉ below := by
      by_contra hNoWitness
      push_neg at hNoWitness
      apply hSetNe
      apply Finset.Subset.antisymm hSubset
      intro i hi
      exact hNoWitness i hi
    obtain ⟨i, hiSucc, hi⟩ := hWitness
    refine ⟨i, ?_⟩
    simp only [belowSucc, selectedCanonicalBoundariesBelow,
      Finset.mem_filter, Finset.mem_univ, true_and] at hiSucc
    simp only [below, selectedCanonicalBoundariesBelow,
      Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    omega
  · rintro ⟨i, hCut⟩
    intro hEq
    have hSeparated :=
      workBlockAt_canonicalBoundary_ne_succ hb crossings i
    rw [hCut] at hSeparated
    exact hSeparated hEq

/-- For any legal one-step work-head move, changing block is equivalent to
crossing one of the selected canonical boundaries.  The clamped left move
from zero is a stay and therefore crosses nothing. -/
theorem workBlockAt_ne_iff_crosses_selectedBoundary {T b x y : Nat}
    (hb : 0 < b) (crossings : Fin T -> Nat)
    (hMove : y = x - 1 \/ y = x \/ y = x + 1) :
    workBlockAt hb crossings x ≠ workBlockAt hb crossings y <->
      ∃ i : Fin (T / b),
        CrossesWorkBoundary (canonicalBoundary hb crossings i).val x y := by
  rcases hMove with hLeft | hStay | hRight
  · subst y
    by_cases hx : x = 0
    · subst x
      constructor
      · intro hNe
        exact False.elim (hNe rfl)
      · rintro ⟨i, hCross⟩
        exact False.elim ((not_crossesWorkBoundary_stay
          (canonicalBoundary hb crossings i).val 0) hCross)
    · have hxPos : 0 < x := Nat.pos_of_ne_zero hx
      have hRestore : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
      constructor
      · intro hNe
        have hRightNe :
            workBlockAt hb crossings (x - 1) ≠
              workBlockAt hb crossings (x - 1 + 1) := by
          rw [hRestore]
          exact Ne.symm hNe
        obtain ⟨i, hCut⟩ :=
          (workBlockAt_right_ne_iff_selectedBoundary
            hb crossings (x - 1)).mp hRightNe
        refine ⟨i, ?_⟩
        exact (crossesWorkBoundary_left_iff
          (canonicalBoundary hb crossings i).val x).mpr ⟨hxPos, hCut⟩
      · rintro ⟨i, hCross⟩
        have hCut := (crossesWorkBoundary_left_iff
          (canonicalBoundary hb crossings i).val x).mp hCross
        have hRightNe :=
          (workBlockAt_right_ne_iff_selectedBoundary
            hb crossings (x - 1)).mpr ⟨i, hCut.2⟩
        rw [hRestore] at hRightNe
        exact Ne.symm hRightNe
  · subst y
    constructor
    · intro hNe
      exact False.elim (hNe rfl)
    · rintro ⟨i, hCross⟩
      exact False.elim ((not_crossesWorkBoundary_stay
        (canonicalBoundary hb crossings i).val x) hCross)
  · subst y
    constructor
    · intro hNe
      obtain ⟨i, hCut⟩ :=
        (workBlockAt_right_ne_iff_selectedBoundary
          hb crossings x).mp hNe
      refine ⟨i, ?_⟩
      exact (crossesWorkBoundary_right_iff
        (canonicalBoundary hb crossings i).val x).mpr hCut
    · rintro ⟨i, hCross⟩
      apply (workBlockAt_right_ne_iff_selectedBoundary
        hb crossings x).mpr
      exact ⟨i, (crossesWorkBoundary_right_iff
        (canonicalBoundary hb crossings i).val x).mp hCross⟩

/-- Actual trajectory specialization of the exact one-step block-change
criterion. -/
theorem workHeadTrajectoryFrom_block_change_iff_selectedCrossing
    {T b : Nat} (hb : 0 < b) (crossings : Fin T -> Nat)
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (time : Nat) :
    workBlockAt hb crossings
        (workHeadTrajectoryFrom machine input config time) ≠
      workBlockAt hb crossings
        (workHeadTrajectoryFrom machine input config (time + 1)) <->
      ∃ i : Fin (T / b),
        WorkBoundaryCrossingAtFrom machine input config time
          (canonicalBoundary hb crossings i).val := by
  exact workBlockAt_ne_iff_crosses_selectedBoundary hb crossings
    (workHeadTrajectoryFrom_step_cases machine input config time)

/-- A directly usable time-to-block classifier for a blank-start run. -/
noncomputable def canonicalWorkBlockAtTime {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (machine : DeterministicMachine)
    (input : List Bool) (time : Nat) : Fin (T / b + 1) :=
  workBlockAt hb crossings (workHeadTrajectory machine input time)

/-- Blank-start trajectory form of the exact block-change criterion.  The
right side is an actual work-boundary crossing, not a coarse displacement
test. -/
theorem canonicalWorkBlockAtTime_change_iff_selectedCrossing
    {T b : Nat} (hb : 0 < b) (crossings : Fin T -> Nat)
    (machine : DeterministicMachine) (input : List Bool) (time : Nat) :
    canonicalWorkBlockAtTime hb crossings machine input time ≠
      canonicalWorkBlockAtTime hb crossings machine input (time + 1) <->
      ∃ i : Fin (T / b),
        WorkBoundaryCrossingAt machine input time
          (canonicalBoundary hb crossings i).val := by
  simpa only [canonicalWorkBlockAtTime, WorkBoundaryCrossingAt,
    workHeadTrajectory] using
    (workHeadTrajectoryFrom_block_change_iff_selectedCrossing hb crossings
      machine input (initialConfiguration machine) time)

/-- The fully concrete, input-dependent classifier obtained from the actual
crossing counts of the first `steps` transitions.  Its partial application in
`time` has exactly the `Nat -> Fin (steps / b + 1)` type accepted by
`ActualRunInputOrder`.  No input-independence is asserted. -/
noncomputable def actualCanonicalWorkBlockAtTime
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b) (time : Nat) : Fin (steps / b + 1) :=
  canonicalWorkBlockAtTime hb
    (fun j : Fin steps =>
      workBoundaryCrossingCount machine input steps j.val)
    machine input time

end OneTapeMagnification
end Frontier
end Pnp4
