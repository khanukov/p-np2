import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalBlockSlabs
import Pnp4.Frontier.OneTapeMagnification.CanonicalCutOffsets
import Pnp4.Frontier.OneTapeMagnification.WorkSlabPersistence

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Block slabs determined by advertised cut offsets

An ambient timed `alpha` advertises one `Fin b` offset in every full bucket.
Before any minimal-crossing check is performed, those offsets already determine
an ordered family of physical cuts and hence `T / b + 1` consecutive work-tape
slabs.  This file develops that geometry directly from the advertised offsets.

The construction is intentionally independent of an actual machine run.  Every
advertised slab is nonempty; when `0 < b`, it has width at most `2 * b`; and
distinct labels give disjoint slabs.  When the offsets are the ones extracted
from a concrete run, the advertised endpoints agree definitionally with the
existing canonical endpoints.

No theorem below says that arbitrary advertised offsets are leftmost minima of
their buckets.  That is a separate validator obligation.
-/

/-- Inclusive lower endpoint of the block determined by advertised cuts. -/
def advertisedBlockLower {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) : Nat :=
  if hzero : block.val = 0 then 0
  else (cutDescriptionOfOffsets offsets
    ⟨block.val - 1, by omega⟩).val + 1

/-- Exclusive upper endpoint of the block determined by advertised cuts. -/
def advertisedBlockUpperExclusive {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) : Nat :=
  if hnext : block.val < T / b then
    (cutDescriptionOfOffsets offsets ⟨block.val, hnext⟩).val + 1
  else T + 1

/-- Width of the half-open slab determined by advertised cuts. -/
def advertisedBlockWidth {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) : Nat :=
  advertisedBlockUpperExclusive offsets block -
    advertisedBlockLower offsets block

@[simp]
theorem advertisedBlockLower_of_val_eq_zero {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1))
    (hzero : block.val = 0) :
    advertisedBlockLower offsets block = 0 := by
  simp [advertisedBlockLower, hzero]

theorem advertisedBlockLower_of_val_pos {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1))
    (hpos : 0 < block.val) :
    advertisedBlockLower offsets block =
      (cutDescriptionOfOffsets offsets
        ⟨block.val - 1, by omega⟩).val + 1 := by
  simp [advertisedBlockLower, Nat.ne_of_gt hpos]

theorem advertisedBlockUpperExclusive_of_val_lt {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1))
    (hnext : block.val < T / b) :
    advertisedBlockUpperExclusive offsets block =
      (cutDescriptionOfOffsets offsets ⟨block.val, hnext⟩).val + 1 := by
  simp [advertisedBlockUpperExclusive, hnext]

@[simp]
theorem advertisedBlockUpperExclusive_of_not_val_lt {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1))
    (hnext : ¬ block.val < T / b) :
    advertisedBlockUpperExclusive offsets block = T + 1 := by
  simp [advertisedBlockUpperExclusive, hnext]

/-- Every advertised exclusive endpoint lies within the represented interval
`[0, T + 1)`. -/
theorem advertisedBlockUpperExclusive_le_total_add_one {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    advertisedBlockUpperExclusive offsets block ≤ T + 1 := by
  unfold advertisedBlockUpperExclusive
  split
  · have hcut := (cutDescriptionOfOffsets offsets
      ⟨block.val, by assumption⟩).isLt
    omega
  · exact Nat.le_refl _

/-- Consecutive advertised block slabs share exactly one half-open endpoint. -/
theorem advertisedBlockUpperExclusive_eq_next_lower {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (current next : Fin (T / b + 1))
    (hnext : next.val = current.val + 1) :
    advertisedBlockUpperExclusive offsets current =
      advertisedBlockLower offsets next := by
  have hcurrent : current.val < T / b := by
    have hnextLe : next.val ≤ T / b := Nat.le_of_lt_succ next.isLt
    omega
  have hnextPos : 0 < next.val := by omega
  have hcutIndex :
      (⟨current.val, hcurrent⟩ : Fin (T / b)) =
        ⟨next.val - 1, by omega⟩ := by
    apply Fin.ext
    change current.val = next.val - 1
    omega
  rw [advertisedBlockUpperExclusive_of_val_lt offsets current hcurrent,
    advertisedBlockLower_of_val_pos offsets next hnextPos]
  rw [hcutIndex]

/-- Advertised cuts inherit strict order from their distinct full buckets. -/
theorem cutDescriptionOfOffsets_lt_of_index_lt {T b : Nat}
    (offsets : CanonicalCutOffsets T b) {first second : Fin (T / b)}
    (hindex : first < second) :
    (cutDescriptionOfOffsets offsets first).val <
      (cutDescriptionOfOffsets offsets second).val := by
  have hfirst := fullBucketBoundary_upper first (offsets first)
  have hsecond := fullBucketBoundary_lower second (offsets second)
  have hbucket : (first.val + 1) * b ≤ second.val * b := by
    exact Nat.mul_le_mul_right b (Nat.succ_le_of_lt hindex)
  exact hfirst.trans_le (hbucket.trans hsecond)

/-- Weak monotonicity of the advertised physical cut vector. -/
theorem cutDescriptionOfOffsets_le_of_index_le {T b : Nat}
    (offsets : CanonicalCutOffsets T b) {first second : Fin (T / b)}
    (hindex : first ≤ second) :
    (cutDescriptionOfOffsets offsets first).val ≤
      (cutDescriptionOfOffsets offsets second).val := by
  rcases hindex.eq_or_lt with hEq | hLt
  · simp [hEq]
  · exact Nat.le_of_lt
      (cutDescriptionOfOffsets_lt_of_index_lt offsets hLt)

/-- Adjacent advertised cuts are strictly ordered and less than `2 * b`
positions apart. -/
theorem cutDescriptionOfOffsets_adjacent_gap_lt_two_mul {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (first second : Fin (T / b))
    (hAdjacent : second.val = first.val + 1) :
    (cutDescriptionOfOffsets offsets first).val <
        (cutDescriptionOfOffsets offsets second).val ∧
      (cutDescriptionOfOffsets offsets second).val <
        (cutDescriptionOfOffsets offsets first).val + 2 * b := by
  have hfirstLower := fullBucketBoundary_lower first (offsets first)
  have hfirstUpper := fullBucketBoundary_upper first (offsets first)
  have hsecondLower := fullBucketBoundary_lower second (offsets second)
  have hsecondUpper := fullBucketBoundary_upper second (offsets second)
  constructor
  · calc
      (cutDescriptionOfOffsets offsets first).val <
          (first.val + 1) * b := hfirstUpper
      _ = second.val * b := by rw [hAdjacent]
      _ ≤ (cutDescriptionOfOffsets offsets second).val := hsecondLower
  · calc
      (cutDescriptionOfOffsets offsets second).val <
          (second.val + 1) * b := hsecondUpper
      _ = first.val * b + 2 * b := by
        rw [hAdjacent]
        ring
      _ ≤ (cutDescriptionOfOffsets offsets first).val + 2 * b :=
        Nat.add_le_add_right hfirstLower (2 * b)

/-- The first advertised cut is inside the first full bucket. -/
theorem firstCutDescriptionOfOffsets_lt_blockSize {T b : Nat}
    (hBlocks : 0 < T / b) (offsets : CanonicalCutOffsets T b) :
    (cutDescriptionOfOffsets offsets
      (firstFullBucketIndex hBlocks)).val < b := by
  calc
    (cutDescriptionOfOffsets offsets
        (firstFullBucketIndex hBlocks)).val =
        (offsets (firstFullBucketIndex hBlocks)).val := by
      simp [cutDescriptionOfOffsets, firstFullBucketIndex]
    _ < b := (offsets (firstFullBucketIndex hBlocks)).isLt

/-- The represented endpoint is less than `2 * b` cells beyond the final
advertised cut. -/
theorem total_lt_lastCutDescriptionOfOffsets_add_two_mul {T b : Nat}
    (hb : 0 < b) (hBlocks : 0 < T / b)
    (offsets : CanonicalCutOffsets T b) :
    T < (cutDescriptionOfOffsets offsets
      (lastFullBucketIndex hBlocks)).val + 2 * b := by
  let last := lastFullBucketIndex hBlocks
  have hLast : last.val + 1 = T / b :=
    lastFullBucketIndex_val_add_one hBlocks
  have hLower : last.val * b ≤
      (cutDescriptionOfOffsets offsets last).val :=
    fullBucketBoundary_lower last (offsets last)
  have hRemainder : T % b < b := Nat.mod_lt T hb
  have hProduct : b * (T / b) = b * (last.val + 1) :=
    congrArg (fun value => b * value) hLast.symm
  have hDecompose : T = last.val * b + (b + T % b) := by
    calc
      T = T % b + b * (T / b) := (Nat.mod_add_div T b).symm
      _ = T % b + b * (last.val + 1) := by rw [hProduct]
      _ = last.val * b + (b + T % b) := by ring
  calc
    T = last.val * b + (b + T % b) := hDecompose
    _ < last.val * b + (b + b) :=
      Nat.add_lt_add_left (Nat.add_lt_add_left hRemainder b) (last.val * b)
    _ = last.val * b + 2 * b := by ring
    _ ≤ (cutDescriptionOfOffsets offsets last).val + 2 * b :=
      Nat.add_le_add_right hLower (2 * b)

/-- Every advertised block has a genuine nonempty half-open interval. -/
theorem advertisedBlockLower_lt_upperExclusive {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    advertisedBlockLower offsets block <
      advertisedBlockUpperExclusive offsets block := by
  by_cases hNoBlocks : T / b = 0
  · have hzero : block.val = 0 := by omega
    rw [advertisedBlockLower_of_val_eq_zero offsets block hzero,
      advertisedBlockUpperExclusive_of_not_val_lt offsets block]
    · omega
    · omega
  · by_cases hzero : block.val = 0
    · have hnext : block.val < T / b := by omega
      rw [advertisedBlockLower_of_val_eq_zero offsets block hzero,
        advertisedBlockUpperExclusive_of_val_lt offsets block hnext]
      omega
    · have hpos : 0 < block.val := Nat.pos_of_ne_zero hzero
      by_cases hlast : block.val = T / b
      · have hnotNext : ¬ block.val < T / b := by omega
        rw [advertisedBlockLower_of_val_pos offsets block hpos,
          advertisedBlockUpperExclusive_of_not_val_lt offsets block hnotNext]
        have hcutLt :=
          (cutDescriptionOfOffsets offsets
            ⟨block.val - 1, by omega⟩).isLt
        omega
      · have hnext : block.val < T / b := by
          have hle : block.val ≤ T / b := Nat.le_of_lt_succ block.isLt
          omega
        let previous : Fin (T / b) := ⟨block.val - 1, by omega⟩
        let next : Fin (T / b) := ⟨block.val, hnext⟩
        have hindex : previous < next := by
          change block.val - 1 < block.val
          omega
        have hcuts := cutDescriptionOfOffsets_lt_of_index_lt offsets hindex
        rw [advertisedBlockLower_of_val_pos offsets block hpos,
          advertisedBlockUpperExclusive_of_val_lt offsets block hnext]
        change (cutDescriptionOfOffsets offsets previous).val + 1 <
          (cutDescriptionOfOffsets offsets next).val + 1
        omega

/-- Every advertised slab contains at least one work cell. -/
theorem advertisedBlockWidth_pos {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    0 < advertisedBlockWidth offsets block := by
  exact Nat.sub_pos_of_lt
    (advertisedBlockLower_lt_upperExclusive offsets block)

/-- The stored width recovers the advertised exclusive endpoint. -/
theorem advertisedBlockLower_add_width_eq_upperExclusive {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) :
    advertisedBlockLower offsets block +
        advertisedBlockWidth offsets block =
      advertisedBlockUpperExclusive offsets block := by
  have horder := advertisedBlockLower_lt_upperExclusive offsets block
  unfold advertisedBlockWidth
  omega

/-- Every block cut out by arbitrary advertised bucket offsets has width at
most `2 * b`. -/
theorem advertisedBlockWidth_le_two_mul {T b : Nat} (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    advertisedBlockWidth offsets block ≤ 2 * b := by
  by_cases hNoBlocks : T / b = 0
  · have hzero : block.val = 0 := by omega
    have hTlt : T < b := Nat.lt_of_div_eq_zero hb hNoBlocks
    rw [advertisedBlockWidth,
      advertisedBlockLower_of_val_eq_zero offsets block hzero,
      advertisedBlockUpperExclusive_of_not_val_lt offsets block]
    · omega
    · omega
  · have hBlocks : 0 < T / b := Nat.pos_of_ne_zero hNoBlocks
    by_cases hzero : block.val = 0
    · have hnext : block.val < T / b := by omega
      have hfirst :
          (⟨block.val, hnext⟩ : Fin (T / b)) =
            firstFullBucketIndex hBlocks := by
        apply Fin.ext
        simp [hzero, firstFullBucketIndex]
      have hgap := firstCutDescriptionOfOffsets_lt_blockSize hBlocks offsets
      rw [advertisedBlockWidth,
        advertisedBlockLower_of_val_eq_zero offsets block hzero,
        advertisedBlockUpperExclusive_of_val_lt offsets block hnext,
        hfirst]
      omega
    · have hpos : 0 < block.val := Nat.pos_of_ne_zero hzero
      by_cases hlast : block.val = T / b
      · have hnotNext : ¬ block.val < T / b := by omega
        have hlastIndex :
            (⟨block.val - 1, by omega⟩ : Fin (T / b)) =
              lastFullBucketIndex hBlocks := by
          apply Fin.ext
          change block.val - 1 = T / b - 1
          rw [hlast]
        have hgap := total_lt_lastCutDescriptionOfOffsets_add_two_mul
          hb hBlocks offsets
        rw [advertisedBlockWidth,
          advertisedBlockLower_of_val_pos offsets block hpos,
          advertisedBlockUpperExclusive_of_not_val_lt offsets block hnotNext,
          hlastIndex]
        omega
      · have hnext : block.val < T / b := by
          have hle : block.val ≤ T / b := Nat.le_of_lt_succ block.isLt
          omega
        let previous : Fin (T / b) := ⟨block.val - 1, by omega⟩
        let next : Fin (T / b) := ⟨block.val, hnext⟩
        have hAdjacent : next.val = previous.val + 1 := by
          simp only [previous, next]
          omega
        have hgap :=
          (cutDescriptionOfOffsets_adjacent_gap_lt_two_mul
            offsets previous next hAdjacent).2
        rw [advertisedBlockWidth,
          advertisedBlockLower_of_val_pos offsets block hpos,
          advertisedBlockUpperExclusive_of_val_lt offsets block hnext]
        change
          (cutDescriptionOfOffsets offsets next).val + 1 -
              ((cutDescriptionOfOffsets offsets previous).val + 1) ≤
            2 * b
        omega

/-- A block's exclusive endpoint is no later than every later block's lower
endpoint. -/
theorem advertisedBlockUpperExclusive_le_lower_of_lt {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    {first second : Fin (T / b + 1)} (hindex : first < second) :
    advertisedBlockUpperExclusive offsets first ≤
      advertisedBlockLower offsets second := by
  have hfirstNext : first.val < T / b := by
    have hsecondLe : second.val ≤ T / b := Nat.le_of_lt_succ second.isLt
    omega
  have hsecondPos : 0 < second.val := by omega
  let firstCut : Fin (T / b) := ⟨first.val, hfirstNext⟩
  let previousCut : Fin (T / b) := ⟨second.val - 1, by omega⟩
  have hcutsIndex : firstCut ≤ previousCut := by
    change first.val ≤ second.val - 1
    omega
  have hcuts := cutDescriptionOfOffsets_le_of_index_le offsets hcutsIndex
  rw [advertisedBlockUpperExclusive_of_val_lt offsets first hfirstNext,
    advertisedBlockLower_of_val_pos offsets second hsecondPos]
  change (cutDescriptionOfOffsets offsets firstCut).val + 1 ≤
    (cutDescriptionOfOffsets offsets previousCut).val + 1
  omega

/-- Distinct advertised block labels determine disjoint slabs. -/
theorem advertisedBlockSlabsDisjoint_of_ne {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (first second : Fin (T / b + 1)) (hne : first ≠ second) :
    WorkSlabsDisjoint
      (advertisedBlockLower offsets first)
      (advertisedBlockWidth offsets first)
      (advertisedBlockLower offsets second)
      (advertisedBlockWidth offsets second) := by
  have hfirstEndpoint :=
    advertisedBlockLower_add_width_eq_upperExclusive offsets first
  have hsecondEndpoint :=
    advertisedBlockLower_add_width_eq_upperExclusive offsets second
  intro cell hfirst hsecond
  unfold WorkCellInSlab at hfirst hsecond
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
  · have hordered := advertisedBlockUpperExclusive_le_lower_of_lt
      offsets (show first < second from hlt)
    omega
  · have hordered := advertisedBlockUpperExclusive_le_lower_of_lt
      offsets (show second < first from hgt)
    omega

/-- The block immediately to the left of an advertised cut. -/
abbrev advertisedCutLeftBlock {T b : Nat} (cut : Fin (T / b)) :
    Fin (T / b + 1) :=
  Fin.castSucc cut

/-- The block immediately to the right of an advertised cut. -/
abbrev advertisedCutRightBlock {T b : Nat} (cut : Fin (T / b)) :
    Fin (T / b + 1) :=
  Fin.succ cut

/-- The physical cut cell belongs to the slab immediately on its left. -/
theorem advertisedPhysicalCut_mem_leftBlockSlab {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (cut : Fin (T / b)) :
    WorkCellInSlab
      (advertisedBlockLower offsets (advertisedCutLeftBlock cut))
      (advertisedBlockWidth offsets (advertisedCutLeftBlock cut))
      (cutDescriptionOfOffsets offsets cut).val := by
  let left : Fin (T / b + 1) := advertisedCutLeftBlock cut
  have hnext : left.val < T / b := cut.isLt
  have hupper : advertisedBlockUpperExclusive offsets left =
      (cutDescriptionOfOffsets offsets cut).val + 1 := by
    rw [advertisedBlockUpperExclusive_of_val_lt offsets left hnext]
    congr 2
  have hlower := advertisedBlockLower_lt_upperExclusive offsets left
  have hendpoint :=
    advertisedBlockLower_add_width_eq_upperExclusive offsets left
  unfold WorkCellInSlab
  change advertisedBlockLower offsets left ≤
      (cutDescriptionOfOffsets offsets cut).val ∧
    (cutDescriptionOfOffsets offsets cut).val <
      advertisedBlockLower offsets left + advertisedBlockWidth offsets left
  omega

/-- The cell immediately to the right of a physical cut belongs to the slab
immediately on that side. -/
theorem advertisedPhysicalCut_succ_mem_rightBlockSlab {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (cut : Fin (T / b)) :
    WorkCellInSlab
      (advertisedBlockLower offsets (advertisedCutRightBlock cut))
      (advertisedBlockWidth offsets (advertisedCutRightBlock cut))
      ((cutDescriptionOfOffsets offsets cut).val + 1) := by
  let right : Fin (T / b + 1) := advertisedCutRightBlock cut
  have hpos : 0 < right.val := by simp [right]
  have hcutIndex :
      (⟨right.val - 1, by omega⟩ : Fin (T / b)) = cut := by
    apply Fin.ext
    change right.val - 1 = cut.val
    simp [right]
  have hlower : advertisedBlockLower offsets right =
      (cutDescriptionOfOffsets offsets cut).val + 1 := by
    rw [advertisedBlockLower_of_val_pos offsets right hpos, hcutIndex]
  have hwidth := advertisedBlockWidth_pos offsets right
  unfold WorkCellInSlab
  change advertisedBlockLower offsets right ≤
      (cutDescriptionOfOffsets offsets cut).val + 1 ∧
    (cutDescriptionOfOffsets offsets cut).val + 1 <
      advertisedBlockLower offsets right + advertisedBlockWidth offsets right
  omega

/-- Every represented work cell has exactly one advertised slab owner.  The
existence proof chooses the first advertised exclusive endpoint to the right
of the cell; disjointness supplies uniqueness. -/
theorem workCell_existsUnique_advertisedBlockSlab {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (cell : Fin (T + 1)) :
    ∃! block : Fin (T / b + 1),
      WorkCellInSlab
        (advertisedBlockLower offsets block)
        (advertisedBlockWidth offsets block)
        cell.val := by
  let endpointAfter : Nat → Prop := fun k =>
    ∃ hk : k < T / b + 1,
      cell.val < advertisedBlockUpperExclusive offsets ⟨k, hk⟩
  have hexists : ∃ k, endpointAfter k := by
    refine ⟨T / b, by
      refine ⟨by omega, ?_⟩
      rw [advertisedBlockUpperExclusive_of_not_val_lt]
      · exact cell.isLt
      · change ¬ T / b < T / b
        exact Nat.lt_irrefl _⟩
  let ownerValue := Nat.find hexists
  have hownerSpec := Nat.find_spec hexists
  let owner : Fin (T / b + 1) := ⟨ownerValue, hownerSpec.choose⟩
  have hownerUpper :
      cell.val < advertisedBlockUpperExclusive offsets owner := by
    exact hownerSpec.choose_spec
  have hownerLower : advertisedBlockLower offsets owner ≤ cell.val := by
    by_cases hzero : owner.val = 0
    · rw [advertisedBlockLower_of_val_eq_zero offsets owner hzero]
      exact Nat.zero_le _
    · have hpos : 0 < owner.val := Nat.pos_of_ne_zero hzero
      let previous : Fin (T / b + 1) := ⟨owner.val - 1, by omega⟩
      have hownerValuePos : 0 < ownerValue := by
        simpa [owner, ownerValue] using hpos
      have hpreviousNot : ¬ endpointAfter previous.val := by
        exact Nat.find_min hexists (by
          change ownerValue - 1 < ownerValue
          omega)
      have hpreviousUpper :
          advertisedBlockUpperExclusive offsets previous ≤ cell.val := by
        apply Nat.le_of_not_gt
        intro hcell
        apply hpreviousNot
        exact ⟨previous.isLt, hcell⟩
      have hadjacent : owner.val = previous.val + 1 := by
        simp only [previous]
        omega
      have hshared := advertisedBlockUpperExclusive_eq_next_lower
        offsets previous owner hadjacent
      omega
  have hendpoint :=
    advertisedBlockLower_add_width_eq_upperExclusive offsets owner
  have howner : WorkCellInSlab
      (advertisedBlockLower offsets owner)
      (advertisedBlockWidth offsets owner) cell.val := by
    unfold WorkCellInSlab
    constructor
    · exact hownerLower
    · omega
  refine ⟨owner, howner, ?_⟩
  intro other hother
  by_contra hne
  exact advertisedBlockSlabsDisjoint_of_ne offsets owner other
    (fun h => hne h.symm) cell howner hother

/-- Actual canonical offsets reproduce the existing actual-run lower
endpoint exactly. -/
@[simp]
theorem advertisedBlockLower_canonicalCutOffsets
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (block : Fin (T / b + 1)) :
    advertisedBlockLower (canonicalCutOffsets machine input T b hb) block =
      canonicalBlockLower hb
        (fun j : Fin T => workBoundaryCrossingCount machine input T j.val)
        block := by
  rfl

/-- Actual canonical offsets reproduce the existing actual-run exclusive
upper endpoint exactly. -/
@[simp]
theorem advertisedBlockUpperExclusive_canonicalCutOffsets
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (block : Fin (T / b + 1)) :
    advertisedBlockUpperExclusive
        (canonicalCutOffsets machine input T b hb) block =
      canonicalBlockUpperExclusive hb
        (fun j : Fin T => workBoundaryCrossingCount machine input T j.val)
        block := by
  rfl

/-- Actual canonical offsets reproduce the existing actual-run slab width
exactly. -/
@[simp]
theorem advertisedBlockWidth_canonicalCutOffsets
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (block : Fin (T / b + 1)) :
    advertisedBlockWidth (canonicalCutOffsets machine input T b hb) block =
      canonicalBlockWidth hb
        (fun j : Fin T => workBoundaryCrossingCount machine input T j.val)
        block := by
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
