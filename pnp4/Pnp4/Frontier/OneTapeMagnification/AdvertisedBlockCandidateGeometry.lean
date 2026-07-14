import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutBlockSlabs

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Candidate-cut geometry inside one advertised work block

The physical slab between two advertised cuts contains exactly the candidate
boundaries needed for the two one-sided leftmost-minimum tests:

* offsets strictly to the right of the left cut, in the preceding bucket;
* offsets strictly to the left of the right cut, in the following bucket.

This is the geometric reason a block-ordered one-pass validator needs at most
two vectors of `b` counters.  The selected cuts themselves are the slab's
outer boundaries, and their crossing multiplicities can be hardwired from
the timed alpha.
-/

/-- Both cells adjacent to a work-tape boundary lie in the advertised slab.
Equivalently, the boundary can be crossed without leaving that block. -/
def WorkBoundaryStrictlyInsideAdvertisedBlock {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (boundary : Fin T) : Prop :=
  advertisedBlockLower offsets block ≤ boundary.val ∧
    boundary.val + 1 < advertisedBlockUpperExclusive offsets block

/-- For every nonfirst block, its lower endpoint is immediately to the right
of the selected cut in the preceding bucket. -/
theorem advertisedBlockLower_eq_leftSelectedCut_add_one {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hpos : 0 < block.val) :
    advertisedBlockLower offsets block =
      (fullBucketBoundary
        (⟨block.val - 1, by omega⟩ : Fin (T / b))
        (offsets ⟨block.val - 1, by omega⟩)).val + 1 := by
  exact advertisedBlockLower_of_val_pos offsets block hpos

/-- For every nonfinal block, its exclusive upper endpoint is immediately to
the right of the selected cut in the next bucket. -/
theorem advertisedBlockUpperExclusive_eq_rightSelectedCut_add_one
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hnext : block.val < T / b) :
    advertisedBlockUpperExclusive offsets block =
      (fullBucketBoundary
        (⟨block.val, hnext⟩ : Fin (T / b))
        (offsets ⟨block.val, hnext⟩)).val + 1 := by
  exact advertisedBlockUpperExclusive_of_val_lt offsets block hnext

/-- Every candidate strictly to the right of the left selected offset is an
internal boundary of this block.  This includes the final tail block. -/
theorem leftBucketTailCandidate_strictlyInsideAdvertisedBlock
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hpos : 0 < block.val)
    (candidate : Fin b)
    (hcandidate :
      (offsets (⟨block.val - 1, by omega⟩ : Fin (T / b))).val <
        candidate.val) :
    WorkBoundaryStrictlyInsideAdvertisedBlock offsets block
      (fullBucketBoundary
        (⟨block.val - 1, by omega⟩ : Fin (T / b)) candidate) := by
  let left : Fin (T / b) := ⟨block.val - 1, by omega⟩
  have hcandidate' : (offsets left).val < candidate.val := by
    simpa [left] using hcandidate
  have hlower := advertisedBlockLower_of_val_pos offsets block hpos
  constructor
  · rw [hlower]
    change (fullBucketBoundary left (offsets left)).val + 1 ≤
      (fullBucketBoundary left candidate).val
    simp only [fullBucketBoundary_val]
    exact Nat.add_le_add_left (Nat.succ_le_of_lt hcandidate') (left.val * b)
  · by_cases hnext : block.val < T / b
    · let right : Fin (T / b) := ⟨block.val, hnext⟩
      rw [advertisedBlockUpperExclusive_of_val_lt offsets block hnext]
      have hleftUpper := fullBucketBoundary_upper left candidate
      have hrightLower := fullBucketBoundary_lower right (offsets right)
      have hindex : left.val + 1 = right.val := by
        simp [left, right]
        omega
      rw [hindex] at hleftUpper
      change (fullBucketBoundary left candidate).val + 1 <
        (fullBucketBoundary right (offsets right)).val + 1
      omega
    · rw [advertisedBlockUpperExclusive_of_not_val_lt offsets block hnext]
      change (fullBucketBoundary left candidate).val + 1 < T + 1
      omega

/-- Every candidate strictly to the left of the right selected offset is an
internal boundary of this block.  This includes the initial prefix block. -/
theorem rightBucketPrefixCandidate_strictlyInsideAdvertisedBlock
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hnext : block.val < T / b)
    (candidate : Fin b)
    (hcandidate : candidate.val <
      (offsets (⟨block.val, hnext⟩ : Fin (T / b))).val) :
    WorkBoundaryStrictlyInsideAdvertisedBlock offsets block
      (fullBucketBoundary
        (⟨block.val, hnext⟩ : Fin (T / b)) candidate) := by
  let right : Fin (T / b) := ⟨block.val, hnext⟩
  have hcandidate' : candidate.val < (offsets right).val := by
    simpa [right] using hcandidate
  constructor
  · by_cases hzero : block.val = 0
    · rw [advertisedBlockLower_of_val_eq_zero offsets block hzero]
      omega
    · have hpos : 0 < block.val := Nat.pos_of_ne_zero hzero
      let left : Fin (T / b) := ⟨block.val - 1, by omega⟩
      rw [advertisedBlockLower_of_val_pos offsets block hpos]
      have hleftUpper := fullBucketBoundary_upper left (offsets left)
      have hrightLower := fullBucketBoundary_lower right candidate
      have hindex : left.val + 1 = right.val := by
        simp [left, right]
        omega
      rw [hindex] at hleftUpper
      change (fullBucketBoundary left (offsets left)).val + 1 ≤
        (fullBucketBoundary right candidate).val
      omega
  · rw [advertisedBlockUpperExclusive_of_val_lt offsets block hnext]
    change (fullBucketBoundary right candidate).val + 1 <
      (fullBucketBoundary right (offsets right)).val + 1
    simp only [fullBucketBoundary_val]
    exact Nat.add_lt_add_left (Nat.add_lt_add_right hcandidate' 1)
      (right.val * b)

/-- A left-bucket candidate no farther right than the selected offset lies on
or outside the left side of the slab. -/
theorem leftBucketNonTailCandidate_beforeAdvertisedBlock
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hpos : 0 < block.val)
    (candidate : Fin b)
    (hcandidate : candidate.val ≤
      (offsets (⟨block.val - 1, by omega⟩ : Fin (T / b))).val) :
    (fullBucketBoundary
        (⟨block.val - 1, by omega⟩ : Fin (T / b)) candidate).val <
      advertisedBlockLower offsets block := by
  let left : Fin (T / b) := ⟨block.val - 1, by omega⟩
  have hcandidate' : candidate.val ≤ (offsets left).val := by
    simpa [left] using hcandidate
  rw [advertisedBlockLower_of_val_pos offsets block hpos]
  change (fullBucketBoundary left candidate).val <
    (fullBucketBoundary left (offsets left)).val + 1
  simp only [fullBucketBoundary_val]
  omega

/-- A right-bucket candidate no farther left than the selected offset lies on
or outside the right side of the slab. -/
theorem rightBucketNonPrefixCandidate_afterAdvertisedBlock
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hnext : block.val < T / b)
    (candidate : Fin b)
    (hcandidate :
      (offsets (⟨block.val, hnext⟩ : Fin (T / b))).val ≤ candidate.val) :
    advertisedBlockUpperExclusive offsets block ≤
      (fullBucketBoundary
        (⟨block.val, hnext⟩ : Fin (T / b)) candidate).val + 1 := by
  let right : Fin (T / b) := ⟨block.val, hnext⟩
  have hcandidate' : (offsets right).val ≤ candidate.val := by
    simpa [right] using hcandidate
  rw [advertisedBlockUpperExclusive_of_val_lt offsets block hnext]
  change (fullBucketBoundary right (offsets right)).val + 1 ≤
    (fullBucketBoundary right candidate).val + 1
  simp only [fullBucketBoundary_val]
  omega

end OneTapeMagnification
end Frontier
end Pnp4
