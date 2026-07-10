import Pnp4.Frontier.OneTapeMagnification.CanonicalBoundarySelection
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Endpoint gaps for canonical boundary blocks

`CanonicalBoundarySelection` proves that selected boundaries in adjacent full
`b`-buckets are less than `2*b` positions apart.  A path decomposition also
needs the two endpoint gaps.  Under the natural condition `b ≤ T`, there is at
least one full bucket.  This file proves that the first selected boundary lies
before `b` and that the suffix from the final selected boundary to `T` has
length strictly below `2*b`.

Together with the adjacent-gap theorem, these are exactly the numerical block
diameter bounds.  They do not define block-local validators, crossing
interfaces, or a branching program.
-/

/-- Index of the first full bucket. -/
def firstFullBucketIndex {T b : Nat} (hBlocks : 0 < T / b) : Fin (T / b) :=
  ⟨0, hBlocks⟩

/-- Index of the final full bucket. -/
def lastFullBucketIndex {T b : Nat} (hBlocks : 0 < T / b) : Fin (T / b) :=
  ⟨T / b - 1, Nat.sub_lt hBlocks Nat.zero_lt_one⟩

@[simp]
theorem firstFullBucketIndex_val {T b : Nat} (hBlocks : 0 < T / b) :
    (firstFullBucketIndex hBlocks).val = 0 :=
  rfl

theorem lastFullBucketIndex_val_add_one {T b : Nat}
    (hBlocks : 0 < T / b) :
    (lastFullBucketIndex hBlocks).val + 1 = T / b := by
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hBlocks)

/-- The first canonical cut is less than one block scale from the left
endpoint. -/
theorem firstCanonicalBoundary_lt_blockSize
    {T b : Nat} (hb : 0 < b) (hBlocks : 0 < T / b)
    (crossings : Fin T → Nat) :
    (canonicalBoundary hb crossings (firstFullBucketIndex hBlocks)).val < b := by
  have hBucket :
      (canonicalBoundary hb crossings
        (firstFullBucketIndex hBlocks)).val < (0 + 1) * b :=
    (canonicalBoundary_mem_bucket hb crossings
      (firstFullBucketIndex hBlocks)).2
  simpa only [zero_add, one_mul] using hBucket

/-- The final endpoint is less than `2*b` positions to the right of the last
canonical cut.  The statement avoids truncated subtraction. -/
theorem total_lt_lastCanonicalBoundary_add_two_mul
    {T b : Nat} (hb : 0 < b) (hBlocks : 0 < T / b)
    (crossings : Fin T → Nat) :
    T <
      (canonicalBoundary hb crossings (lastFullBucketIndex hBlocks)).val +
        2 * b := by
  let last := lastFullBucketIndex hBlocks
  have hLast : last.val + 1 = T / b := by
    exact lastFullBucketIndex_val_add_one hBlocks
  have hLower : last.val * b ≤
      (canonicalBoundary hb crossings last).val :=
    (canonicalBoundary_mem_bucket hb crossings last).1
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
    _ ≤ (canonicalBoundary hb crossings last).val + 2 * b :=
      Nat.add_le_add_right hLower (2 * b)

/-- The scale assumptions used in applications imply that a full bucket
exists. -/
theorem fullBucket_exists_of_blockSize_le
    {T b : Nat} (hb : 0 < b) (hLe : b ≤ T) :
    0 < T / b :=
  Nat.div_pos hLe hb

/-- Complete numerical gap package: the left endpoint, every adjacent pair of
selected cuts, and the right endpoint all fit below the advertised scale
bounds. -/
theorem canonicalBoundary_all_gaps
    {T b : Nat} (hb : 0 < b) (hBlocks : 0 < T / b)
    (crossings : Fin T → Nat) :
    (canonicalBoundary hb crossings (firstFullBucketIndex hBlocks)).val < b ∧
      (∀ i j : Fin (T / b), j.val = i.val + 1 →
        (canonicalBoundary hb crossings i).val <
          (canonicalBoundary hb crossings j).val ∧
        (canonicalBoundary hb crossings j).val <
          (canonicalBoundary hb crossings i).val + 2 * b) ∧
      T <
        (canonicalBoundary hb crossings (lastFullBucketIndex hBlocks)).val +
          2 * b := by
  exact ⟨firstCanonicalBoundary_lt_blockSize hb hBlocks crossings,
    fun i j hAdjacent =>
      canonicalBoundary_adjacent_gap_lt_two_mul
        hb crossings i j hAdjacent,
    total_lt_lastCanonicalBoundary_add_two_mul hb hBlocks crossings⟩

end OneTapeMagnification
end Frontier
end Pnp4
