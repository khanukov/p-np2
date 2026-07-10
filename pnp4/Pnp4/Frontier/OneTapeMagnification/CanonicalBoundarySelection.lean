import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Basic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Canonical low-crossing boundaries in full buckets

This file isolates the finite counting fact used by block decompositions of a
one-tape computation.  Split the boundary positions `0, ..., T - 1` into the
`T / b` *full* buckets of length `b`; the final remainder is deliberately not
claimed to be covered.  In every full bucket we select the leftmost boundary
whose crossing count is minimum in that bucket.

The selected counts obey the exact charging inequality

`b * (sum of selected counts) <= (sum over full buckets) <= total sum`.

Consequently, if the total crossing count is at most `T`, the sum of selected
counts is at most `T / b`.  No machine-simulation claim is made here: this is
only the combinatorial core needed by such a simulation.
-/

/-- Boundary at offset `k` in full bucket `i`.  The type of `i` guarantees
that the whole bucket lies before `T`; no claim is made about the remainder
after `(T / b) * b`. -/
def fullBucketBoundary {T b : Nat} (i : Fin (T / b)) (k : Fin b) : Fin T :=
  ⟨i.val * b + k.val, by
    have hk : i.val * b + k.val < (i.val + 1) * b := by
      calc
        i.val * b + k.val < i.val * b + b :=
          Nat.add_lt_add_left k.isLt (i.val * b)
        _ = (i.val + 1) * b := by simp [Nat.add_mul]
    have hi : i.val + 1 ≤ T / b := Nat.succ_le_of_lt i.isLt
    have hfull : (i.val + 1) * b ≤ (T / b) * b :=
      Nat.mul_le_mul_right b hi
    exact lt_of_lt_of_le hk (hfull.trans (Nat.div_mul_le_self T b))⟩

@[simp]
theorem fullBucketBoundary_val {T b : Nat} (i : Fin (T / b)) (k : Fin b) :
    (fullBucketBoundary i k).val = i.val * b + k.val :=
  rfl

/-- Every boundary selected from bucket `i` lies at or to the right of its
left endpoint. -/
theorem fullBucketBoundary_lower {T b : Nat} (i : Fin (T / b)) (k : Fin b) :
    i.val * b ≤ (fullBucketBoundary i k).val := by
  simp [fullBucketBoundary]

/-- Every boundary selected from bucket `i` lies strictly before the right
endpoint `(i + 1) * b`. -/
theorem fullBucketBoundary_upper {T b : Nat} (i : Fin (T / b)) (k : Fin b) :
    (fullBucketBoundary i k).val < (i.val + 1) * b := by
  calc
    i.val * b + k.val < i.val * b + b :=
      Nat.add_lt_add_left k.isLt (i.val * b)
    _ = (i.val + 1) * b := by simp [Nat.add_mul]

/-- The product coordinate `(bucket, offset)` is uniquely determined by its
boundary position. -/
theorem fullBucketBoundary_injective {T b : Nat} :
    Function.Injective
      (fun p : Fin (T / b) × Fin b => fullBucketBoundary p.1 p.2) := by
  intro p q hpq
  have hval := congrArg Fin.val hpq
  have hBucket : p.1.val = q.1.val := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hqp
      have hstep : q.1.val + 1 ≤ p.1.val := Nat.succ_le_of_lt hqp
      have hmul : (q.1.val + 1) * b ≤ p.1.val * b :=
        Nat.mul_le_mul_right b hstep
      have hqUpper := fullBucketBoundary_upper q.1 q.2
      have hpLower := fullBucketBoundary_lower p.1 p.2
      have hlt : (fullBucketBoundary q.1 q.2).val <
          (fullBucketBoundary p.1 p.2).val :=
        lt_of_lt_of_le hqUpper (hmul.trans hpLower)
      exact (Nat.ne_of_lt hlt) hval.symm
    · apply Nat.le_of_not_gt
      intro hpqBucket
      have hstep : p.1.val + 1 ≤ q.1.val := Nat.succ_le_of_lt hpqBucket
      have hmul : (p.1.val + 1) * b ≤ q.1.val * b :=
        Nat.mul_le_mul_right b hstep
      have hpUpper := fullBucketBoundary_upper p.1 p.2
      have hqLower := fullBucketBoundary_lower q.1 q.2
      have hlt : (fullBucketBoundary p.1 p.2).val <
          (fullBucketBoundary q.1 q.2).val :=
        lt_of_lt_of_le hpUpper (hmul.trans hqLower)
      exact (Nat.ne_of_lt hlt) hval
  have hOffset : p.2.val = q.2.val := by
    simp only [fullBucketBoundary_val] at hval
    rw [hBucket] at hval
    exact Nat.add_left_cancel hval
  apply Prod.ext
  · exact Fin.ext hBucket
  · exact Fin.ext hOffset

private def IsBucketMinimum {T b : Nat} (crossings : Fin T → Nat)
    (i : Fin (T / b)) (k : Nat) : Prop :=
  ∃ hk : k < b,
    ∀ l : Fin b,
      crossings (fullBucketBoundary i ⟨k, hk⟩) ≤
        crossings (fullBucketBoundary i l)

private theorem isBucketMinimum_exists {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) :
    ∃ k, IsBucketMinimum crossings i k := by
  let zeroOffset : Fin b := ⟨0, hb⟩
  have hne : (Finset.univ : Finset (Fin b)).Nonempty :=
    ⟨zeroOffset, Finset.mem_univ zeroOffset⟩
  obtain ⟨k, -, hkMin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin b))
      (fun l => crossings (fullBucketBoundary i l)) hne
  refine ⟨k.val, k.isLt, ?_⟩
  intro l
  exact hkMin l (Finset.mem_univ l)

/-- The least offset which attains the minimum crossing count in bucket `i`.
Using `Nat.find` makes the tie-breaking rule leftmost. -/
noncomputable def canonicalBoundaryOffset {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) : Fin b := by
  classical
  let hex := isBucketMinimum_exists hb crossings i
  exact ⟨Nat.find hex, (Nat.find_spec hex).choose⟩

/-- The canonical minimum-crossing boundary in a full bucket. -/
noncomputable def canonicalBoundary {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) : Fin T :=
  fullBucketBoundary i (canonicalBoundaryOffset hb crossings i)

@[simp]
theorem canonicalBoundary_val {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) :
    (canonicalBoundary hb crossings i).val =
      i.val * b + (canonicalBoundaryOffset hb crossings i).val :=
  rfl

/-- The canonical boundary lies in its advertised half-open bucket. -/
theorem canonicalBoundary_mem_bucket {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) :
    i.val * b ≤ (canonicalBoundary hb crossings i).val ∧
      (canonicalBoundary hb crossings i).val < (i.val + 1) * b := by
  exact ⟨fullBucketBoundary_lower i _, fullBucketBoundary_upper i _⟩

/-- Canonical boundaries in adjacent full buckets are strictly ordered, and
the later one is less than `2 * b` positions to the right of the earlier one.
The second conjunct is written without truncated subtraction. -/
theorem canonicalBoundary_adjacent_gap_lt_two_mul {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i j : Fin (T / b))
    (hAdjacent : j.val = i.val + 1) :
    (canonicalBoundary hb crossings i).val <
        (canonicalBoundary hb crossings j).val ∧
      (canonicalBoundary hb crossings j).val <
        (canonicalBoundary hb crossings i).val + 2 * b := by
  have hi := canonicalBoundary_mem_bucket hb crossings i
  have hj := canonicalBoundary_mem_bucket hb crossings j
  constructor
  · calc
      (canonicalBoundary hb crossings i).val < (i.val + 1) * b := hi.2
      _ = j.val * b := by rw [hAdjacent]
      _ ≤ (canonicalBoundary hb crossings j).val := hj.1
  · calc
      (canonicalBoundary hb crossings j).val < (j.val + 1) * b := hj.2
      _ = i.val * b + 2 * b := by
        rw [hAdjacent]
        simp [Nat.succ_mul, Nat.add_assoc]
      _ ≤ (canonicalBoundary hb crossings i).val + 2 * b :=
        Nat.add_le_add_right hi.1 (2 * b)

/-- The selected crossing count is no larger than the count at any boundary
in the same full bucket. -/
theorem canonicalBoundary_is_minimum {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) (l : Fin b) :
    crossings (canonicalBoundary hb crossings i) ≤
      crossings (fullBucketBoundary i l) := by
  classical
  let hex := isBucketMinimum_exists hb crossings i
  have hspec := (Nat.find_spec hex).choose_spec l
  simpa [canonicalBoundary, canonicalBoundaryOffset, hex] using hspec

/-- If another offset has the same crossing count as the canonical minimum,
then the canonical offset is to its left. -/
theorem canonicalBoundary_tie_leftmost {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) (l : Fin b)
    (hTie : crossings (fullBucketBoundary i l) =
      crossings (canonicalBoundary hb crossings i)) :
    (canonicalBoundaryOffset hb crossings i).val ≤ l.val := by
  classical
  let hex := isBucketMinimum_exists hb crossings i
  apply Nat.find_min' hex
  refine ⟨l.isLt, ?_⟩
  intro m
  rw [hTie]
  exact canonicalBoundary_is_minimum hb crossings i m

/-- All full buckets, represented by their `(bucket, offset)` coordinates. -/
def fullBucketCoordinates (T b : Nat) : Finset (Fin (T / b) × Fin b) :=
  Finset.univ

/-- The set of boundary positions covered by full buckets.  Its complement
inside `Fin T` is exactly where a possible final remainder may live. -/
def fullBucketBoundaries (T b : Nat) : Finset (Fin T) :=
  (fullBucketCoordinates T b).image
    (fun p => fullBucketBoundary p.1 p.2)

/-- Summing over covered boundary positions is the same as summing over the
injective bucket/offset coordinates. -/
theorem sum_fullBucketBoundaries_eq_coordinates {T b : Nat}
    (crossings : Fin T → Nat) :
    ∑ j ∈ fullBucketBoundaries T b, crossings j =
      ∑ p : Fin (T / b) × Fin b,
        crossings (fullBucketBoundary p.1 p.2) := by
  classical
  simpa [fullBucketBoundaries, fullBucketCoordinates] using
    (Finset.sum_image (f := crossings)
      (fullBucketBoundary_injective (T := T) (b := b)).injOn)

/-- The sum over the covered full-bucket boundaries is bounded by the sum over
all `T` boundary positions. -/
theorem sum_fullBucketBoundaries_le_total {T b : Nat}
    (crossings : Fin T → Nat) :
    ∑ j ∈ fullBucketBoundaries T b, crossings j ≤ ∑ j, crossings j := by
  classical
  exact Finset.sum_le_sum_of_subset (fun _ _ => Finset.mem_univ _)

/-- In each bucket, `b` copies of the selected minimum can be charged to the
`b` actual boundary counts in that bucket. -/
theorem bucket_minimum_mul_le_bucket_sum {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) :
    b * crossings (canonicalBoundary hb crossings i) ≤
      ∑ l : Fin b, crossings (fullBucketBoundary i l) := by
  calc
    b * crossings (canonicalBoundary hb crossings i) =
        ∑ _l : Fin b, crossings (canonicalBoundary hb crossings i) := by
      simp
    _ ≤ ∑ l : Fin b, crossings (fullBucketBoundary i l) :=
      Finset.sum_le_sum (fun l _ =>
        canonicalBoundary_is_minimum hb crossings i l)

/-- Exact aggregate charging inequality for all full buckets. -/
theorem canonicalBoundary_charging {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) :
    b * (∑ i : Fin (T / b), crossings (canonicalBoundary hb crossings i)) ≤
      ∑ j ∈ fullBucketBoundaries T b, crossings j := by
  calc
    b * (∑ i : Fin (T / b), crossings (canonicalBoundary hb crossings i)) =
        ∑ i : Fin (T / b),
          b * crossings (canonicalBoundary hb crossings i) := by
      simp [Finset.mul_sum]
    _ ≤ ∑ i : Fin (T / b),
        ∑ l : Fin b, crossings (fullBucketBoundary i l) :=
      Finset.sum_le_sum (fun i _ =>
        bucket_minimum_mul_le_bucket_sum hb crossings i)
    _ = ∑ j ∈ fullBucketBoundaries T b, crossings j := by
      rw [sum_fullBucketBoundaries_eq_coordinates crossings]
      exact (Fintype.sum_prod_type
        (fun p : Fin (T / b) × Fin b =>
          crossings (fullBucketBoundary p.1 p.2))).symm

/-- Full chain: selected minima charge into the covered boundaries, which in
turn are a subset of all boundary positions. -/
theorem canonicalBoundary_charging_le_total {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) :
    b * (∑ i : Fin (T / b), crossings (canonicalBoundary hb crossings i)) ≤
      ∑ j, crossings j :=
  (canonicalBoundary_charging hb crossings).trans
    (sum_fullBucketBoundaries_le_total crossings)

/-- If total crossings are at most `T`, the selected counts sum to at most
`T / b`.  This uses floor division exactly; no divisibility hypothesis and no
coverage of the final remainder are assumed. -/
theorem sum_canonicalBoundary_le_div {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (hTotal : (∑ j, crossings j) ≤ T) :
    (∑ i : Fin (T / b), crossings (canonicalBoundary hb crossings i)) ≤
      T / b := by
  rw [Nat.le_div_iff_mul_le hb]
  simpa [Nat.mul_comm] using
    (canonicalBoundary_charging_le_total hb crossings).trans hTotal

end OneTapeMagnification
end Frontier
end Pnp4
