import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutMinimalityChecker

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One-sided form of the leftmost-minimum cut check

For a selected offset, candidates to its left must have *strictly* larger
crossing count, while candidates to its right need only have at least its
count.  This is exactly equivalent to minimum plus leftmost tie-breaking.

The asymmetric form is the one a block-ordered validator can check locally:
the prefix candidates of a bucket lie in the block to the selected cut's
left, and the tail candidates lie in the block to its right.
-/

/-- Abstract one-sided comparison condition for a selected value and a vector
of candidate values. -/
def OneSidedLeftmostMinimum {b : Nat}
    (selected : Nat) (offset : Fin b) (candidates : Fin b → Nat) : Prop :=
  (∀ candidate : Fin b, candidate.val < offset.val →
      selected < candidates candidate) ∧
    ∀ candidate : Fin b, offset.val < candidate.val →
      selected ≤ candidates candidate

/-- One-sided comparisons are exactly minimum plus leftmost tie-breaking when
the selected value is the vector coordinate at `offset`. -/
theorem oneSidedLeftmostMinimum_iff_minimum_and_leftmost {b : Nat}
    (values : Fin b → Nat) (offset : Fin b) :
    OneSidedLeftmostMinimum (values offset) offset values ↔
      (∀ candidate : Fin b, values offset ≤ values candidate) ∧
        ∀ candidate : Fin b,
          values candidate = values offset → offset.val ≤ candidate.val := by
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · intro candidate
      rcases lt_trichotomy candidate.val offset.val with hlt | heq | hgt
      · exact Nat.le_of_lt (hleft candidate hlt)
      · have hoffset : candidate = offset := Fin.ext heq
        simp [hoffset]
      · exact hright candidate hgt
    · intro candidate heq
      by_contra hnot
      have hlt : candidate.val < offset.val := by omega
      have hstrict := hleft candidate hlt
      omega
  · rintro ⟨hminimum, hleftmost⟩
    constructor
    · intro candidate hlt
      have hle := hminimum candidate
      apply Nat.lt_of_le_of_ne hle
      intro heq
      have hoffsetLe := hleftmost candidate heq.symm
      omega
    · intro candidate _
      exact hminimum candidate

/-- Bucket-specialized one-sided condition is exactly the existing semantic
`AdvertisedCutOffsetIsLeftmostMinimum`. -/
theorem oneSidedLeftmostMinimum_bucket_iff
    {T b : Nat} (crossings : Fin T → Nat)
    (bucket : Fin (T / b)) (offset : Fin b) :
    OneSidedLeftmostMinimum
        (crossings (fullBucketBoundary bucket offset)) offset
        (fun candidate => crossings (fullBucketBoundary bucket candidate)) ↔
      AdvertisedCutOffsetIsLeftmostMinimum crossings bucket offset := by
  exact oneSidedLeftmostMinimum_iff_minimum_and_leftmost
    (fun candidate => crossings (fullBucketBoundary bucket candidate)) offset

/-- Executable finite one-sided comparison checker. -/
def oneSidedLeftmostMinimumCheck {b : Nat}
    (selected : Nat) (offset : Fin b)
    (candidates : Fin b → Nat) : Bool :=
  decide
    ((∀ candidate : Fin b, candidate.val < offset.val →
        selected < candidates candidate) ∧
      ∀ candidate : Fin b, offset.val < candidate.val →
        selected ≤ candidates candidate)

/-- Exact reflection of the executable one-sided checker. -/
theorem oneSidedLeftmostMinimumCheck_eq_true_iff {b : Nat}
    (selected : Nat) (offset : Fin b) (candidates : Fin b → Nat) :
    oneSidedLeftmostMinimumCheck selected offset candidates = true ↔
      OneSidedLeftmostMinimum selected offset candidates := by
  simp [oneSidedLeftmostMinimumCheck, OneSidedLeftmostMinimum]

/-- With the selected coordinate supplied exactly, the one-sided Boolean
checker equals the pre-existing leftmost-minimum checker. -/
theorem oneSidedLeftmostMinimumCheck_eq_advertisedCutCheck
    {T b : Nat} (crossings : Fin T → Nat)
    (bucket : Fin (T / b)) (offset : Fin b) :
    oneSidedLeftmostMinimumCheck
        (crossings (fullBucketBoundary bucket offset)) offset
        (fun candidate => crossings (fullBucketBoundary bucket candidate)) =
      advertisedCutOffsetLeftmostMinimumCheck crossings bucket offset := by
  rw [Bool.eq_iff_iff,
    oneSidedLeftmostMinimumCheck_eq_true_iff,
    advertisedCutOffsetLeftmostMinimumCheck_eq_true_iff,
    oneSidedLeftmostMinimum_bucket_iff]

end OneTapeMagnification
end Frontier
end Pnp4
