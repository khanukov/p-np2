import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedCanonicalAlpha

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact checker for advertised leftmost-minimum cuts

An ambient timed alpha advertises one offset in every full bucket, but the
ambient carrier does not itself require those offsets to be the canonical
cuts of the represented run.  This file closes that semantic validation gap
against a supplied crossing-count profile and then specializes it to the
actual blank-start run.

The Boolean checker is exact: it accepts precisely when every advertised
offset minimizes the crossing count in its bucket and is no farther right
than any other minimizer.  That condition uniquely characterizes
`canonicalBoundaryOffset`.  For actual crossing counts, acceptance is
therefore equivalent both to equality with `canonicalCutOffsets` and to
extensional equality of the reconstructed physical cuts with
`canonicalCutDescription`.

This is an executable finite checker at the Lean-definition level, but it is
not yet the small-width local-counter compilation required by the MMW
branching-program argument.  It directly evaluates the actual run's crossing
count at every candidate boundary.  A later carrier construction must stream
or otherwise certify those per-candidate counts, their comparisons, and the
leftmost tie-break within the claimed width bound.  No such width conclusion
is hidden here.
-/

/-- An advertised offset is a minimum of its bucket and is to the left of
every offset tied with it.  The second conjunct makes the tie-break explicit
rather than relying on uniqueness of a chosen implementation. -/
abbrev AdvertisedCutOffsetIsLeftmostMinimum {T b : Nat}
    (crossings : Fin T → Nat) (bucket : Fin (T / b))
    (offset : Fin b) : Prop :=
  (∀ candidate : Fin b,
      crossings (fullBucketBoundary bucket offset) ≤
        crossings (fullBucketBoundary bucket candidate)) ∧
    ∀ candidate : Fin b,
      crossings (fullBucketBoundary bucket candidate) =
          crossings (fullBucketBoundary bucket offset) →
        offset.val ≤ candidate.val

/-- Finite Boolean checker for one advertised bucket offset. -/
def advertisedCutOffsetLeftmostMinimumCheck {T b : Nat}
    (crossings : Fin T → Nat) (bucket : Fin (T / b))
    (offset : Fin b) : Bool :=
  decide (AdvertisedCutOffsetIsLeftmostMinimum crossings bucket offset)

/-- Exact reflection for the one-bucket checker. -/
theorem advertisedCutOffsetLeftmostMinimumCheck_eq_true_iff {T b : Nat}
    (crossings : Fin T → Nat) (bucket : Fin (T / b))
    (offset : Fin b) :
    advertisedCutOffsetLeftmostMinimumCheck crossings bucket offset = true ↔
      AdvertisedCutOffsetIsLeftmostMinimum crossings bucket offset := by
  simp [advertisedCutOffsetLeftmostMinimumCheck]

/-- The semantic leftmost-minimum condition uniquely characterizes the
existing canonical offset selected with `Nat.find`. -/
theorem advertisedCutOffsetIsLeftmostMinimum_iff_eq_canonicalBoundaryOffset
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (bucket : Fin (T / b)) (offset : Fin b) :
    AdvertisedCutOffsetIsLeftmostMinimum crossings bucket offset ↔
      offset = canonicalBoundaryOffset hb crossings bucket := by
  constructor
  · rintro ⟨hminimum, hleftmost⟩
    have hcanonicalLe :
        crossings
            (fullBucketBoundary bucket
              (canonicalBoundaryOffset hb crossings bucket)) ≤
          crossings (fullBucketBoundary bucket offset) := by
      simpa [canonicalBoundary] using
        canonicalBoundary_is_minimum hb crossings bucket offset
    have hoffsetLe :
        crossings (fullBucketBoundary bucket offset) ≤
          crossings
            (fullBucketBoundary bucket
              (canonicalBoundaryOffset hb crossings bucket)) :=
      hminimum (canonicalBoundaryOffset hb crossings bucket)
    have hcount :
        crossings (fullBucketBoundary bucket offset) =
          crossings
            (fullBucketBoundary bucket
              (canonicalBoundaryOffset hb crossings bucket)) :=
      Nat.le_antisymm hoffsetLe hcanonicalLe
    apply Fin.ext
    apply Nat.le_antisymm
    · exact hleftmost
        (canonicalBoundaryOffset hb crossings bucket) hcount.symm
    · exact canonicalBoundary_tie_leftmost hb crossings bucket offset (by
        simpa [canonicalBoundary] using hcount)
  · intro hoffset
    subst offset
    constructor
    · intro candidate
      simpa [canonicalBoundary] using
        canonicalBoundary_is_minimum hb crossings bucket candidate
    · intro candidate hcount
      exact canonicalBoundary_tie_leftmost hb crossings bucket candidate (by
        simpa [canonicalBoundary] using hcount)

/-- Every advertised bucket offset satisfies the exact leftmost-minimum
condition for one crossing-count profile. -/
abbrev AdvertisedCutOffsetsAreLeftmostMinimum {T b : Nat}
    (crossings : Fin T → Nat) (offsets : CanonicalCutOffsets T b) : Prop :=
  ∀ bucket : Fin (T / b),
    AdvertisedCutOffsetIsLeftmostMinimum crossings bucket (offsets bucket)

/-- Finite Boolean checker for a complete advertised offset vector. -/
def advertisedCutOffsetsLeftmostMinimumCheck {T b : Nat}
    (crossings : Fin T → Nat) (offsets : CanonicalCutOffsets T b) : Bool :=
  decide (AdvertisedCutOffsetsAreLeftmostMinimum crossings offsets)

/-- Exact reflection for the complete-vector checker. -/
theorem advertisedCutOffsetsLeftmostMinimumCheck_eq_true_iff {T b : Nat}
    (crossings : Fin T → Nat) (offsets : CanonicalCutOffsets T b) :
    advertisedCutOffsetsLeftmostMinimumCheck crossings offsets = true ↔
      AdvertisedCutOffsetsAreLeftmostMinimum crossings offsets := by
  simp [advertisedCutOffsetsLeftmostMinimumCheck]

/-- Simultaneous leftmost-minimum validity is exactly equality with the
canonical offset vector for the supplied crossing counts. -/
theorem advertisedCutOffsetsAreLeftmostMinimum_iff_eq_canonical
    {T b : Nat} (hb : 0 < b) (crossings : Fin T → Nat)
    (offsets : CanonicalCutOffsets T b) :
    AdvertisedCutOffsetsAreLeftmostMinimum crossings offsets ↔
      offsets =
        (fun bucket : Fin (T / b) ↦
          canonicalBoundaryOffset hb crossings bucket) := by
  constructor
  · intro hvalid
    funext bucket
    exact
      (advertisedCutOffsetIsLeftmostMinimum_iff_eq_canonicalBoundaryOffset
        hb crossings bucket (offsets bucket)).1 (hvalid bucket)
  · intro hoffsets
    subst offsets
    intro bucket
    exact
      (advertisedCutOffsetIsLeftmostMinimum_iff_eq_canonicalBoundaryOffset
        hb crossings bucket
          (canonicalBoundaryOffset hb crossings bucket)).2 rfl

/-- The actual crossing-count profile of the first `T` transitions of the
blank-start run.  Naming it makes explicit that the specialized checker below
consults the real run rather than locally supplied counter certificates. -/
def actualWorkBoundaryCrossingProfile
    (machine : DeterministicMachine) (input : List Bool) (T : Nat) :
    Fin T → Nat :=
  fun boundary ↦
    workBoundaryCrossingCount machine input T boundary.val

/-- Semantic cut-minimality validity for the offsets advertised by an
arbitrary ambient timed alpha, measured against the actual blank-start run. -/
def AdvertisedTimedAlphaCutsAreLeftmostMinimum
    (machine : DeterministicMachine) (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) : Prop :=
  AdvertisedCutOffsetsAreLeftmostMinimum
    (actualWorkBoundaryCrossingProfile machine input T) alpha.offsets

/-- Boolean actual-run cut-minimality checker for an arbitrary ambient timed
alpha.  Its word and terminal fields are intentionally irrelevant here. -/
def advertisedTimedAlphaCutMinimalityCheck
    (machine : DeterministicMachine) (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) : Bool :=
  advertisedCutOffsetsLeftmostMinimumCheck
    (actualWorkBoundaryCrossingProfile machine input T) alpha.offsets

/-- Exact semantic reflection of the actual-run alpha checker. -/
theorem advertisedTimedAlphaCutMinimalityCheck_eq_true_iff
    (machine : DeterministicMachine) (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    advertisedTimedAlphaCutMinimalityCheck machine input alpha = true ↔
      AdvertisedTimedAlphaCutsAreLeftmostMinimum machine input alpha := by
  exact advertisedCutOffsetsLeftmostMinimumCheck_eq_true_iff
    (actualWorkBoundaryCrossingProfile machine input T) alpha.offsets

/-- Main exactness theorem: the actual-run checker accepts precisely the
canonical offset vector extracted from that run. -/
theorem advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    advertisedTimedAlphaCutMinimalityCheck machine input alpha = true ↔
      alpha.offsets = canonicalCutOffsets machine input T b hb := by
  rw [advertisedTimedAlphaCutMinimalityCheck_eq_true_iff]
  simpa [AdvertisedTimedAlphaCutsAreLeftmostMinimum,
    actualWorkBoundaryCrossingProfile, canonicalCutOffsets] using
    (advertisedCutOffsetsAreLeftmostMinimum_iff_eq_canonical hb
      (actualWorkBoundaryCrossingProfile machine input T) alpha.offsets)

/-- Equivalent physical-cut form of exactness.  Thus no alternative offset
vector can pass merely by reconstructing the same cuts. -/
theorem advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_physicalCuts_eq
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    advertisedTimedAlphaCutMinimalityCheck machine input alpha = true ↔
      cutDescriptionOfOffsets alpha.offsets =
        canonicalCutDescription machine input T b hb := by
  constructor
  · intro hcheck
    have hoffsets :=
      (advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
        machine input T b hb alpha).1 hcheck
    rw [hoffsets]
    exact
      (canonicalCutDescription_eq_cutDescriptionOfOffsets
        machine input T b hb).symm
  · intro hcuts
    apply
      (advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
        machine input T b hb alpha).2
    apply cutDescriptionOfOffsets_injective
    exact hcuts.trans
      (canonicalCutDescription_eq_cutDescriptionOfOffsets
        machine input T b hb)

/-- Completeness: the timed alpha extracted from the actual run passes the
cut-minimality checker. -/
theorem advertisedTimedAlphaCutMinimalityCheck_actual_eq_true
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    advertisedTimedAlphaCutMinimalityCheck machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) = true := by
  apply
    (advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
      machine input T b hb
        (chronologicalTimedCanonicalAlpha machine input T b hb)).2
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
