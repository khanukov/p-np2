import Pnp4.Frontier.OneTapeMagnification.CanonicalCrossingRecords

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Canonical cut offsets

Every canonical cut selected from a full bucket is determined by an offset in
`Fin b`.  This file keeps that coordinate instead of paying for an arbitrary
element of `Fin T` at every bucket.  The resulting ambient cut carrier has
exact size `b^(T / b)`, and pairing it with the existing fixed-length crossing
payload word gives the corresponding refined ambient alpha count.

These are ambient carrier counts only.  They do not count reachable cuts,
locally valid crossing records, or complete machine transcripts.
-/

/-- One offset in `Fin b` for every full bucket. -/
abbrev CanonicalCutOffsets (T b : Nat) := Fin (T / b) → Fin b

/-- Reconstruct the physical full-bucket cuts from their offsets. -/
def cutDescriptionOfOffsets {T b : Nat}
    (offsets : CanonicalCutOffsets T b) : CanonicalCutDescription T b :=
  fun i => fullBucketBoundary i (offsets i)

@[simp]
theorem cutDescriptionOfOffsets_apply {T b : Nat}
    (offsets : CanonicalCutOffsets T b) (i : Fin (T / b)) :
    cutDescriptionOfOffsets offsets i = fullBucketBoundary i (offsets i) :=
  rfl

/-- The full physical cut description determines its offset vector uniquely
when it is reconstructed bucket by bucket. -/
theorem cutDescriptionOfOffsets_injective {T b : Nat} :
    Function.Injective (cutDescriptionOfOffsets (T := T) (b := b)) := by
  intro offsets offsets' hCuts
  funext i
  have hBoundary :
      fullBucketBoundary i (offsets i) =
        fullBucketBoundary i (offsets' i) := by
    exact congrFun hCuts i
  have hPair : (i, offsets i) = (i, offsets' i) :=
    fullBucketBoundary_injective (T := T) (b := b) hBoundary
  exact congrArg Prod.snd hPair

/-- A canonical minimum cut has one and only one offset in its advertised
full bucket. -/
theorem canonicalBoundary_existsUnique_offset {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) (i : Fin (T / b)) :
    ∃! offset : Fin b,
      canonicalBoundary hb crossings i = fullBucketBoundary i offset := by
  refine ⟨canonicalBoundaryOffset hb crossings i, rfl, ?_⟩
  intro offset hOffset
  have hPair :
      (i, canonicalBoundaryOffset hb crossings i) = (i, offset) :=
    fullBucketBoundary_injective (T := T) (b := b) hOffset
  exact (congrArg Prod.snd hPair).symm

/-- Extract the canonical offset vector selected by one concrete blank-start
run. -/
noncomputable def canonicalCutOffsets
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : CanonicalCutOffsets T b :=
  fun i =>
    canonicalBoundaryOffset hb
      (fun j : Fin T => workBoundaryCrossingCount machine input T j.val) i

/-- Reconstructing the cut at bucket `i` from its extracted offset gives
exactly the physical cut stored by `canonicalCutDescription`. -/
@[simp]
theorem canonicalCutDescription_apply_eq_fullBucketBoundary
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (i : Fin (T / b)) :
    canonicalCutDescription machine input T b hb i =
      fullBucketBoundary i
        (canonicalCutOffsets machine input T b hb i) :=
  rfl

/-- The whole concrete physical cut vector is reconstructed from the
extracted offset vector. -/
theorem canonicalCutDescription_eq_cutDescriptionOfOffsets
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    canonicalCutDescription machine input T b hb =
      cutDescriptionOfOffsets (canonicalCutOffsets machine input T b hb) := by
  funext i
  exact canonicalCutDescription_apply_eq_fullBucketBoundary
    machine input T b hb i

/-- Each concrete canonical cut has a unique offset in its selected full
bucket. -/
theorem canonicalCutDescription_existsUnique_offset
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (i : Fin (T / b)) :
    ∃! offset : Fin b,
      canonicalCutDescription machine input T b hb i =
        fullBucketBoundary i offset := by
  refine ⟨canonicalCutOffsets machine input T b hb i,
    canonicalCutDescription_apply_eq_fullBucketBoundary
      machine input T b hb i, ?_⟩
  intro offset hOffset
  have hBoundary :
      fullBucketBoundary i (canonicalCutOffsets machine input T b hb i) =
        fullBucketBoundary i offset :=
    (canonicalCutDescription_apply_eq_fullBucketBoundary
      machine input T b hb i).symm.trans hOffset
  have hPair :
      (i, canonicalCutOffsets machine input T b hb i) = (i, offset) :=
    fullBucketBoundary_injective (T := T) (b := b) hBoundary
  exact (congrArg Prod.snd hPair).symm

/-- Exact size of the offset-vector carrier.  This is the full function
space, not a reachability count for canonical cuts of actual runs. -/
theorem card_canonicalCutOffsets (T b : Nat) :
    Fintype.card (CanonicalCutOffsets T b) = b ^ (T / b) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- A refined ambient alpha carrier: one bucket offset and one crossing
payload slot for each full bucket. -/
structure AmbientCanonicalOffsetAlpha (State : Type) (T b : Nat) where
  offsets : CanonicalCutOffsets T b
  payloads : AmbientCrossingPayloadVector State T b
deriving Fintype

/-- Forget the offset representation by reconstructing its physical cuts.
This maps the refined carrier into the earlier, coarser ambient carrier. -/
def ambientCanonicalOffsetAlphaToCanonicalAlpha
    {State : Type} {T b : Nat}
    (alpha : AmbientCanonicalOffsetAlpha State T b) :
    AmbientCanonicalAlpha State T b :=
  { cuts := cutDescriptionOfOffsets alpha.offsets
    payloads := alpha.payloads }

/-- The refined carrier is exactly the product of the offset-vector carrier
and the existing fixed crossing-payload word. -/
def ambientCanonicalOffsetAlphaEquiv (State : Type) (T b : Nat) :
    AmbientCanonicalOffsetAlpha State T b ≃
      CanonicalCutOffsets T b × AmbientCrossingPayloadVector State T b where
  toFun alpha := (alpha.offsets, alpha.payloads)
  invFun fields := { offsets := fields.1, payloads := fields.2 }
  left_inv alpha := by cases alpha; rfl
  right_inv fields := by rcases fields with ⟨offsets, payloads⟩; rfl

/-- Exact refined ambient alpha count
`b^(T / b) * (2 * |State| * (T + 1))^(T / b)`.

No claim is made that every such pair is reachable, locally valid, or a
complete transcript. -/
theorem card_ambientCanonicalOffsetAlpha
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (AmbientCanonicalOffsetAlpha State T b) =
      b ^ (T / b) *
        (2 * Fintype.card State * (T + 1)) ^ (T / b) := by
  rw [Fintype.card_congr (ambientCanonicalOffsetAlphaEquiv State T b),
    Fintype.card_prod, card_canonicalCutOffsets,
    card_ambientCrossingPayloadVector]

end OneTapeMagnification
end Frontier
end Pnp4
