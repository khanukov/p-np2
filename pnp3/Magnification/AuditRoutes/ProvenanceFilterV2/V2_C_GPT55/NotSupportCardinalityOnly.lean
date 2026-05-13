import Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Sketch
import Magnification.AuditRoutes.SupportCardinalityBarrier.SupportCardinalityOnly
import Magnification.AuditRoutes.LogWidthAdversary.RenameSize
import Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2

/-!
# V2-C / GPT55 is not support-cardinality-only

Progress classification: side-track audit formalization.  This module checks a
local design claim about the V2-C provenance filter: the predicate inspects
cross-length Boolean behaviour, not merely the cardinalities of syntactic
supports.  It does **not** promote V2-C to a survivor, introduce a source
obligation, or connect the route to `PpolyDAG`.

The separating pair is deliberately elementary.

* `orAllWitness` computes the OR of all input bits.  Appending a final `false`
  bit preserves OR, and the recursive formula grows by two nodes per length.
* `andAllWitness` computes the AND of all input bits.  It has the same support
  at every length, but it fails the zero-extension law already at `0 → 1`:
  `AND₁(false) = false` while `AND₀ = true`.

Thus any invariant that only sees the support-cardinality profile would have to
assign the same truth value to both witnesses, contradicting V2-C.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_C_GPT55

open Pnp3.ComplexityInterfaces

/-- Embed the old `n` input coordinates as the first `n` coordinates at length `n+1`. -/
def firstEmbedding (n : Nat) : Fin n → Fin (n + 1) :=
  fun i => ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩

/-- The fresh last coordinate in a successor length. -/
def lastInput (n : Nat) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

/-- Right-growing OR over all coordinates.  The empty OR is `false`. -/
def orAllFamily : ∀ n : Nat, FormulaCircuit n
  | 0 => FormulaCircuit.const false
  | n + 1 =>
      FormulaCircuit.or
        (FormulaCircuit.rename (firstEmbedding n) (orAllFamily n))
        (FormulaCircuit.input (lastInput n))

/-- Right-growing AND over all coordinates.  The empty AND is `true`. -/
def andAllFamily : ∀ n : Nat, FormulaCircuit n
  | 0 => FormulaCircuit.const true
  | n + 1 =>
      FormulaCircuit.and
        (FormulaCircuit.rename (firstEmbedding n) (andAllFamily n))
        (FormulaCircuit.input (lastInput n))

/-- Renaming only rewires input leaves, so evaluation transports along the map. -/
theorem eval_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) (x : Bitstring n) :
    FormulaCircuit.eval (FormulaCircuit.rename σ c) x =
      FormulaCircuit.eval c (fun i => x (σ i)) := by
  induction c with
  | const b =>
      simp [FormulaCircuit.rename, FormulaCircuit.eval]
  | input i =>
      simp [FormulaCircuit.rename, FormulaCircuit.eval]
  | not c ih =>
      simp [FormulaCircuit.rename, FormulaCircuit.eval, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.eval, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.eval, ih₁, ih₂]

/-- Renaming transports syntactic support by `Finset.image`. -/
theorem support_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    FormulaCircuit.support (FormulaCircuit.rename σ c) =
      (FormulaCircuit.support c).image σ := by
  induction c with
  | const b =>
      simp [FormulaCircuit.rename, FormulaCircuit.support]
  | input i =>
      simp [FormulaCircuit.rename, FormulaCircuit.support]
  | not c ih =>
      simp [FormulaCircuit.rename, FormulaCircuit.support, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.support, ih₁, ih₂, Finset.image_union]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.support, ih₁, ih₂, Finset.image_union]

/-- OR and AND mention exactly the same coordinates at every length. -/
theorem orAll_support_eq_andAll_support (n : Nat) :
    FormulaCircuit.support (orAllFamily n) =
      FormulaCircuit.support (andAllFamily n) := by
  induction n with
  | zero =>
      simp [orAllFamily, andAllFamily, FormulaCircuit.support]
  | succ n ih =>
      simp [orAllFamily, andAllFamily, FormulaCircuit.support, support_rename, ih]

/-- Exact size of the all-OR family. -/
theorem orAll_size (n : Nat) :
    FormulaCircuit.size (orAllFamily n) = 2 * n + 1 := by
  induction n with
  | zero =>
      simp [orAllFamily, FormulaCircuit.size]
  | succ n ih =>
      simp [orAllFamily, FormulaCircuit.size,
        Pnp3.Magnification.AuditRoutes.LogWidthAdversary.rename_size, ih]
      omega

/-- Exact size of the all-AND family. -/
theorem andAll_size (n : Nat) :
    FormulaCircuit.size (andAllFamily n) = 2 * n + 1 := by
  induction n with
  | zero =>
      simp [andAllFamily, FormulaCircuit.size]
  | succ n ih =>
      simp [andAllFamily, FormulaCircuit.size,
        Pnp3.Magnification.AuditRoutes.LogWidthAdversary.rename_size, ih]
      omega

/-- The shared linear polynomial bound used by the two strict witnesses. -/
def allInputsPolyBound (n : Nat) : Nat := 2 * n + 1

/-- The shared linear bound is polynomial. -/
theorem allInputsPolyBound_poly :
    ∃ c : Nat, ∀ n, allInputsPolyBound n ≤ n ^ c + c := by
  refine ⟨2, ?_⟩
  intro n
  unfold allInputsPolyBound
  exact FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.two_mul_succ_le_pow_two_plus_two n

/-- Language decided by the all-OR family. -/
def orAllLanguage : Language :=
  fun n x => FormulaCircuit.eval (orAllFamily n) x

/-- Strict `InPpolyFormula` witness for the all-OR family. -/
def orAllWitness : InPpolyFormula orAllLanguage where
  polyBound := allInputsPolyBound
  polyBound_poly := allInputsPolyBound_poly
  family := orAllFamily
  family_size_le := by
    intro n
    rw [orAll_size]
    rfl
  correct := fun _ _ => rfl

/-- Language decided by the all-AND family. -/
def andAllLanguage : Language :=
  fun n x => FormulaCircuit.eval (andAllFamily n) x

/-- Strict `InPpolyFormula` witness for the all-AND family. -/
def andAllWitness : InPpolyFormula andAllLanguage where
  polyBound := allInputsPolyBound
  polyBound_poly := allInputsPolyBound_poly
  family := andAllFamily
  family_size_le := by
    intro n
    rw [andAll_size]
    rfl
  correct := fun _ _ => rfl

/-- The all-OR witness satisfies V2-C with edit budget `2`. -/
theorem orAll_satisfies_v2_C :
    ProvenanceFilter_v2_V2_C_GPT55 orAllWitness := by
  refine ⟨2, ?_, ?_⟩
  · intro n
    simp [orAllWitness, orAll_size]
    omega
  · intro n x
    simp [orAllWitness, orAllFamily, FormulaCircuit.eval, eval_rename,
      firstEmbedding, lastInput]

/-- The empty bitstring used for the `0 → 1` AND counterexample. -/
def emptyBits_for_allInputs : Bitstring 0 := fun i => Fin.elim0 i

/-- The all-AND witness fails V2-C already on zero-extension from length `0` to `1`. -/
theorem andAll_zeroExtension_counterexample :
    FormulaCircuit.eval (andAllWitness.family 1)
      (fun i : Fin 1 =>
        if h : i.val < 0 then emptyBits_for_allInputs ⟨i.val, h⟩ else false) ≠
    FormulaCircuit.eval (andAllWitness.family 0) emptyBits_for_allInputs := by
  simp [andAllWitness, andAllFamily, FormulaCircuit.eval]

/-- V2-C rejects the all-AND witness. -/
theorem andAll_fails_v2_C :
    ¬ ProvenanceFilter_v2_V2_C_GPT55 andAllWitness := by
  exact v2_C_GPT55_rejects_of_zeroExtension_counterexample
    andAllWitness 0 emptyBits_for_allInputs andAll_zeroExtension_counterexample

/-- The OR and AND witnesses have the same support-cardinality profile. -/
theorem orAll_andAll_same_support_cardinality_profile :
    SupportCardinalityBarrier.supportCardinalityProfile orAllWitness =
      SupportCardinalityBarrier.supportCardinalityProfile andAllWitness := by
  funext n
  unfold SupportCardinalityBarrier.supportCardinalityProfile
  exact congrArg Finset.card (orAll_support_eq_andAll_support n)

/--
V2-C is not support-cardinality-only.

The two witnesses above have identical support-cardinality profiles, but V2-C
accepts the OR family and rejects the AND family.  Therefore V2-C necessarily
uses more information than the cardinality of `FormulaCircuit.support`.
-/
theorem ProvenanceFilter_v2_V2_C_GPT55_not_support_cardinality_only :
    ¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
        @ProvenanceFilter_v2_V2_C_GPT55 := by
  intro hSupportOnly
  have hIff := hSupportOnly orAllWitness andAllWitness
    orAll_andAll_same_support_cardinality_profile
  exact andAll_fails_v2_C (hIff.mp orAll_satisfies_v2_C)

end V2_C_GPT55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
