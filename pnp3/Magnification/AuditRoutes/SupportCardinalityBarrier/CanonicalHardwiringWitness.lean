import Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringSupport
import Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2

/-!
# Support-cardinality barrier: canonical hardwiring witness (T3)

Slot T3 for `seed_packs/fp3b4_support_cardinality_barrier/`.

This module packages the T1 canonical hardwiring family as a strict
`InPpolyFormula` witness for the T1 language.  It deliberately stops before the
later barrier-predicate and headline-barrier slots: no support-cardinality-only
predicate, no meta-barrier theorem, and no bridge to any final P-vs-NP endpoint
is introduced here.

Progress category: side-track audit infrastructure.  The size proof reuses the
exact `prefixAnd_size` theorem from the log-width adversary family and the same
linear polynomial cap `2 * n + 1` used by that route.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace SupportCardinalityBarrier

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary
  (prefixAnd_size two_mul_succ_le_pow_two_plus_two)

/-- The linear polynomial cap used for the canonical hardwiring witness. -/
def canonicalHardwiringPolyBound (n : Nat) : Nat :=
  2 * n + 1

/-- Polynomial-boundedness certificate for `canonicalHardwiringPolyBound`. -/
theorem canonicalHardwiringPolyBound_poly :
    ∃ c : Nat, ∀ n, canonicalHardwiringPolyBound n ≤ n ^ c + c := by
  refine ⟨2, ?_⟩
  intro n
  exact two_mul_succ_le_pow_two_plus_two n

/--
Size bound for the canonical hardwiring family under the linear cap.

The T1 family at length `n` is `prefixAnd n (s n) (hs n)`, whose exact size is
`2 * s n + 1`.  Since `hs n` says `s n ≤ n`, this is bounded by `2 * n + 1`.
-/
theorem canonicalHardwiringFamily_size_le
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) (n : Nat) :
    FormulaCircuit.size (canonicalHardwiringFamily s hs n) ≤
      canonicalHardwiringPolyBound n := by
  calc
    FormulaCircuit.size (canonicalHardwiringFamily s hs n)
        = 2 * s n + 1 := by
          unfold canonicalHardwiringFamily
          exact prefixAnd_size n (s n) (hs n)
    _ ≤ 2 * n + 1 := by
          have hsn : s n ≤ n := hs n
          omega
    _ = canonicalHardwiringPolyBound n := rfl

/--
T3 output: package the canonical hardwiring family as an `InPpolyFormula` witness.

The language is definitionally evaluation of `canonicalHardwiringFamily`, so the
semantic `correct` field is judgmental (`rfl`).
-/
def canonicalHardwiringWitness
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) :
    InPpolyFormula (canonicalHardwiringLanguage s hs) where
  polyBound := canonicalHardwiringPolyBound
  polyBound_poly := canonicalHardwiringPolyBound_poly
  family := canonicalHardwiringFamily s hs
  family_size_le := canonicalHardwiringFamily_size_le s hs
  correct := fun _ _ => rfl

end SupportCardinalityBarrier
end AuditRoutes
end Magnification
end Pnp3
