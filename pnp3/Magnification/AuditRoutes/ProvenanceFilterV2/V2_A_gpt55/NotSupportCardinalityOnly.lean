import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NonVacuity
import Magnification.AuditRoutes.SupportCardinalityBarrier.SupportCardinalityOnly
import Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringWitness

/-!
# V2-A Phase 2: not support-cardinality-only

Progress classification: side-track audit formalization.  This file proves that
V2-A Phase 2 is not merely a support-cardinality-profile predicate: two strict
formula witnesses can have the same support-cardinality at every length while
V2-A accepts one and rejects the other because it also inspects gate labels.

The separating pair is intentionally concrete.

* `seededPrefixAndWitness` is accepted by `seededPrefixAndWitness_admitted`.
* The canonical full-prefix hardwiring witness with profile `n ↦ n` is rejected:
  at length `2`, its formula has support size `2` but contains no OR gate, so it
  violates the V2-A mixed OR/NOT requirement.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces
open FormulaShape

/-- The full-support canonical hardwiring witness used as the bad twin. -/
abbrev fullPrefixCanonicalWitness : InPpolyFormula
    (Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringLanguage
      (fun n => n) (fun n => Nat.le_refl n)) :=
  Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringWitness
    (fun n => n) (fun n => Nat.le_refl n)

/--
The full-prefix canonical hardwiring witness is rejected by V2-A Phase 2.

At length `2`, the canonical witness has active support cardinality exactly `2`,
so V2-A demands both a positive OR-gate count and a positive NOT-gate count.  But
its displayed syntax is the raw `prefixAnd 2 2`, and `prefixAnd` has no OR gates.
-/
theorem excludes_fullPrefixAnd_canonicalWitness :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter fullPrefixCanonicalWitness := by
  intro hFilter
  obtain ⟨_hUnbounded, _hGate, _hDepth, hMix⟩ := hFilter
  have hSupport : 2 ≤ (FormulaCircuit.support (fullPrefixCanonicalWitness.family 2)).card := by
    rw [fullPrefixCanonicalWitness,
      Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringWitness]
    rw [Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringFamily_support_card]
  have hOrPos : 0 < orGateCount (fullPrefixCanonicalWitness.family 2) :=
    (hMix 2 hSupport).1
  have hOrZero : orGateCount (fullPrefixCanonicalWitness.family 2) = 0 := by
    simp [fullPrefixCanonicalWitness,
      Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringWitness,
      Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringFamily,
      orGateCount_prefixAnd]
  rw [hOrZero] at hOrPos
  exact Nat.lt_irrefl 0 hOrPos

/--
V2-A Phase 2 is not support-cardinality-only.

The accepted seeded-prefix witness and the rejected full-prefix canonical
hardwiring witness have the same support-cardinality profile (`n ↦ n`).  If the
filter were support-cardinality-only, acceptance would transport from the seeded
witness to the canonical witness, contradicting `excludes_fullPrefixAnd_canonicalWitness`.
-/
theorem ProvenanceFilter_v2_V2_A_gpt55_not_support_cardinality_only :
    ¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
          @ProvenanceFilter_v2_V2_A_gpt55_Filter := by
  intro hSupportOnly
  have hSameProfile : ∀ n,
      (FormulaCircuit.support (seededPrefixAndWitness.family n)).card =
        (FormulaCircuit.support (fullPrefixCanonicalWitness.family n)).card := by
    intro n
    rw [seededPrefixAndWitness, seededPrefixAndFamily_support_card]
    rw [fullPrefixCanonicalWitness,
      Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringWitness]
    rw [Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.canonicalHardwiringFamily_support_card]
  have hTransport :=
    Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly.apply
        hSupportOnly
        seededPrefixAndWitness
        fullPrefixCanonicalWitness
        hSameProfile
  exact excludes_fullPrefixAnd_canonicalWitness
    (hTransport.mp seededPrefixAndWitness_admitted)

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
