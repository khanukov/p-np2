import Magnification.AuditRoutes.SupportCardinalityBarrier.Barrier
import Magnification.AuditRoutes.FixedParamsProbe

/-!
# Support-cardinality barrier: application to `InSupportFunctionalDiversity` (T6)

Slot T6 for `seed_packs/fp3b4_support_cardinality_barrier/`.

This module applies the abstract T5 barrier theorem to the concrete FP-3 audit
filter `FP3Attempt.InSupportFunctionalDiversity`.  The application is local to
filter design: it records that this particular audit predicate is determined
entirely by the support-cardinality profile of an `InPpolyFormula` witness, and
therefore inherits the canonical hardwiring twin obstruction from T5.

No `SourceTheorem`, no `gap_from_*` bridge, no `ResearchGapWitness`, and no final
P-vs-NP endpoint is introduced here.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace SupportCardinalityBarrier

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe

/--
The FP-3 support-diversity filter is support-cardinality-only.

`FP3Attempt.InSupportFunctionalDiversity` has exactly two conjuncts:

* unboundedness of `n ↦ |support (w.family n)|`, and
* infinitely-often strict non-saturation of the same cardinality function.

Thus witnesses with the same support-cardinality profile satisfy the predicate
simultaneously, even when their languages, formula shapes, polynomial bounds, or
semantics differ.
-/
theorem inSupportFunctionalDiversity_is_support_cardinality_only :
    IsSupportCardinalityOnly @FP3Attempt.InSupportFunctionalDiversity := by
  intro L₁ L₂ w₁ w₂ hProfile
  constructor
  · intro hDiversity
    constructor
    · intro B
      obtain ⟨n, hn⟩ := hDiversity.1 B
      refine ⟨n, ?_⟩
      have hCard :
          (FormulaCircuit.support (w₁.family n)).card =
            (FormulaCircuit.support (w₂.family n)).card := by
        simpa [supportCardinalityProfile] using congrFun hProfile n
      simpa [hCard] using hn
    · intro N
      obtain ⟨n, hNle, hStrict⟩ := hDiversity.2 N
      refine ⟨n, hNle, ?_⟩
      have hCard :
          (FormulaCircuit.support (w₁.family n)).card =
            (FormulaCircuit.support (w₂.family n)).card := by
        simpa [supportCardinalityProfile] using congrFun hProfile n
      simpa [hCard] using hStrict
  · intro hDiversity
    constructor
    · intro B
      obtain ⟨n, hn⟩ := hDiversity.1 B
      refine ⟨n, ?_⟩
      have hCard :
          (FormulaCircuit.support (w₁.family n)).card =
            (FormulaCircuit.support (w₂.family n)).card := by
        simpa [supportCardinalityProfile] using congrFun hProfile n
      simpa [hCard] using hn
    · intro N
      obtain ⟨n, hNle, hStrict⟩ := hDiversity.2 N
      refine ⟨n, hNle, ?_⟩
      have hCard :
          (FormulaCircuit.support (w₁.family n)).card =
            (FormulaCircuit.support (w₂.family n)).card := by
        simpa [supportCardinalityProfile] using congrFun hProfile n
      simpa [hCard] using hStrict

/--
Any honest sublinear-support witness satisfying `InSupportFunctionalDiversity`
has a canonical hardwiring twin satisfying the same predicate.

This is the concrete NOGO-000007 witness: the FP-3 support-functional-diversity
filter cannot serve as a hardwiring-excluding provenance filter, because T5
transports it to the canonical hardwiring witness with the identical
support-cardinality profile.
-/
theorem any_honest_sublinear_support_witness_has_hardwiring_twin
    {L : Language}
    (w_honest : InPpolyFormula L)
    (hHonest : FP3Attempt.InSupportFunctionalDiversity w_honest)
    (hSubLinear :
      ∀ n, (FormulaCircuit.support (w_honest.family n)).card ≤ n) :
    FP3Attempt.InSupportFunctionalDiversity
      (canonicalHardwiringWitness
        (fun n => (FormulaCircuit.support (w_honest.family n)).card)
        hSubLinear) := by
  exact
    support_cardinality_barrier
      @FP3Attempt.InSupportFunctionalDiversity
      inSupportFunctionalDiversity_is_support_cardinality_only
      w_honest
      hHonest
      hSubLinear

end SupportCardinalityBarrier
end AuditRoutes
end Magnification
end Pnp3
