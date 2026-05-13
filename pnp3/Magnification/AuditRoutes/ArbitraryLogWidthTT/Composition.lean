import Magnification.AuditRoutes.ArbitraryLogWidthTT.Witness
import Magnification.AuditRoutes.LogWidthAdversary.Diversity_Unbounded
import Magnification.AuditRoutes.LogWidthAdversary.Diversity_BelowN
import Magnification.AuditRoutes.FixedParamsProbe

/-!
# Arbitrary log-width truth-table payload: final composition

Slot T6 for `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`.

This module composes the T1--T5 arbitrary-payload construction with the
existing log-width diversity reducers.  The result is the headline
NOGO-000006 witness: every all-essential truth-table payload family on the
`Nat.log2 (n + 1)` window, after canonical embedding into `n` inputs, satisfies
`FP3Attempt.InSupportFunctionalDiversity`.

Progress category: side-track audit formalization.  This closes the
support-cardinality hardwiring obstruction for arbitrary all-essential
log-width `ttFormula` payloads.  It does not design `ProvenanceFilter_v2`, does
not introduce a source theorem, and does not create any lower-bound bridge or
final P-vs-NP endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ArbitraryLogWidthTT

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe
open Pnp3.Magnification.AuditRoutes.LogWidthAdversary

/--
First diversity conjunct for arbitrary all-essential log-width truth-table
payloads.

T4 computes the exact support cardinality of the family as `widthFn n`; the
existing S8 reducer then transfers the unboundedness of `Nat.log2 (n+1)` to the
actual witness support.
-/
theorem arbitraryPayload_support_unbounded
    (F : PayloadFamily)
    (hF : AllEssentialPayload F) :
    ∀ B : Nat, ∃ n : Nat,
      B < (FormulaCircuit.support
        ((adversaryWitness_v_arbpayload F hF).family n)).card := by
  refine adversary_support_unbounded
    (adversaryWitness_v_arbpayload F hF) widthFn ?_ ?_
  · intro n
    have hcard := adversaryFamily_v_arbpayload_support_card F hF n
    show widthFn n ≤ _
    rw [show (adversaryWitness_v_arbpayload F hF).family =
          adversaryFamily_v_arbpayload F from rfl]
    exact Nat.le_of_eq hcard.symm
  · intro B
    rcases logWidth_unbounded B with ⟨n, hB⟩
    refine ⟨n, ?_⟩
    simpa [widthFn] using hB

/--
Second diversity conjunct for arbitrary all-essential log-width truth-table
payloads.

T4 gives the exact same support cardinality identity, and the existing S9
reducer combines it with the infinitely-often inequality
`Nat.log2 (n+1) < n`.
-/
theorem arbitraryPayload_support_below_n_io
    (F : PayloadFamily)
    (hF : AllEssentialPayload F) :
    ∀ N : Nat, ∃ n : Nat,
      N ≤ n ∧
      (FormulaCircuit.support
        ((adversaryWitness_v_arbpayload F hF).family n)).card < n := by
  refine adversary_support_below_n_io
    (adversaryWitness_v_arbpayload F hF) widthFn ?_ ?_
  · intro n
    have hcard := adversaryFamily_v_arbpayload_support_card F hF n
    show _ ≤ widthFn n
    rw [show (adversaryWitness_v_arbpayload F hF).family =
          adversaryFamily_v_arbpayload F from rfl]
    exact Nat.le_of_eq hcard
  · intro N
    rcases logWidth_lt_self N with ⟨n, hNn, hlt⟩
    refine ⟨n, hNn, ?_⟩
    simpa [widthFn] using hlt

/--
**T6 headline theorem / NOGO-000006 formal witness.**

For every payload family `F` whose `n`-th truth-table payload depends on all
`widthFn n = Nat.log2 (n + 1)` coordinates, the packaged polynomial-size
formula witness satisfies `FP3Attempt.InSupportFunctionalDiversity`.

This upgrades the previous prefix-AND-only obstruction to the full arbitrary
all-essential log-width `ttFormula` payload setting.  The theorem is strictly
about the audit-route support-cardinality filter: no `SourceTheorem`, no
`gap_from`, no `ResearchGapWitness`, and no final complexity-separation endpoint
is introduced here.
-/
theorem arbitraryLogWidthTT_satisfies_diversity
    (F : PayloadFamily)
    (hF : AllEssentialPayload F) :
    FP3Attempt.InSupportFunctionalDiversity
      (adversaryWitness_v_arbpayload F hF) :=
  ⟨arbitraryPayload_support_unbounded F hF,
   arbitraryPayload_support_below_n_io F hF⟩

end ArbitraryLogWidthTT
end AuditRoutes
end Magnification
end Pnp3
