import Magnification.AuditRoutes.ArbitraryLogWidthTT.Family
import Magnification.AuditRoutes.LogWidthAdversary.TTFormulaSizeBound
import Mathlib.Tactic

/-!
# Arbitrary log-width truth-table payload: formula witness packaging

Slot T5 for `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`.

This module packages the arbitrary logarithmic truth-table payload family from
T4 as a strict `InPpolyFormula` witness.  The construction is audit-only
side-track plumbing: it proves that the hardwired truth-table family itself has
polynomial-size formulas, but it does not introduce a lower-bound endpoint,
source theorem, provenance filter, or bridge to any final P-vs-NP target.

The all-essential hypothesis is retained in the public signature even though the
size/correctness fields below do not use it.  T6 needs the same witness together
with support-diversity facts, and those support facts do depend on
`AllEssentialPayload F`.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ArbitraryLogWidthTT

open Pnp3.ComplexityInterfaces
open Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe

/--
The concrete linear polynomial cap used for the arbitrary-payload witness.

The truth-table size theorem gives `size (ttFormula f) ≤ 7 * 2^k`.  At width
`k = Nat.log2 (n + 1)`, the standard floor-log inequality gives
`2^k ≤ n + 1`, so `7 * (n + 1)` is enough after the outer variable rename.
-/
def adversaryPolyBound_v_arbpayload (n : Nat) : Nat :=
  7 * (n + 1)

/-- A quadratic slack inequality used to package the linear cap as polynomial. -/
theorem adversaryPolyBound_v_arbpayload_le_square_add_twentyTwo (n : Nat) :
    adversaryPolyBound_v_arbpayload n ≤ n ^ 2 + 22 := by
  dsimp [adversaryPolyBound_v_arbpayload]
  nlinarith [sq_nonneg ((n : Int) - 4)]

/-- The explicit polynomial-boundedness certificate for the T5 linear cap. -/
theorem adversaryPolyBound_v_arbpayload_poly :
    ∃ c : Nat, ∀ n, adversaryPolyBound_v_arbpayload n ≤ n ^ c + c := by
  refine ⟨22, ?_⟩
  intro n
  have hquad : adversaryPolyBound_v_arbpayload n ≤ n ^ 2 + 22 :=
    adversaryPolyBound_v_arbpayload_le_square_add_twentyTwo n
  have hpow : n ^ 2 ≤ n ^ 22 := by
    cases n with
    | zero => norm_num
    | succ n =>
        exact Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num : 2 ≤ 22)
  exact le_trans hquad (Nat.add_le_add_right hpow 22)

/--
The logarithmic truth-table width has at most `n + 1` rows.

This is the floor-log inequality specialized to the T4 width function.  It is
kept local to the witness file because T5 is the first slot that needs the
exponential size bound rather than only the support-cardinality width.
-/
theorem two_pow_widthFn_le_succ (n : Nat) :
    2 ^ widthFn n ≤ n + 1 := by
  simpa [widthFn, Nat.log2_eq_log_two] using
    (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n))

/-- Size bound for the arbitrary-payload family under the explicit linear cap. -/
theorem adversaryFamily_v_arbpayload_size_le
    (F : PayloadFamily) (n : Nat) :
    FormulaCircuit.size (adversaryFamily_v_arbpayload F n) ≤
      adversaryPolyBound_v_arbpayload n := by
  calc
    FormulaCircuit.size (adversaryFamily_v_arbpayload F n)
        = FormulaCircuit.size (ttFormula (F n)) := by
          unfold adversaryFamily_v_arbpayload
          exact Pnp3.Magnification.AuditRoutes.LogWidthAdversary.rename_size
            (embed (widthFn_le n))
            (ttFormula (F n))
    _ ≤ 7 * 2 ^ widthFn n :=
          Pnp3.Magnification.AuditRoutes.LogWidthAdversary.ttFormula_size_le
            (widthFn n) (F n)
    _ ≤ 7 * (n + 1) := by
          exact Nat.mul_le_mul_left 7 (two_pow_widthFn_le_succ n)
    _ = adversaryPolyBound_v_arbpayload n := rfl

/--
T5 output: package the arbitrary log-width truth-table family as an
`InPpolyFormula` witness.

The `hF` parameter is intentionally not consumed by the record fields: the
formula-size and correctness packaging works for every payload family.  It is
part of the signature so T6 can use the same term in the diversity theorem,
where all-essentiality is needed for support growth.
-/
def adversaryWitness_v_arbpayload
    (F : PayloadFamily)
    (_hF : AllEssentialPayload F) :
    InPpolyFormula (adversaryLanguage_v_arbpayload F) where
  polyBound := adversaryPolyBound_v_arbpayload
  polyBound_poly := adversaryPolyBound_v_arbpayload_poly
  family := adversaryFamily_v_arbpayload F
  family_size_le := adversaryFamily_v_arbpayload_size_le F
  correct := fun _ _ => rfl

end ArbitraryLogWidthTT
end AuditRoutes
end Magnification
end Pnp3
