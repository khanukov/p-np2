import Magnification.FinalResultMainline
import Models.Model_PartialMCSP

/-!
# Canonical asymptotic formula-track data

This module fixes the **canonical** asymptotic spec/parameter family used in
the final magnification routes.  Its purpose is to move the
`(hAsym, hNPbridge)` pair — currently passed as hypothesis parameters to many
mainline endpoints — into a concrete in-repo construction.

The canonical track uses the smallest gap allowed by the asymptotic spec
interface:

* `sYES n := 1` (smallest value compatible with `sYES_pos`),
* `sNO n := 2` (smallest value compatible with `gap_ok`).

### Status

* `canonicalAsymptoticSpec`, `canonicalAsymptoticParams`,
  `canonicalShannonBound`, `canonicalAsymptoticParams_*` — fully proved
  unconditionally.
* `canonicalAsymptoticHAsym` — built from a `canonicalSliceEq` proof.
* `canonicalAsymptoticNPBridge_of_TM`, `canonicalAsymptoticData_of_TM`,
  `canonicalAntiCheckerAssumptions_of_TM` — build the strict NP package
  (`AsymptoticNPPullback`, `AsymptoticFormulaTrackData`,
  `AntiCheckerAssumptions`) from a concrete
  `Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

The TM-verifier witness is the **mathematical gap** for unconditionally
closing the canonical NP pullback (published OPS19/CJW20 fact "GapMCSP ∈ NP").
The slice-equality `canonicalSliceEq` is a **technical Lean unfolding** of the
noncomputable `gapPartialMCSP_AsymptoticLanguage` at canonical length; we
provide it as a function parameter to keep this module's infrastructure
unblocked while leaving the technical proof as a separate deliverable.
-/

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/-! ## Canonical asymptotic spec -/

/-- Canonical asymptotic spec: `sYES n = 1`, `sNO n = 2`. -/
def canonicalAsymptoticSpec : GapPartialMCSPAsymptoticSpec where
  sYES := fun _ => 1
  sNO := fun _ => 2
  gap_ok := fun _ => by decide
  sYES_pos := fun _ => by decide

@[simp] lemma canonicalAsymptoticSpec_sYES (n : Nat) :
    canonicalAsymptoticSpec.sYES n = 1 := rfl

@[simp] lemma canonicalAsymptoticSpec_sNO (n : Nat) :
    canonicalAsymptoticSpec.sNO n = 2 := rfl

/-! ## Shannon counting for `sNO = 2` -/

/-- For `n ≥ 1`, `2^n / 2 = 2^(n - 1)`. -/
private lemma two_pow_div_two (n : Nat) (hn : 1 ≤ n) :
    2 ^ n / 2 = 2 ^ (n - 1) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [← hsub]
    exact Nat.pow_succ 2 (n - 1)
  rw [hpow]
  exact Nat.mul_div_cancel _ (by decide : 0 < 2)

/-- For `n ≥ 4`, `n + 2 ≤ 2^(n - 1)`. -/
private lemma succ_succ_le_pow_pred : ∀ n : Nat, 4 ≤ n → n + 2 ≤ 2 ^ (n - 1)
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | (n + 8), _ => by
    have ih : (n + 7) + 2 ≤ 2 ^ ((n + 7) - 1) :=
      succ_succ_le_pow_pred (n + 7) (by omega)
    have hk1 : (n + 7) - 1 = n + 6 := by omega
    have hk2 : (n + 8) - 1 = n + 7 := by omega
    have ih' : n + 9 ≤ 2 ^ (n + 6) := by rw [← hk1]; exact ih
    have hpow : 2 ^ (n + 7) = 2 ^ (n + 6) * 2 := Nat.pow_succ 2 (n + 6)
    show (n + 8) + 2 ≤ 2 ^ ((n + 8) - 1)
    rw [hk2, hpow]
    have hpos : 1 ≤ 2 ^ (n + 6) := Nat.one_le_pow _ _ (by decide)
    omega
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | 2, h => absurd h (by decide)
  | 3, h => absurd h (by decide)

/-- The Shannon-counting bound for `sNO = 2` and `n ≥ 8`. -/
lemma canonicalShannonBound (n : Nat) (hn : 8 ≤ n) :
    circuitCountBound n 1 < 2 ^ (Partial.tableLen n / 2) := by
  have hCount : circuitCountBound n 1 = n + 2 := by
    show 2 * (circuitCountBound n 0) ^ 2 + 2 * (circuitCountBound n 0) + n + 2 = n + 2
    simp [circuitCountBound]
  have htableLen : Partial.tableLen n = 2 ^ n := rfl
  have hn_ge1 : 1 ≤ n := by omega
  have hn_ge4 : 4 ≤ n := by omega
  have hdiv : Partial.tableLen n / 2 = 2 ^ (n - 1) := by
    rw [htableLen, two_pow_div_two n hn_ge1]
  have hlin : n + 2 ≤ 2 ^ (n - 1) := succ_succ_le_pow_pred n hn_ge4
  have hexp_strict : 2 ^ (n - 1) < 2 ^ (2 ^ (n - 1)) := by
    have hself : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : Nat))).2 hself
  rw [hCount, hdiv]
  exact lt_of_le_of_lt hlin hexp_strict

/-! ## Canonical per-slice parameters -/

/-- Canonical per-slice parameters at slice index `n ≥ 8`. -/
def canonicalAsymptoticParams (n : Nat) (hn : 8 ≤ n) : GapPartialMCSPParams where
  n := n
  sYES := 1
  sNO := 2
  gap_ok := by decide
  n_large := hn
  sYES_pos := by decide
  circuit_bound_ok := by
    have h := canonicalShannonBound n hn
    show circuitCountBound n (2 - 1) < 2 ^ (Partial.tableLen n / 2)
    simpa using h

@[simp] lemma canonicalAsymptoticParams_n (n : Nat) (hn : 8 ≤ n) :
    (canonicalAsymptoticParams n hn).n = n := rfl

@[simp] lemma canonicalAsymptoticParams_sYES (n : Nat) (hn : 8 ≤ n) :
    (canonicalAsymptoticParams n hn).sYES = 1 := rfl

@[simp] lemma canonicalAsymptoticParams_sNO (n : Nat) (hn : 8 ≤ n) :
    (canonicalAsymptoticParams n hn).sNO = 2 := rfl

@[simp] lemma canonicalAsymptoticParams_partialInputLen (n : Nat) (hn : 8 ≤ n) :
    Models.partialInputLen (canonicalAsymptoticParams n hn) = Partial.inputLen n := rfl

/-! ## Canonical-slice equality (proved unconditionally)

Closed using the helper
`Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen` from
`Model_PartialMCSP.lean`, which bridges the `Classical.choose` cast via
`Eq.rec` with a universally-quantified motive.
-/

/-- Slice equality at canonical length for the canonical spec/params pair. -/
theorem canonicalSliceEq (n : Nat) (hn : 8 ≤ n)
    (x : Core.BitVec (Models.partialInputLen (canonicalAsymptoticParams n hn))) :
    gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
        (Models.partialInputLen (canonicalAsymptoticParams n hn)) x =
      gapPartialMCSP_Language (canonicalAsymptoticParams n hn)
        (Models.partialInputLen (canonicalAsymptoticParams n hn)) x := by
  classical
  -- Both Bools equal `decide (PartialMCSP_YES_at n 1 (decodePartial x))`.
  by_cases hYes : PartialMCSP_YES (canonicalAsymptoticParams n hn) (decodePartial x)
  · have hRHS_true :
        gapPartialMCSP_Language (canonicalAsymptoticParams n hn)
            (Models.partialInputLen (canonicalAsymptoticParams n hn)) x = true :=
      (Models.gapPartialMCSP_language_true_iff_yes
        (canonicalAsymptoticParams n hn) x).2 hYes
    have hYesAt : PartialMCSP_YES_at n 1 (decodePartial (n := n) x) := by
      rcases hYes with ⟨C, hSize, hCons⟩
      exact ⟨C, by simpa using hSize, hCons⟩
    have hLHS_true :
        gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
            (Models.partialInputLen (canonicalAsymptoticParams n hn)) x = true := by
      have : gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
          (Partial.inputLen n) x = true :=
        (Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen
          canonicalAsymptoticSpec n x).2 (by simpa using hYesAt)
      exact this
    rw [hLHS_true, hRHS_true]
  · have hRHS_not_true :
        gapPartialMCSP_Language (canonicalAsymptoticParams n hn)
            (Models.partialInputLen (canonicalAsymptoticParams n hn)) x ≠ true := by
      intro hT
      exact hYes ((Models.gapPartialMCSP_language_true_iff_yes
        (canonicalAsymptoticParams n hn) x).1 hT)
    have hRHS_false :
        gapPartialMCSP_Language (canonicalAsymptoticParams n hn)
            (Models.partialInputLen (canonicalAsymptoticParams n hn)) x = false := by
      cases hV : gapPartialMCSP_Language (canonicalAsymptoticParams n hn)
          (Models.partialInputLen (canonicalAsymptoticParams n hn)) x
      · rfl
      · exact (hRHS_not_true hV).elim
    have hYesAt_not : ¬ PartialMCSP_YES_at n 1 (decodePartial (n := n) x) := by
      intro hAt
      apply hYes
      rcases hAt with ⟨C, hSize, hCons⟩
      exact ⟨C, by simpa using hSize, hCons⟩
    have hLHS_not_true :
        gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
            (Models.partialInputLen (canonicalAsymptoticParams n hn)) x ≠ true := by
      intro hT
      have hAt : PartialMCSP_YES_at n (canonicalAsymptoticSpec.sYES n) (decodePartial x) :=
        (Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen
          canonicalAsymptoticSpec n x).1 hT
      exact hYesAt_not (by simpa using hAt)
    have hLHS_false :
        gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
            (Models.partialInputLen (canonicalAsymptoticParams n hn)) x = false := by
      cases hV : gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
          (Models.partialInputLen (canonicalAsymptoticParams n hn)) x
      · rfl
      · exact (hLHS_not_true hV).elim
    rw [hLHS_false, hRHS_false]

/-! ## Canonical `AsymptoticFormulaTrackHypothesis` -/

/-- Canonical asymptotic hypothesis, with threshold `N0 := 8`. **Unconditional**. -/
def canonicalAsymptoticHAsym : AsymptoticFormulaTrackHypothesis where
  spec := canonicalAsymptoticSpec
  N0 := 8
  pAt := canonicalAsymptoticParams
  pAt_n := fun _ _ => rfl
  sliceEq := canonicalSliceEq

@[simp] lemma canonicalAsymptoticHAsym_spec :
    canonicalAsymptoticHAsym.spec = canonicalAsymptoticSpec := rfl

@[simp] lemma canonicalAsymptoticHAsym_N0 :
    canonicalAsymptoticHAsym.N0 = 8 := rfl

/-! ## Conditional NP-bridge from a concrete TM witness

The bridge is unconditional **once** a TM witness for `canonicalAsymptoticSpec`
is provided.  Such a witness is a `Models.GapPartialMCSP_Asymptotic_TMWitness
canonicalAsymptoticSpec` — i.e., a concrete verifier TM with polynomial
runtime that accepts on `concat x w` iff the asymptotic language is true at
`x`.

The TM-verifier witness is the **mathematical gap** for closing the canonical
NP pullback unconditionally.  Building it constructively requires composing
toolkit primitives in `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/`.
-/

/-- NP-bridge for the canonical asymptotic spec from a concrete TM witness. -/
def canonicalAsymptoticNPBridge_of_TM
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AsymptoticNPPullback canonicalAsymptoticHAsym where
  strictAsymptotic :=
    Models.gapPartialMCSP_Asymptotic_in_NP_of_TM canonicalAsymptoticSpec
      (Models.gapPartialMCSP_Asymptotic_in_NP_TM_of_witness
        canonicalAsymptoticSpec W)

/-- Canonical `AsymptoticFormulaTrackData` built from a TM witness. -/
def canonicalAsymptoticData_of_TM
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AsymptoticFormulaTrackData where
  spec := canonicalAsymptoticSpec
  N0 := 8
  pAt := canonicalAsymptoticParams
  pAt_n := fun _ _ => rfl
  sliceEq := canonicalSliceEq
  asymptoticNP_TM :=
    Models.gapPartialMCSP_Asymptotic_in_NP_TM_of_witness
      canonicalAsymptoticSpec W

lemma canonicalAsymptoticData_hypothesis
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    asymptoticFormulaTrackHypothesis_of_data
        (canonicalAsymptoticData_of_TM W) =
      canonicalAsymptoticHAsym := rfl

/-- The canonical anti-checker assumptions built from a TM witness. -/
def canonicalAntiCheckerAssumptions_of_TM
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AntiCheckerAssumptions where
  asymptotic := canonicalAsymptoticHAsym
  npBridge := canonicalAsymptoticNPBridge_of_TM W

end Magnification
end Pnp3
