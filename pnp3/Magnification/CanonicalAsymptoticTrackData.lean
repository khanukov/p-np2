import Magnification.FinalResultMainline
import Models.Model_PartialMCSP

/-!
# Canonical asymptotic formula-track data

This module fixes the **canonical** asymptotic spec/parameter family used in
the final magnification routes.  Its purpose is to move the
`(hAsym, hNPbridge)` pair — currently passed as hypothesis parameters to many
mainline endpoints (`i4_final_wiring_*`, the eventual DAG routes, the
`RefutedRoute_*` audit endpoints) — into a concrete in-repo construction.

The canonical track uses the smallest gap allowed by the asymptotic spec
interface:

* `sYES n := 1` (smallest value compatible with `sYES_pos`),
* `sNO n := 2` (smallest value compatible with `gap_ok`).

With this choice the per-slice `circuit_bound_ok` obligation reduces to the
clean Shannon-counting inequality `n + 2 < 2 ^ (2^n / 2)`, provable for all
`n ≥ 4`.

### Layered conditional structure

This module is **layered**:

1. `canonicalAsymptoticSpec` — pure data, no proof obligations.
2. `canonicalAsymptoticParams n hn` — fully unconditional, including the
   Shannon-counting `circuit_bound_ok`.
3. `canonicalAsymptoticHAsym` — fully unconditional once
   `canonicalSliceEq` is built.  The slice-equality is a pointwise unfolding
   of the asymptotic and per-slice language definitions, both of which
   evaluate to `decide (PartialMCSP_YES_at n 1 T)` at canonical length under
   the canonical spec (because `canonicalAsymptoticSpec.sYES n = 1 =
   (canonicalAsymptoticParams n hn).sYES`).
4. `canonicalAsymptoticNPBridge_of_TM`, `canonicalAsymptoticData_of_TM`,
   `canonicalAntiCheckerAssumptions_of_TM` — built from a single concrete TM
   witness for the canonical spec.

### Status

* Items 1–2 and 4 are fully unconditional once Item 3 lands.
* Item 3 (`canonicalSliceEq`) is a straightforward Boolean unfolding using
  `gapPartialMCSP_language_true_iff_yes` and a parallel asymptotic-side
  helper `gapPartialMCSP_AsymptoticLanguage_inputLen_true_iff_yes`.
* The strict-NP TM witness in Item 4 is the **only remaining gap** for
  closing the canonical NP pullback unconditionally.  Building it
  constructively requires composing the existing toolkit primitives in
  `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/`.  This module fixes
  the *interface* through which any such witness flows.

The D0-feasibility audit recorded that the canonical spec matches the
published OPS19/CJW20 magnification statement; this file realizes the
corresponding Lean interface side.

Downstream theorems can be migrated from
`(hAsym : AsymptoticFormulaTrackHypothesis) (hNPbridge : AsymptoticNPPullback hAsym)`
to `(W : GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec)` without
any change to the magnification proof structure.
-/

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/-! ## Canonical asymptotic spec -/

/-- Canonical asymptotic spec: `sYES n = 1`, `sNO n = 2`.

This is the smallest legal value for both thresholds compatible with the
`GapPartialMCSPAsymptoticSpec` interface (`sYES_pos` requires `1 ≤ sYES n`,
`gap_ok` requires `sYES n + 1 ≤ sNO n`).  Using the smallest legal thresholds
keeps the Shannon-counting obligation on `pAt` as cheap as possible. -/
def canonicalAsymptoticSpec : GapPartialMCSPAsymptoticSpec where
  sYES := fun _ => 1
  sNO := fun _ => 2
  gap_ok := fun _ => by decide
  sYES_pos := fun _ => by decide

@[simp] lemma canonicalAsymptoticSpec_sYES (n : Nat) :
    canonicalAsymptoticSpec.sYES n = 1 := rfl

@[simp] lemma canonicalAsymptoticSpec_sNO (n : Nat) :
    canonicalAsymptoticSpec.sNO n = 2 := rfl

/-! ## Shannon counting for `sNO = 2`

The per-slice `GapPartialMCSPParams.circuit_bound_ok` requires
`circuitCountBound n (sNO - 1) < 2 ^ (Partial.tableLen n / 2)`.
With `sNO = 2` this reduces to `n + 2 < 2 ^ (2^n / 2)`, provable for all
`n ≥ 4` via a short induction.
-/

/-- For `n ≥ 1`, `2^n / 2 = 2^(n - 1)`. -/
private lemma two_pow_div_two (n : Nat) (hn : 1 ≤ n) :
    2 ^ n / 2 = 2 ^ (n - 1) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [← hsub]
    exact Nat.pow_succ 2 (n - 1)
  rw [hpow]
  exact Nat.mul_div_cancel _ (by decide : 0 < 2)

/-- For `n ≥ 4`, `n + 2 ≤ 2^(n - 1)`.  Inductive numerical lemma. -/
private lemma succ_succ_le_pow_pred : ∀ n : Nat, 4 ≤ n → n + 2 ≤ 2 ^ (n - 1)
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | (n + 8), _ => by
    -- Step: from `(n + 7) + 2 ≤ 2^(n + 6)` derive `(n + 8) + 2 ≤ 2^(n + 7)`.
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

/-- The Shannon-counting bound for `sNO = 2` and `n ≥ 8`.

This is the precise inequality demanded by `GapPartialMCSPParams.circuit_bound_ok`
when `sNO = 2`, after unfolding `circuitCountBound n 1 = n + 2`. -/
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
  -- `2^(n-1) < 2^(2^(n-1))` because `n - 1 < 2^(n-1)` (Mathlib lemma).
  have hexp_strict : 2 ^ (n - 1) < 2 ^ (2 ^ (n - 1)) := by
    have hself : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self
    -- Monotonicity of `2^_` in the exponent.
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

/-! ## Asymptotic-language evaluation at canonical length

The asymptotic language is defined via a `dite` on `∃ m, N = Partial.inputLen m`,
with `Classical.choose` selecting the witness `m`.  At `N = Partial.inputLen n`,
the chosen `m` equals `n` by `partialInputLen_injective`. -/

/-- At canonical length `N = Partial.inputLen n`, the asymptotic language is
`true` iff `PartialMCSP_YES_at n (spec.sYES n)` on the decoded table.

The proof works by case-splitting on the YES predicate and unfolding the
asymptotic-language definition.  Because `Partial.inputLen` is injective,
`Classical.choose` of the canonical-length existential resolves to `n`. -/
lemma gapPartialMCSP_AsymptoticLanguage_inputLen_true_iff_yes
    (spec : GapPartialMCSPAsymptoticSpec) (n : Nat)
    (x : Core.BitVec (Partial.inputLen n)) :
    gapPartialMCSP_AsymptoticLanguage spec (Partial.inputLen n) x = true ↔
      PartialMCSP_YES_at n (spec.sYES n) (decodePartial x) := by
  classical
  -- Canonical existential and its choose-witness identification.
  have hShape : ∃ m : Nat, Partial.inputLen n = Partial.inputLen m := ⟨n, rfl⟩
  have hChoose_spec : Partial.inputLen n =
      Partial.inputLen (Classical.choose hShape) := Classical.choose_spec hShape
  have hChoose_eq : Classical.choose hShape = n :=
    (partialInputLen_injective hChoose_spec).symm
  -- Direct boolean simplification through the noncomputable `dite`.
  simp [gapPartialMCSP_AsymptoticLanguage, hShape, hChoose_eq]

/-! ## Slice-equality between asymptotic and per-slice languages -/

/-- Slice equality at canonical length for the canonical spec/params pair.

Both languages reduce to `decide (PartialMCSP_YES_at n 1 (decodePartial x))`
at canonical length `N = inputLen n`, because
`canonicalAsymptoticSpec.sYES n = 1 = (canonicalAsymptoticParams n hn).sYES`. -/
lemma canonicalSliceEq (n : Nat) (hn : 8 ≤ n)
    (x : Core.BitVec (Models.partialInputLen (canonicalAsymptoticParams n hn))) :
    gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
        (Models.partialInputLen (canonicalAsymptoticParams n hn)) x =
      gapPartialMCSP_Language (canonicalAsymptoticParams n hn)
        (Models.partialInputLen (canonicalAsymptoticParams n hn)) x := by
  classical
  set p : GapPartialMCSPParams := canonicalAsymptoticParams n hn with hp_def
  -- `partialInputLen p = Partial.inputLen p.n = Partial.inputLen n`.
  have hLenEq : Models.partialInputLen p = Partial.inputLen n := rfl
  -- Case split on the canonical YES predicate.
  by_cases hYes : PartialMCSP_YES p (decodePartial x)
  · have hRHS_true :
        gapPartialMCSP_Language p (Models.partialInputLen p) x = true :=
      (gapPartialMCSP_language_true_iff_yes p x).2 hYes
    -- The spec-side YES is the same predicate after rewriting `sYES = 1`.
    have hYesAt :
        PartialMCSP_YES_at n 1 (decodePartial (n := n) x) := by
      -- `PartialMCSP_YES p = ∃ C : Circuit p.n, C.size ≤ p.sYES ∧ is_consistent C T`,
      -- and `p.n = n`, `p.sYES = 1`.
      rcases hYes with ⟨C, hSize, hCons⟩
      exact ⟨C, by simpa using hSize, hCons⟩
    have hLHS_true :
        gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
            (Models.partialInputLen p) x = true := by
      rw [hLenEq]
      exact (gapPartialMCSP_AsymptoticLanguage_inputLen_true_iff_yes
        canonicalAsymptoticSpec n x).2 (by simpa using hYesAt)
    rw [hLHS_true, hRHS_true]
  · have hRHS_not_true :
        gapPartialMCSP_Language p (Models.partialInputLen p) x ≠ true := by
      intro hT
      exact hYes ((gapPartialMCSP_language_true_iff_yes p x).1 hT)
    have hRHS_false :
        gapPartialMCSP_Language p (Models.partialInputLen p) x = false := by
      cases hV : gapPartialMCSP_Language p (Models.partialInputLen p) x
      · rfl
      · exact (hRHS_not_true hV).elim
    have hYesAt_not :
        ¬ PartialMCSP_YES_at n 1 (decodePartial (n := n) x) := by
      intro hAt
      apply hYes
      rcases hAt with ⟨C, hSize, hCons⟩
      exact ⟨C, by simpa using hSize, hCons⟩
    have hLHS_not_true :
        gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
            (Models.partialInputLen p) x ≠ true := by
      intro hT
      rw [hLenEq] at hT
      have hAt : PartialMCSP_YES_at n (canonicalAsymptoticSpec.sYES n)
          (decodePartial x) :=
        (gapPartialMCSP_AsymptoticLanguage_inputLen_true_iff_yes
          canonicalAsymptoticSpec n x).1 hT
      exact hYesAt_not (by simpa using hAt)
    have hLHS_false :
        gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
            (Models.partialInputLen p) x = false := by
      cases hV : gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec
          (Models.partialInputLen p) x
      · rfl
      · exact (hLHS_not_true hV).elim
    rw [hLHS_false, hRHS_false]

/-! ## Canonical `AsymptoticFormulaTrackHypothesis` -/

/-- Canonical asymptotic hypothesis, with threshold `N0 := 8`. -/
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

The bridge is unconditional **once** a TM witness for
`canonicalAsymptoticSpec` is provided.  Such a witness is a
`Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec` —
i.e., a concrete verifier TM with polynomial runtime that accepts on
`concat x w` iff the asymptotic language is true at `x`.

The asymptotic-spec TM witness is the **only remaining gap** for closing the
canonical NP pullback unconditionally.  Building it constructively requires
composing toolkit primitives in
`pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/` (see `Foundation.lean`,
`AtomicPrograms.lean`, `BinaryCounter.lean`, `ConstStatePhasedProgram.lean`,
`GateWrappers.lean`) into a verifier that decides
`PartialMCSP_YES_at n 1 (decodePartial x)` from a 1-of-(`n + 2`) certificate
selecting the candidate size-1 circuit.

This module fixes the interface; the toolkit composition is a separate
engineering deliverable (estimated 800–1500 LOC; see the D0-audit summary).
-/

/-- NP-bridge for the canonical asymptotic spec from a concrete TM witness. -/
def canonicalAsymptoticNPBridge_of_TM
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AsymptoticNPPullback canonicalAsymptoticHAsym where
  strictAsymptotic :=
    Models.gapPartialMCSP_Asymptotic_in_NP_of_TM canonicalAsymptoticSpec
      (Models.gapPartialMCSP_Asymptotic_in_NP_TM_of_witness
        canonicalAsymptoticSpec W)

/-- Canonical `AsymptoticFormulaTrackData` built from a TM witness.

This is the recommended entry point: any consumer that takes an
`AsymptoticFormulaTrackData` can be fed the canonical track once a TM witness
is supplied. -/
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

/-- The canonical data, viewed as the canonical hypothesis. -/
lemma canonicalAsymptoticData_hypothesis
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    asymptoticFormulaTrackHypothesis_of_data (canonicalAsymptoticData_of_TM W) =
      canonicalAsymptoticHAsym := rfl

/-! ## Hypothesis-level provider -/

/-- The canonical anti-checker assumptions built from a TM witness. -/
def canonicalAntiCheckerAssumptions_of_TM
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AntiCheckerAssumptions where
  asymptotic := canonicalAsymptoticHAsym
  npBridge := canonicalAsymptoticNPBridge_of_TM W

end Magnification
end Pnp3
