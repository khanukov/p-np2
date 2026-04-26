import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Theorem2Quantitative
import Complexity.Interfaces
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Single-slice escape condition needed to turn slice-by-slice lower bounds into a
genuine `PpolyFormula` contradiction.

For each candidate polynomial size bound, it is enough to find one truth-table
length `2^n` where the lower-bound schedule beats that polynomial witness.
-/
def BeatsEveryPpolyBoundAtSomeTableLength
    (sizeBound : Nat → Nat) : Prop :=
  ∀ polyBound : Nat → Nat,
    (∃ c : Nat, ∀ m : Nat, polyBound m ≤ m ^ c + c) →
      ∃ n : Nat, polyBound (Pnp3.Models.Partial.tableLen n) < sizeBound n + 1

/--
Strengthened growth escape condition: for every polynomial witness and every
requested lower cutoff `nMin`, there is a later truth-table slice where the
size schedule beats that polynomial witness.

This is useful only as a reusable growth-transfer tool.  For the current CKLM
`N^{2-o(1)}` envelope below, the matching frequent-growth obligation is proved
impossible by `not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope`.
-/
def BeatsEveryPpolyBoundFrequentlyAtSomeTableLength
    (sizeBound : Nat → Nat) : Prop :=
  ∀ polyBound : Nat → Nat,
    (∃ c : Nat, ∀ m : Nat, polyBound m ≤ m ^ c + c) →
      ∀ nMin : Nat,
        ∃ n : Nat,
          nMin ≤ n ∧
            polyBound (Pnp3.Models.Partial.tableLen n) < sizeBound n + 1

/--
The strengthened frequent escape condition implies the original one-shot
escape condition by instantiating `nMin = 0`.
-/
theorem BeatsEveryPpolyBoundAtSomeTableLength.of_frequently
    {sizeBound : Nat → Nat}
    (hFreq : BeatsEveryPpolyBoundFrequentlyAtSomeTableLength sizeBound) :
    BeatsEveryPpolyBoundAtSomeTableLength sizeBound := by
  intro polyBound hPoly
  rcases hFreq polyBound hPoly 0 with ⟨n, _hn0, hBeat⟩
  exact ⟨n, hBeat⟩

/--
Transfer lemma for growth obligations.

If `lowerBound` already beats every polynomial witness on arbitrarily late
truth-table slices, and `sizeBound` eventually dominates `lowerBound`, then
`sizeBound` also beats every polynomial witness on some truth-table slice.
-/
theorem BeatsEveryPpolyBoundAtSomeTableLength.of_eventuallyAtLeast
    {lowerBound sizeBound : Nat → Nat}
    (hFreqLower : BeatsEveryPpolyBoundFrequentlyAtSomeTableLength lowerBound)
    (hEventually : ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n → lowerBound n ≤ sizeBound n) :
    BeatsEveryPpolyBoundAtSomeTableLength sizeBound := by
  rcases hEventually with ⟨n0, hEventually⟩
  refine BeatsEveryPpolyBoundAtSomeTableLength.of_frequently ?_
  intro polyBound hPoly nMin
  let nCut := max nMin n0
  rcases hFreqLower polyBound hPoly nCut with ⟨n, hnCut, hBeatLower⟩
  have hn0 : n0 ≤ n := le_trans (le_max_right nMin n0) hnCut
  have hLowerLe : lowerBound n ≤ sizeBound n := hEventually n hn0
  refine ⟨n, le_trans (le_max_left nMin n0) hnCut, ?_⟩
  exact lt_of_lt_of_le hBeatLower (Nat.succ_le_succ hLowerLe)

/--
No-go theorem for the currently encoded CKLM Theorem-2 envelope:
it cannot satisfy `BeatsEveryPpolyBoundAtSomeTableLength`.

Reason: on slice length `m = 2^n`, the encoded envelope is always at most
`m^2`, while the polynomial witness `m ↦ m^8 + 8` is strictly larger than
`m^2 + 1`.  Thus the strict growth obligation needed for the asymptotic
`¬ PpolyFormula` bridge can never hold for this envelope.
-/
theorem not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope
    (c : Nat) :
    ¬ BeatsEveryPpolyBoundAtSomeTableLength (cklmFormulaTheorem2LowerEnvelope c) := by
  intro hBeat
  let polyBound : Nat → Nat := fun m => m ^ 8 + 8
  have hPolyBound :
      ∃ d : Nat, ∀ m : Nat, polyBound m ≤ m ^ d + d := by
    refine ⟨8, ?_⟩
    intro m
    simp [polyBound]
  rcases hBeat polyBound hPolyBound with ⟨n, hlt⟩
  have hExpLe : (2 * n) / (2 ^ (c * Nat.sqrt n + c)) ≤ 2 * n := by
    exact Nat.div_le_self _ _
  have hEnvelopeLe_pow2n :
      cklmFormulaTheorem2LowerEnvelope c n ≤ 2 ^ (2 * n) := by
    unfold cklmFormulaTheorem2LowerEnvelope
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hExpLe
  have hPowLe :
      2 ^ (2 * n) ≤ 2 ^ (8 * n) := by
    have hMul : 2 * n ≤ 8 * n := by omega
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hMul
  have hEnvelopeSuccLe :
      cklmFormulaTheorem2LowerEnvelope c n + 1 ≤
        polyBound (Pnp3.Models.Partial.tableLen n) := by
    have hStep1 :
        cklmFormulaTheorem2LowerEnvelope c n + 1 ≤ 2 ^ (2 * n) + 1 :=
      Nat.succ_le_succ hEnvelopeLe_pow2n
    have hStep2 :
        2 ^ (2 * n) + 1 ≤ 2 ^ (8 * n) + 8 := by
      have hPowPlus :
          2 ^ (2 * n) + 1 ≤ 2 ^ (8 * n) + 1 :=
        Nat.add_le_add_right hPowLe 1
      have hOneLeEight : (1 : Nat) ≤ 8 := by decide
      have hLift :
          2 ^ (8 * n) + 1 ≤ 2 ^ (8 * n) + 8 :=
        Nat.add_le_add_left hOneLeEight (2 ^ (8 * n))
      exact le_trans hPowPlus hLift
    have hPolyEval :
        polyBound (Pnp3.Models.Partial.tableLen n) = 2 ^ (8 * n) + 8 := by
      simp [polyBound, Pnp3.Models.Partial.tableLen, Nat.pow_mul, Nat.mul_comm]
    exact le_trans hStep1 (by simpa [hPolyEval] using hStep2)
  exact (Nat.not_lt_of_ge hEnvelopeSuccLe) hlt

/--
Frequent-escape no-go for the currently encoded CKLM envelope.
-/
theorem not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope
    (c : Nat) :
    ¬ BeatsEveryPpolyBoundFrequentlyAtSomeTableLength
        (cklmFormulaTheorem2LowerEnvelope c) := by
  intro hFreq
  exact not_beatsEveryPpolyBoundAtSomeTableLength_cklmEnvelope c
    (BeatsEveryPpolyBoundAtSomeTableLength.of_frequently hFreq)

/--
Global guardrail: a uniform frequent-growth hypothesis for the current CKLM
envelope family is inconsistent.  Any downstream route requiring this hypothesis
is diagnostic/vacuous, not progress toward `¬ PpolyFormula`.
-/
theorem no_uniform_cklmEnvelopeFrequentEscape : (∀ c : Nat,
    BeatsEveryPpolyBoundFrequentlyAtSomeTableLength
      (cklmFormulaTheorem2LowerEnvelope c)) → False := by
  intro hUniform
  exact not_beatsEveryPpolyBoundFrequentlyAtSomeTableLength_cklmEnvelope 0
    (hUniform 0)

/--
Global asymptotic language attached to one thresholded exact-slice schedule.

At lengths of the form `2^n`, this recovers the exact thresholded tree-MCSP
slice for the corresponding `n`; on all other lengths it returns `false`.
-/
noncomputable def formulaCircuitAsymptoticLanguageOfSliceSpec
    (spec : FormulaCircuitSliceSpec) :
    Pnp3.ComplexityInterfaces.Language := by
  classical
  intro m x
  exact if hm : m = Pnp3.Models.Partial.tableLen (Nat.log 2 m) then
      formulaCircuitThresholdLanguage spec (Nat.log 2 m) m x
    else
      false

/--
On the canonical truth-table lengths `2^n`, the asymptotic language agrees
exactly with the `n`-th thresholded MCSP slice.
-/
theorem formulaCircuitAsymptoticLanguageOfSliceSpec_eq_thresholdLanguage_at_tableLen
    (spec : FormulaCircuitSliceSpec)
    (n : Nat)
    (x : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.Models.Partial.tableLen n)) :
    formulaCircuitAsymptoticLanguageOfSliceSpec spec
        (Pnp3.Models.Partial.tableLen n) x =
      formulaCircuitThresholdLanguage spec n
        (Pnp3.Models.Partial.tableLen n) x := by
  have hlog :
      Nat.log 2 (Pnp3.Models.Partial.tableLen n) = n := by
    simpa [Pnp3.Models.Partial.tableLen] using Nat.log_pow Nat.one_lt_two n
  have hm :
      Pnp3.Models.Partial.tableLen n =
        Pnp3.Models.Partial.tableLen
          (Nat.log 2 (Pnp3.Models.Partial.tableLen n)) := by
    rw [hlog]
  unfold formulaCircuitAsymptoticLanguageOfSliceSpec
  have hIf :
      (if hm' :
            Pnp3.Models.Partial.tableLen n =
              Pnp3.Models.Partial.tableLen
                (Nat.log 2 (Pnp3.Models.Partial.tableLen n)) then
          formulaCircuitThresholdLanguage spec
            (Nat.log 2 (Pnp3.Models.Partial.tableLen n))
            (Pnp3.Models.Partial.tableLen n) x
        else
          false) =
        formulaCircuitThresholdLanguage spec
          (Nat.log 2 (Pnp3.Models.Partial.tableLen n))
          (Pnp3.Models.Partial.tableLen n) x := by
    exact if_pos hm
  rw [hIf, hlog]

/--
Published slice lower bound compiled into a contradiction against the strict
`pnp3` class `PpolyFormula` for the corresponding global asymptotic language.
-/
theorem no_PpolyFormula_of_formulaCircuitPublishedLowerBoundContract_and_growth
    {spec : FormulaCircuitSliceSpec}
    (contract : FormulaCircuitPublishedLowerBoundContract spec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguageOfSliceSpec spec) := by
  intro hFormula
  rcases hFormula with ⟨w, _⟩
  obtain ⟨n, hBeatPoly⟩ := hGrowth w.polyBound w.polyBound_poly
  have hSliceLower :
      SizeLowerBound
        formulaCircuitFamilyClass
        (formulaCircuitThresholdLanguage spec n)
        (formulaCircuitThresholdLowerBound spec n) :=
    formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract
      contract n
  have hCompSlice :
      ∀ x : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.Models.Partial.tableLen n),
        Pnp3.ComplexityInterfaces.FormulaCircuit.eval
            (w.family (Pnp3.Models.Partial.tableLen n)) x =
          formulaCircuitThresholdLanguage spec n
            (Pnp3.Models.Partial.tableLen n) x := by
    intro x
    calc
      Pnp3.ComplexityInterfaces.FormulaCircuit.eval
          (w.family (Pnp3.Models.Partial.tableLen n)) x
          = formulaCircuitAsymptoticLanguageOfSliceSpec spec
              (Pnp3.Models.Partial.tableLen n) x := by
              exact w.correct (Pnp3.Models.Partial.tableLen n) x
      _ = formulaCircuitThresholdLanguage spec n
            (Pnp3.Models.Partial.tableLen n) x := by
            exact
              formulaCircuitAsymptoticLanguageOfSliceSpec_eq_thresholdLanguage_at_tableLen
                spec n x
  have hSizeLower :
      spec.sizeBound n + 1 ≤
        Pnp3.ComplexityInterfaces.FormulaCircuit.size
          (w.family (Pnp3.Models.Partial.tableLen n)) := by
    simpa [formulaCircuitFamilyClass, formulaCircuitThresholdLowerBound,
      exactTreeMCSPThresholdLowerBound] using
      hSliceLower
        (Pnp3.Models.Partial.tableLen n)
        (w.family (Pnp3.Models.Partial.tableLen n))
        hCompSlice
  have hSizeUpper :
      Pnp3.ComplexityInterfaces.FormulaCircuit.size
          (w.family (Pnp3.Models.Partial.tableLen n)) ≤
        w.polyBound (Pnp3.Models.Partial.tableLen n) :=
    w.family_size_le (Pnp3.Models.Partial.tableLen n)
  have hBound :
      spec.sizeBound n + 1 ≤ w.polyBound (Pnp3.Models.Partial.tableLen n) :=
    le_trans hSizeLower hSizeUpper
  exact Nat.not_lt_of_ge hBound hBeatPoly

/--
Backward-compatible wrapper: interpret a PRG hardness spec as its underlying
thresholded slice specification.
-/
noncomputable def formulaCircuitAsymptoticLanguage
    (spec : LocalPRGHardnessSpec) :
    Pnp3.ComplexityInterfaces.Language :=
  formulaCircuitAsymptoticLanguageOfSliceSpec spec.toFormulaCircuitSliceSpec

/--
Backward-compatible wrapper for the slice-agreement theorem on the old
`LocalPRGHardnessSpec` surface.
-/
theorem formulaCircuitAsymptoticLanguage_eq_thresholdMCSPLanguage_at_tableLen
    (spec : LocalPRGHardnessSpec)
    (n : Nat)
    (x : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.Models.Partial.tableLen n)) :
    formulaCircuitAsymptoticLanguage spec (Pnp3.Models.Partial.tableLen n) x =
      thresholdMCSPLanguage spec n (Pnp3.Models.Partial.tableLen n) x := by
  exact
    formulaCircuitAsymptoticLanguageOfSliceSpec_eq_thresholdLanguage_at_tableLen
      spec.toFormulaCircuitSliceSpec n x

/--
One-sided local-PRG route compiled into the same `PpolyFormula` contradiction
via the smaller theorem-facing formula lower-bound contract.
-/
theorem no_PpolyFormula_of_formulaCircuitPublishedOneSidedLocalPRGRoute_and_growth
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedOneSidedLocalPRGRouteContract spec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage spec) := by
  simpa [formulaCircuitAsymptoticLanguage] using
    no_PpolyFormula_of_formulaCircuitPublishedLowerBoundContract_and_growth
      (formulaCircuitPublishedLowerBoundContract_of_publishedOneSidedLocalPRGRoute
        contract)
      hGrowth

/--
Two-sided local-PRG route compiled into the same `PpolyFormula` contradiction.
-/
theorem no_PpolyFormula_of_formulaCircuitPublishedLocalPRGRoute_and_growth
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage spec) := by
  simpa [formulaCircuitAsymptoticLanguage] using
    no_PpolyFormula_of_formulaCircuitPublishedLowerBoundContract_and_growth
      (formulaCircuitPublishedLowerBoundContract_of_publishedLocalPRGRoute contract)
      hGrowth

/--
Named CKLM-style specialization for the formula / branching-program published
route, instantiated on the in-repo formula syntax.
-/
theorem no_PpolyFormula_of_CKLM_formulaOrBranchingProgramRoute_and_growth
    {spec : FormulaOrBranchingProgramLocalPRGHardnessSpec}
    (contract :
      FormulaCircuitPublishedLocalPRGRouteContract spec.toLocalPRGHardnessSpec)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength spec.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage spec.toLocalPRGHardnessSpec) := by
  exact no_PpolyFormula_of_formulaCircuitPublishedLocalPRGRoute_and_growth
    contract hGrowth

/--
Mainline CKLM source-to-asymptotic bridge: the explicit local-PRG source
contract yields the same `PpolyFormula` contradiction, provided the source
size schedule escapes every polynomial bound on some truth-table length.
-/
theorem no_PpolyFormula_of_CKLMFormulaCircuitLocalPRGSource_and_growth
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (hGrowth : BeatsEveryPpolyBoundAtSomeTableLength source.sizeBound) :
    ¬ Pnp3.ComplexityInterfaces.PpolyFormula
        (formulaCircuitAsymptoticLanguage source.toLocalPRGHardnessSpec) := by
  exact no_PpolyFormula_of_formulaCircuitPublishedLocalPRGRoute_and_growth
    contract.toPublishedRoute hGrowth

end AlgorithmsToLowerBounds
end Pnp4
