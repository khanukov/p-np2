import Magnification.Bridge_to_Magnification_Partial
import Magnification.AC0LocalityBridge
import Magnification.Facts_Magnification_Partial
import Magnification.LocalityProvider_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces

namespace Pnp3
namespace Magnification

open Models
open LowerBounds
open ComplexityInterfaces

/-- Global strict NP witness family for fixed-parameter partial-MCSP languages. -/
def StrictGapNPFamily : Prop :=
  ∀ p : GapPartialMCSPParams,
    ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)

/--
Constructive bridge: explicit TM witnesses for each fixed parameter imply the
global strict NP-family hypothesis.
-/
theorem strictGapNPFamily_of_tmWitnesses
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
  StrictGapNPFamily := by
  intro p
  exact gapPartialMCSP_in_NP_TM_of_witness p (hW p)

/--
Asymptotic entry hypothesis for the partial formula track:
explicitly provides parameters and lower-bound hypotheses at all
sizes above a threshold `N0`.
-/
structure AsymptoticFormulaTrackHypothesis where
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  pAt_hyp : ∀ n (hn : N0 ≤ n), FormulaLowerBoundHypothesisPartial (pAt n hn) (1 : Rat)

/--
Asymptotic entry hypothesis for the semantic (non-vacuous) Step-C route.
-/
structure AsymptoticFormulaTrackHypothesis_semantic where
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  pAt_hyp :
    ∀ n (hn : N0 ≤ n),
      FormulaLowerBoundHypothesisPartial_semantic (pAt n hn) (1 : Rat)

/--
Asymptotic constructive Step-C hypothesis directly on syntactic AC0 easy families:
for each sufficiently large size and each solver, provide AC0 realizability of
`AC0EasyFamily` together with the compression-hypothesis lower bound.
-/
structure AsymptoticSyntacticEasyHypothesis where
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  easyAt :
    ∀ n (hn : N0 ≤ n) (solver : SmallAC0Solver_Partial (pAt n hn)),
      ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
        (AC0EasyFamily solver.params.ac0)
  compressionAt :
    ∀ n (hn : N0 ≤ n), AC0CompressionHypothesis (pAt n hn)

/--
Constructive asymptotic hypothesis for the AC0 lower-bound side:
for each size, all small AC0 solvers at that parameter have a default
all-functions multi-switching package.
-/
structure AsymptoticDefaultMultiSwitchingHypothesis where
  N0 : Nat
  pAt : ∀ n : Nat, N0 ≤ n → GapPartialMCSPParams
  pAt_n : ∀ n (hn : N0 ≤ n), (pAt n hn).n = n
  msAt :
    ∀ n (hn : N0 ≤ n) (solver : SmallAC0Solver_Partial (pAt n hn)),
      AllFunctionsAC0MultiSwitchingWitness solver.params.ac0

/--
Bridge from constructive default multi-switching data to the standard
asymptotic formula-track hypothesis.
-/
def asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis) :
  AsymptoticFormulaTrackHypothesis := by
  refine
    { N0 := hMS.N0
      pAt := hMS.pAt
      pAt_n := hMS.pAt_n
      pAt_hyp := ?_ }
  intro n hn
  exact
    formula_hypothesis_from_pipeline_partial_of_default_multiSwitching
      (p := hMS.pAt n hn)
      (δ := (1 : Rat))
      (hδ := zero_lt_one)
      (hMS := hMS.msAt n hn)

/--
Build semantic asymptotic formula-track data from direct syntactic easy-family
assumptions.
-/
def asymptoticFormulaTrackHypothesis_semantic_of_syntacticEasy
  (hEasy : AsymptoticSyntacticEasyHypothesis) :
  AsymptoticFormulaTrackHypothesis_semantic := by
  refine
    { N0 := hEasy.N0
      pAt := hEasy.pAt
      pAt_n := hEasy.pAt_n
      pAt_hyp := ?_ }
  intro n hn
  exact
    formula_hypothesis_from_syntacticEasy_partial
      (p := hEasy.pAt n hn)
      (δ := (1 : Rat))
      (hδ := zero_lt_one)
      (hEasy := hEasy.easyAt n hn)
      (hComp := hEasy.compressionAt n hn)

/-- Local witness extracted from the asymptotic formula-track hypothesis at size `n`. -/
def AsymptoticFormulaTrackWitnessAt (n : Nat) : Prop :=
  ∃ p : GapPartialMCSPParams, p.n = n ∧ FormulaLowerBoundHypothesisPartial p (1 : Rat)

/-- Materialize a witness at any `n ≥ N0` from asymptotic track data. -/
theorem witnessAt_of_asymptotic
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (n : Nat) (hn : hAsym.N0 ≤ n) :
  AsymptoticFormulaTrackWitnessAt n := by
  refine ⟨hAsym.pAt n hn, hAsym.pAt_n n hn, hAsym.pAt_hyp n hn⟩

/--
Parameter-generic final statement for the partial formula track.
This is the primary non-canonical entrypoint.
-/
theorem NP_not_subset_PpolyFormula_from_params
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat))
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas
      (hProvider := hProvider)
      (p := p)
      (δ := (1 : Rat)) hHyp hNPstrict

/-- Semantic fixed-parameter entrypoint. -/
theorem NP_not_subset_PpolyFormula_from_params_semantic
  (hProvider : StructuredLocalityProviderPartial_semantic)
  (p : GapPartialMCSPParams)
  (hHyp : FormulaLowerBoundHypothesisPartial_semantic p (1 : Rat))
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas_semantic
      (hProvider := hProvider)
      (p := p)
      (δ := (1 : Rat)) hHyp hNPstrict

/-- Semantic fixed-parameter entrypoint with auto Step-C hypothesis. -/
theorem NP_not_subset_PpolyFormula_from_params_semantic_auto
  (hProvider : StructuredLocalityProviderPartial_semantic)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  have hHyp : FormulaLowerBoundHypothesisPartial_semantic p (1 : Rat) :=
    formula_hypothesis_from_pipeline_partial_constructive
      (p := p) (δ := (1 : Rat)) hδ
  exact
    NP_not_subset_PpolyFormula_from_params_semantic
      (hProvider := hProvider) (p := p) (hHyp := hHyp) hNPstrict

/--
Preferred semantic fixed-parameter entrypoint from direct syntactic easy-family
assumptions.
-/
theorem NP_not_subset_PpolyFormula_from_params_semantic_of_syntacticEasy
  (hProvider : StructuredLocalityProviderPartial_semantic)
  (p : GapPartialMCSPParams)
  (hEasy : ∀ solver : SmallAC0Solver_Partial p,
    ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
      (AC0EasyFamily solver.params.ac0))
  (hComp : AC0CompressionHypothesis p)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hδ : (0 : Rat) < (1 : Rat) := zero_lt_one
  exact
    NP_not_subset_PpolyFormula_from_partial_formulas_semantic_of_syntacticEasy
      (hProvider := hProvider)
      (p := p)
      (δ := (1 : Rat))
      hδ hEasy hComp hNPstrict

/--
Asymptotic wrapper: if the partial pipeline lower bound is available at all
sufficiently large sizes, we can instantiate the bridge at any such size.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPstrict : ComplexityInterfaces.NP_strict
    (gapPartialMCSP_Language (hAsym.pAt hAsym.N0 (le_rfl)))) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hHyp : FormulaLowerBoundHypothesisPartial (hAsym.pAt hAsym.N0 (le_rfl)) (1 : Rat) :=
    hAsym.pAt_hyp hAsym.N0 (le_rfl)
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := hAsym.pAt hAsym.N0 (le_rfl)) (δ := (1 : Rat)) hHyp

/-- Asymptotic semantic wrapper for formula separation. -/
theorem NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic
  (hProvider : StructuredLocalityProviderPartial_semantic)
  (hAsym : AsymptoticFormulaTrackHypothesis_semantic)
  (hNPstrict : ComplexityInterfaces.NP_strict
    (gapPartialMCSP_Language (hAsym.pAt hAsym.N0 (le_rfl)))) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hHyp :
      FormulaLowerBoundHypothesisPartial_semantic
        (hAsym.pAt hAsym.N0 (le_rfl)) (1 : Rat) :=
    hAsym.pAt_hyp hAsym.N0 (le_rfl)
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation_semantic
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := hAsym.pAt hAsym.N0 (le_rfl)) (δ := (1 : Rat)) hHyp

/--
Preferred asymptotic semantic wrapper from direct syntactic easy-family data.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic_of_syntacticEasy
  (hProvider : StructuredLocalityProviderPartial_semantic)
  (hEasy : AsymptoticSyntacticEasyHypothesis)
  (hNPstrict : ComplexityInterfaces.NP_strict
    (gapPartialMCSP_Language
      ((asymptoticFormulaTrackHypothesis_semantic_of_syntacticEasy hEasy).pAt
        (asymptoticFormulaTrackHypothesis_semantic_of_syntacticEasy hEasy).N0
        (le_rfl)))) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic
      (hProvider := hProvider)
      (hAsym := asymptoticFormulaTrackHypothesis_semantic_of_syntacticEasy hEasy)
      (hNPstrict := hNPstrict)

/--
Asymptotic wrapper using constructive default multi-switching data.
This closes the AC0-side lower-bound premise without external AC0 witness
arguments; locality/provider obligations are still handled separately.
-/
theorem NP_not_subset_PpolyFormula_of_defaultMultiSwitching_hypothesis
  (hProvider : StructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPstrict : ComplexityInterfaces.NP_strict
    (gapPartialMCSP_Language
      ((asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS).pAt
        (asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS).N0 (le_rfl)))) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
      (hProvider := hProvider)
      (hAsym := asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS)
      (hNPstrict := hNPstrict)

/--
Bridge from a concrete asymptotic witness at one size to formula separation.
This is the direct trigger-facing entrypoint without any hardcoded canonical size.
-/
theorem NP_not_subset_PpolyFormula_of_witness_at
  (hProvider : StructuredLocalityProviderPartial)
  {n : Nat}
  (hW : AsymptoticFormulaTrackWitnessAt n)
  (hNPstrict : ∀ p : GapPartialMCSPParams, p.n = n →
    ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  obtain ⟨p, hpN, hHyp⟩ := hW
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider) (hNPstrict := hNPstrict p hpN) (p := p) (δ := (1 : Rat)) hHyp

/--
Generic entrypoint: derive `NP ⊄ PpolyFormula` from one language-level collapse
witness (`L ∈ NP` together with `PpolyFormula L -> False`).
-/
theorem NP_not_subset_PpolyFormula_of_language
  (L : ComplexityInterfaces.Language)
  (hNPstrict : ComplexityInterfaces.NP_strict L)
  (hCollapse : ComplexityInterfaces.PpolyFormula L → False) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hStrict : ComplexityInterfaces.NP_strict_not_subset_PpolyFormula :=
    ComplexityInterfaces.NP_strict_not_subset_PpolyFormula_of_contra (by
      intro hAllStrict
      exact hCollapse (hAllStrict L hNPstrict))
  exact ComplexityInterfaces.NP_not_subset_PpolyFormula_of_NP_strict_not_subset_PpolyFormula hStrict

/--
Asymptotic-language entrypoint: this is the direct hook for
`gapPartialMCSP_AsymptoticLanguage` once NP-membership/collapse lemmas are available.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_language
  (spec : GapPartialMCSPAsymptoticSpec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec))
  (hCollapse :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_of_language
      (L := gapPartialMCSP_AsymptoticLanguage spec)
      hNP_TM hCollapse

/--
TM-strict entrypoint: same as `NP_not_subset_PpolyFormula_of_asymptotic_language`,
but consumes `NP_TM` and bridges via `NP_of_NP_TM`.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_language_TM
  (spec : GapPartialMCSPAsymptoticSpec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec))
  (hCollapse :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact NP_not_subset_PpolyFormula_of_asymptotic_language spec hNP_TM hCollapse

/--
Transfer interface: to collapse `PpolyFormula` for the asymptotic language,
it is enough to map it to a fixed-parameter language where the provider-based
contradiction is already available.
-/
def AsymptoticLanguageCollapseTransfer
  (spec : GapPartialMCSPAsymptoticSpec) : Prop :=
  ∃ p : GapPartialMCSPParams,
    FormulaLowerBoundHypothesisPartial p (1 : Rat) ∧
    (ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p))

/--
Slice-agreement condition connecting the asymptotic language with a fixed
parameter language at the target input length `partialInputLen p`.
-/
def AsymptoticLanguageSliceAgreement
  (spec : GapPartialMCSPAsymptoticSpec) (p : GapPartialMCSPParams) : Prop :=
  ∀ x : ComplexityInterfaces.Bitstring (Models.partialInputLen p),
    gapPartialMCSP_AsymptoticLanguage spec (Models.partialInputLen p) x =
      gapPartialMCSP_Language p (Models.partialInputLen p) x

/--
If asymptotic and fixed languages agree on the target length, any strict
formula witness for the asymptotic language can be converted to a strict
formula witness for the fixed language.
-/
theorem ppolyFormula_fixed_of_asymptotic_slice
  (spec : GapPartialMCSPAsymptoticSpec)
  (p : GapPartialMCSPParams)
  (hAgree : AsymptoticLanguageSliceAgreement spec p) :
  ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) →
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) := by
  intro hAsym
  rcases hAsym with ⟨w, _⟩
  let c0 : Nat := Classical.choose w.polyBound_poly
  let c : Nat := c0 + 2
  have hc0 : ∀ n, w.polyBound n ≤ n ^ c0 + c0 := Classical.choose_spec w.polyBound_poly
  refine ⟨{ polyBound := fun n => n ^ c + c
            polyBound_poly := ?_
            family := fun n =>
              if h : n = Models.partialInputLen p then
                w.family n
              else
                ComplexityInterfaces.FormulaCircuit.const false
            family_size_le := ?_
            correct := ?_ }, trivial⟩
  · exact ⟨c, by intro n; rfl⟩
  · intro n
    by_cases hN : n = Models.partialInputLen p
    · simp [hN]
      have hSize : ComplexityInterfaces.FormulaCircuit.size (w.family n) ≤ w.polyBound n :=
        w.family_size_le n
      have hBound0 : w.polyBound n ≤ n ^ c0 + c0 := hc0 n
      have hPow : n ^ c0 ≤ n ^ c := by
        have hn_pos : 0 < n := by
          have hPosPartial :
              0 < Models.partialInputLen p := by
            simp [Models.partialInputLen, Models.Partial.inputLen, Models.Partial.tableLen]
          simpa [hN] using hPosPartial
        exact Nat.pow_le_pow_right hn_pos (Nat.le_add_right c0 2)
      have hBound : n ^ c0 + c0 ≤ n ^ c + c := by
        have hcLe : c0 ≤ c := by simp [c]
        omega
      have hBound' : n ^ c0 + c0 ≤ Models.partialInputLen p ^ c + c := by
        simpa [hN] using hBound
      exact le_trans hSize (le_trans hBound0 hBound')
    · simp [hN]
      have hc_ge_one : 1 ≤ c := by simp [c]
      have hOneLe : 1 ≤ n ^ c + 1 := by omega
      have hTail : n ^ c + 1 ≤ n ^ c + c := Nat.add_le_add_left hc_ge_one (n ^ c)
      exact le_trans hOneLe hTail
  · intro n x
    by_cases hN : n = Models.partialInputLen p
    · subst hN
      simp
      exact Eq.trans (w.correct (Models.partialInputLen p) x) (hAgree x)
    · simp [Models.gapPartialMCSP_Language, hN]
      rfl

/--
Constructive transfer from an explicit fixed-parameter witness:
lower-bound hypothesis + slice agreement.
-/
theorem asymptoticLanguageCollapseTransfer_of_sliceAgreement
  (spec : GapPartialMCSPAsymptoticSpec)
  (p : GapPartialMCSPParams)
  (hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat))
  (hAgree : AsymptoticLanguageSliceAgreement spec p) :
  AsymptoticLanguageCollapseTransfer spec := by
  refine ⟨p, hHyp, ?_⟩
  exact ppolyFormula_fixed_of_asymptotic_slice spec p hAgree

/--
Constructive packaged witness for `AsymptoticLanguageCollapseTransfer`.
-/
structure ConstructiveAsymptoticLanguageCollapseTransfer
  (spec : GapPartialMCSPAsymptoticSpec) where
  p : GapPartialMCSPParams
  hyp : FormulaLowerBoundHypothesisPartial p (1 : Rat)
  map :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) →
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)

/-- Convert a constructive package into the transfer predicate. -/
theorem asymptoticLanguageCollapseTransfer_of_constructive
  (spec : GapPartialMCSPAsymptoticSpec)
  (hC : ConstructiveAsymptoticLanguageCollapseTransfer spec) :
  AsymptoticLanguageCollapseTransfer spec := by
  exact ⟨hC.p, hC.hyp, hC.map⟩

/-- Default-availability flag for a constructive asymptotic transfer. -/
def hasDefaultAsymptoticLanguageCollapseTransfer
  (spec : GapPartialMCSPAsymptoticSpec) : Prop :=
  Nonempty (ConstructiveAsymptoticLanguageCollapseTransfer spec)

/-- Extract the transfer predicate from the default constructive flag. -/
theorem defaultAsymptoticLanguageCollapseTransfer
  (spec : GapPartialMCSPAsymptoticSpec)
  (h : hasDefaultAsymptoticLanguageCollapseTransfer spec) :
  AsymptoticLanguageCollapseTransfer spec := by
  rcases h with ⟨hC⟩
  exact asymptoticLanguageCollapseTransfer_of_constructive spec hC

/--
Any explicit constructive transfer package gives the default-transfer flag.
-/
theorem hasDefaultAsymptoticLanguageCollapseTransfer_of_constructive
  (spec : GapPartialMCSPAsymptoticSpec)
  (hC : ConstructiveAsymptoticLanguageCollapseTransfer spec) :
  hasDefaultAsymptoticLanguageCollapseTransfer spec :=
  ⟨hC⟩

/--
Default-transfer witness from a fixed parameter slice-agreement package.
-/
theorem hasDefaultAsymptoticLanguageCollapseTransfer_of_sliceAgreement
  (spec : GapPartialMCSPAsymptoticSpec)
  (p : GapPartialMCSPParams)
  (hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat))
  (hAgree : AsymptoticLanguageSliceAgreement spec p) :
  hasDefaultAsymptoticLanguageCollapseTransfer spec := by
  refine hasDefaultAsymptoticLanguageCollapseTransfer_of_constructive spec ?_
  refine ⟨p, hHyp, ?_⟩
  exact ppolyFormula_fixed_of_asymptotic_slice spec p hAgree

/--
Provider-based collapse for the asymptotic language, factored through an
explicit transfer to one fixed-size witness language.
-/
theorem collapse_asymptotic_language_of_transfer
  (spec : GapPartialMCSPAsymptoticSpec)
  (hProvider : StructuredLocalityProviderPartial)
  (hTransfer : AsymptoticLanguageCollapseTransfer spec) :
  ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False := by
  intro hPpolyAsym
  rcases hTransfer with ⟨p, hHyp, hMap⟩
  have hPpolyFixed : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
    hMap hPpolyAsym
  obtain ⟨T, loc, hT, hℓ⟩ := hProvider p (1 : Rat) hHyp hPpolyFixed
  exact noSmallLocalCircuitSolver_partial_v2 loc

/--
Asymptotic-language formula separation from:
* strict TM NP-membership witness (`NP_TM` input),
* provider, and
* explicit transfer interface.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_language_with_transfer
  (spec : GapPartialMCSPAsymptoticSpec)
  (hProvider : StructuredLocalityProviderPartial)
  (hTransfer : AsymptoticLanguageCollapseTransfer spec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_of_asymptotic_language
      (spec := spec)
      (hNP_TM := hNP_TM)
      (hCollapse := collapse_asymptotic_language_of_transfer spec hProvider hTransfer)

/--
TM-strict version of the transfer-based asymptotic-language separation.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_language_with_transfer_TM
  (spec : GapPartialMCSPAsymptoticSpec)
  (hProvider : StructuredLocalityProviderPartial)
  (hTransfer : AsymptoticLanguageCollapseTransfer spec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact NP_not_subset_PpolyFormula_of_asymptotic_language_with_transfer
    spec hProvider hTransfer hNP_TM

/--
Direct `P ≠ NP` bridge from an asymptotic-language collapse witness.

This avoids routing through fixed-size parameter packs and gives a
language-level final hook for the asymptotic path.
-/
theorem P_ne_NP_of_asymptotic_language
  (spec : GapPartialMCSPAsymptoticSpec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec))
  (hCollapse :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_of_asymptotic_language
      (spec := spec) (hNP_TM := hNP_TM) (hCollapse := hCollapse)
  have hNPsep : ComplexityInterfaces.NP_not_subset_Ppoly :=
    hFormulaToPpoly hNPFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNPsep ComplexityInterfaces.P_subset_Ppoly_proof

/--
Provider+transfer version of the asymptotic-language `P ≠ NP` bridge.
-/
theorem P_ne_NP_of_asymptotic_language_with_transfer
  (spec : GapPartialMCSPAsymptoticSpec)
  (hProvider : StructuredLocalityProviderPartial)
  (hTransfer : AsymptoticLanguageCollapseTransfer spec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec))
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_of_asymptotic_language_with_transfer
      spec hProvider hTransfer hNP_TM
  have hNPsep : ComplexityInterfaces.NP_not_subset_Ppoly :=
    hFormulaToPpoly hNPFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNPsep ComplexityInterfaces.P_subset_Ppoly_proof

/--
TM-strict provider+transfer version of the asymptotic-language `P ≠ NP` bridge.
-/
theorem P_ne_NP_of_asymptotic_language_with_transfer_TM
  (spec : GapPartialMCSPAsymptoticSpec)
  (hProvider : StructuredLocalityProviderPartial)
  (hTransfer : AsymptoticLanguageCollapseTransfer spec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec))
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_of_asymptotic_language_with_transfer_TM
      spec hProvider hTransfer hNP_TM
  have hNPsep : ComplexityInterfaces.NP_not_subset_Ppoly :=
    hFormulaToPpoly hNPFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNPsep ComplexityInterfaces.P_subset_Ppoly_proof

/--
Default-transfer variant of asymptotic-language formula separation.
-/
theorem NP_not_subset_PpolyFormula_of_asymptotic_language_with_default_transfer
  (spec : GapPartialMCSPAsymptoticSpec)
  (hProvider : StructuredLocalityProviderPartial)
  (hDefaultTransfer : hasDefaultAsymptoticLanguageCollapseTransfer spec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec)) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_of_asymptotic_language_with_transfer
      spec hProvider (defaultAsymptoticLanguageCollapseTransfer spec hDefaultTransfer) hNP_TM

/--
Default-transfer variant of asymptotic-language `P ≠ NP` bridge.
-/
theorem P_ne_NP_of_asymptotic_language_with_default_transfer
  (spec : GapPartialMCSPAsymptoticSpec)
  (hProvider : StructuredLocalityProviderPartial)
  (hDefaultTransfer : hasDefaultAsymptoticLanguageCollapseTransfer spec)
  (hNP_TM : ComplexityInterfaces.NP_TM (gapPartialMCSP_AsymptoticLanguage spec))
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_of_asymptotic_language_with_transfer
      spec hProvider
      (defaultAsymptoticLanguageCollapseTransfer spec hDefaultTransfer)
      hNP_TM
      hFormulaToPpoly

/--
Strict-track final hook: from strict formula separation obtain `P ≠ NP`.
-/
theorem P_ne_NP_of_NP_strict_not_subset_PpolyFormula
  (hStrict : ComplexityInterfaces.NP_strict_not_subset_PpolyFormula)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    ComplexityInterfaces.P_ne_NP_of_NP_strict_not_subset_PpolyFormula
      hStrict hFormulaToPpoly

/--
Strict-track final hook: from strict non-uniform separation obtain `P ≠ NP`.
-/
theorem P_ne_NP_of_NP_strict_not_subset_Ppoly
  (hStrict : ComplexityInterfaces.NP_strict_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    ComplexityInterfaces.P_ne_NP_of_NP_strict_not_subset_Ppoly hStrict

/--
Asymptotic compatibility wrapper for the final `P ≠ NP` bridge.
-/
theorem P_ne_NP_final_of_asymptotic_hypothesis
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
      hProvider hAsym (hNPfam (hAsym.pAt hAsym.N0 (le_rfl)))
  have hNP : ComplexityInterfaces.NP_not_subset_Ppoly :=
    hFormulaToPpoly hNPFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNP ComplexityInterfaces.P_subset_Ppoly_proof

/-- Canonical Partial MCSP parameters used in the final bridge. -/
@[simp] def canonicalPartialParams : GapPartialMCSPParams where
  n := 8
  sYES := 1
  sNO := 3
  gap_ok := by decide
  n_large := by decide
  sYES_pos := by decide
  circuit_bound_ok := by native_decide

/--
Primary final statement (asymptotic entry): from the structured provider and
asymptotic formula-track hypothesis we derive `NP ⊄ PpolyFormula`.

Scope note:
this theorem is a formula-separation endpoint of the AC0-target magnification
route; it is not a standalone global non-uniform separation claim.
-/
theorem NP_not_subset_PpolyFormula_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact NP_not_subset_PpolyFormula_of_asymptotic_hypothesis
    hProvider hAsym (hNPfam (hAsym.pAt hAsym.N0 (le_rfl)))

/--
Primary asymptotic final formula-separation statement.

This default-engine form removes direct provider arguments from the active
final theorem interface.

Scope note:
despite the `PpolyFormula` codomain, this interface is still tied to the AC0
pipeline assumptions (`AsymptoticFormulaTrackHypothesis` + provider packaging).
-/
theorem NP_not_subset_PpolyFormula_final
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/-- Compatibility alias for callers already using the old default-provider name. -/
theorem NP_not_subset_PpolyFormula_final_default_provider
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact NP_not_subset_PpolyFormula_final hDefaultProvider hAsym hNPfam

/--
Final formula-separation wrapper using constructive default multi-switching
asymptotic data plus the default locality provider.

Scope note:
this remains an AC0-side route wrapper and should be reported as such.
-/
theorem NP_not_subset_PpolyFormula_final_of_default_multiSwitching
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis) :
  (hNPfam : StrictGapNPFamily) →
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  intro hNPfam
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider := hDefaultProvider)
      (hAsym := asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS)
      (hNPfam := hNPfam)

/--
AC0-target final theorem with an explicit structured locality provider.

Compared to the default-flag wrappers, this variant is more constructive at
the interface level: no `Nonempty` default provider extraction is used.
-/
theorem NP_not_subset_AC0_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_of_defaultMultiSwitching_hypothesis
      (hProvider := hProvider)
      (hMS := hMS)
      (hNPstrict :=
        hNPfam
          ((asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS).pAt
            (asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS).N0
            (le_rfl)))

/--
AC0-target fixed-parameter theorem without asymptotic packaging.

This is the strict local hook: one concrete `p`, one strict NP witness for
`gapPartialMCSP_Language p`, and one default multi-switching package for
all small AC0 solvers at this same `p`.
-/
theorem NP_not_subset_AC0_at_param_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  have hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat) :=
    formula_hypothesis_from_pipeline_partial_of_default_multiSwitching
      (p := p)
      (δ := (1 : Rat))
      (hδ := zero_lt_one)
      (hMS := hMSp)
  exact
    OPS_trigger_formulas_partial_of_provider_formula_separation
      (hProvider := hProvider)
      (hNPstrict := hNPstrict)
      (p := p)
      (δ := (1 : Rat))
      hHyp

/--
Fixed-parameter AC0 theorem with explicit TM witness for NP-membership.

This removes the separate `hNPstrict` argument by deriving it from
`GapPartialMCSP_TMWitness`.
-/
theorem NP_not_subset_AC0_at_param_with_provider_of_tmWitness
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hW : GapPartialMCSP_TMWitness p)
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_AC0_at_param_with_provider
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := gapPartialMCSP_in_NP_TM_of_witness p hW)
      (hMSp := hMSp)

/--
Engine-based fixed-parameter AC0 theorem.

Same statement as `NP_not_subset_AC0_at_param_with_provider`, but consumes an
explicit constructive locality engine and derives the provider internally.
-/
theorem NP_not_subset_AC0_at_param_of_engine
  (E : ConstructiveLocalityEnginePartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_AC0_at_param_with_provider
      (hProvider := structuredLocalityProviderPartial_of_engine E)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)

/--
Engine-based fixed-parameter AC0 theorem from an explicit TM witness.
-/
theorem NP_not_subset_AC0_at_param_of_engine_of_tmWitness
  (E : ConstructiveLocalityEnginePartial)
  (p : GapPartialMCSPParams)
  (hW : GapPartialMCSP_TMWitness p)
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_AC0_at_param_of_engine
      (E := E)
      (p := p)
      (hNPstrict := gapPartialMCSP_in_NP_TM_of_witness p hW)
      (hMSp := hMSp)

/--
AC0-target final theorem with an explicit constructive locality engine.

This removes default-provider existential packaging from the theorem input by
consuming a concrete `ConstructiveLocalityEnginePartial`.
-/
theorem NP_not_subset_AC0_final_of_engine
  (E : ConstructiveLocalityEnginePartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_AC0_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_engine E)
      (hMS := hMS)
      (hNPfam := hNPfam)

/--
AC0-target asymptotic final theorem from explicit TM witnesses and provider.

This removes `StrictGapNPFamily` from inputs via
`strictGapNPFamily_of_tmWitnesses`.
-/
theorem NP_not_subset_AC0_final_with_provider_of_tmWitnesses
  (hProvider : StructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_AC0_final_with_provider
      (hProvider := hProvider)
      (hMS := hMS)
      (hNPfam := strictGapNPFamily_of_tmWitnesses hW)

/--
AC0-target asymptotic final theorem from explicit TM witnesses and engine.
-/
theorem NP_not_subset_AC0_final_of_engine_of_tmWitnesses
  (E : ConstructiveLocalityEnginePartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hW : ∀ p : GapPartialMCSPParams, GapPartialMCSP_TMWitness p) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_AC0_final_of_engine
      (E := E)
      (hMS := hMS)
      (hNPfam := strictGapNPFamily_of_tmWitnesses hW)

/--
AC0-target final theorem.

This theorem stays inside the AC0 constructive route
(multi-switching/locality) used by `AC0LocalityBridge` and does not require
the old bridge `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.

Scope note:
this is an AC0-route formula-separation endpoint; it is not the global
`P ≠ NP` statement.
-/
theorem NP_not_subset_AC0_final
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_AC0_final_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hMS := hMS)
      (hNPfam := hNPfam)

/--
Automatic provider wiring from the uniform half-size condition.
-/
theorem NP_not_subset_PpolyFormula_final_of_halfSize
  (hHalf : FormulaHalfSizeBoundPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider := hasDefaultStructuredLocalityProviderPartial_of_halfSize hHalf)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Automatic provider wiring from the default half-size flag.
-/
theorem NP_not_subset_PpolyFormula_final_of_default_halfSize
  (hHalf : hasDefaultFormulaHalfSizeBoundPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_default_halfSize hHalf)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring from an explicit formula-certificate package.
-/
theorem NP_not_subset_PpolyFormula_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_formulaCertificate hCert)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring from the default formula-certificate flag.
-/
theorem NP_not_subset_PpolyFormula_final_of_default_formulaCertificate
  (hCert : hasDefaultFormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final_of_formulaCertificate
      (hCert := defaultFormulaCertificateProviderPartial hCert)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring from explicit restriction-level certificate
data.
-/
theorem NP_not_subset_PpolyFormula_final_of_restrictionData
  (D : FormulaRestrictionCertificateDataPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_restrictionData D)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring from default restriction-level certificate data.
-/
theorem NP_not_subset_PpolyFormula_final_of_default_restrictionData
  (hD : hasDefaultFormulaRestrictionCertificateDataPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_default_restrictionData hD)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring from support-based restriction bounds.
-/
theorem NP_not_subset_PpolyFormula_final_of_supportBounds
  (hB : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_supportBounds hB)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Certificate-first provider wiring from default support-bounds flag.
-/
theorem NP_not_subset_PpolyFormula_final_of_default_supportBounds
  (hB : hasDefaultFormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily) :
  ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact
    NP_not_subset_PpolyFormula_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_default_supportBounds hB)
      (hAsym := hAsym)
      (hNPfam := hNPfam)

/--
Compatible final wrapper: deduce `P ≠ NP` from the active formula-track
final statement plus an explicit bridge from formula separation to
lightweight non-uniform separation.

Scope note:
this is a conditional wrapper over the AC0-side formula-separation route; it is
not an unconditional in-repo `P ≠ NP` theorem.
-/
theorem P_ne_NP_final_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_final_with_provider hProvider hAsym hNPfam
  have hNP : ComplexityInterfaces.NP_not_subset_Ppoly :=
    hFormulaToPpoly hNPFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNP ComplexityInterfaces.P_subset_Ppoly_proof

/--
Depth-aware conditional wrapper.

Compared to `P_ne_NP_final_with_provider`, the last bridge to `P/poly`
is required only for the depth-bounded class `PpolyFormulaDepth d`.
We additionally ask for an explicit lifting step from the active formula-track
separation endpoint to this depth-bounded separation statement.
-/
theorem P_ne_NP_final_depth_with_provider
  (d : Nat)
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (formulaLiftToDepth :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
      ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d)
  (formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d →
      ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hNPFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_PpolyFormula_final_with_provider hProvider hAsym hNPfam
  have hNPDepth : ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d :=
    formulaLiftToDepth hNPFormula
  have hNP : ComplexityInterfaces.NP_not_subset_Ppoly :=
    formulaDepthToPpoly hNPDepth
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      hNP ComplexityInterfaces.P_subset_Ppoly_proof

/--
Depth-aware wrapper with canonical lift:
`NP_not_subset_PpolyFormula -> NP_not_subset_PpolyFormulaDepth d`
is taken from `ComplexityInterfaces` automatically.
-/
theorem P_ne_NP_final_depth_with_provider_of_bridge
  (d : Nat)
  (hProvider : StructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d →
      ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_with_provider
      (d := d)
      (hProvider := hProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      (formulaLiftToDepth :=
        ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth_of_NP_not_subset_PpolyFormula)
      (formulaDepthToPpoly := formulaDepthToPpoly)

/--
Single contract that captures all external inputs currently required by the
active final `P ≠ NP` wrapper family.

This keeps the conditional nature of the final claim explicit in one place.
-/
structure ConditionalPneNpFinalContract where
  defaultProvider : hasDefaultStructuredLocalityProviderPartial
  asymptotic : AsymptoticFormulaTrackHypothesis
  npFamily : StrictGapNPFamily
  formulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
      ComplexityInterfaces.NP_not_subset_Ppoly

/--
Depth-aware version of the final conditional contract.

This is the AC0-oriented interface for I-5: the non-uniform bridge is tracked
at fixed depth `d` rather than over unrestricted formulas.
-/
structure ConditionalPneNpDepthFinalContract where
  depth : Nat
  defaultProvider : hasDefaultStructuredLocalityProviderPartial
  asymptotic : AsymptoticFormulaTrackHypothesis
  npFamily : StrictGapNPFamily
  formulaLiftToDepth :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
      ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth depth
  formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth depth →
      ComplexityInterfaces.NP_not_subset_Ppoly

/--
Depth-aware contract with canonical formula-to-depth lift.

Callers only provide the depth-bounded bridge to `P/poly`.
-/
structure ConditionalPneNpDepthBridgeFinalContract where
  depth : Nat
  defaultProvider : hasDefaultStructuredLocalityProviderPartial
  asymptotic : AsymptoticFormulaTrackHypothesis
  npFamily : StrictGapNPFamily
  formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth depth →
      ComplexityInterfaces.NP_not_subset_Ppoly

/--
Contract-based entrypoint for the active conditional final theorem.
-/
theorem P_ne_NP_final_of_contract
  (h : ConditionalPneNpFinalContract) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial h.defaultProvider)
      (hAsym := h.asymptotic)
      (hNPfam := h.npFamily)
      h.formulaToPpoly

/--
Contract-based entrypoint for the depth-aware conditional final theorem.
-/
theorem P_ne_NP_final_of_depth_contract
  (h : ConditionalPneNpDepthFinalContract) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_with_provider
      (d := h.depth)
      (hProvider := defaultStructuredLocalityProviderPartial h.defaultProvider)
      (hAsym := h.asymptotic)
      (hNPfam := h.npFamily)
      (formulaLiftToDepth := h.formulaLiftToDepth)
      (formulaDepthToPpoly := h.formulaDepthToPpoly)

/--
Contract-based entrypoint for the canonical-lift depth-aware theorem.
-/
theorem P_ne_NP_final_of_depth_bridge_contract
  (h : ConditionalPneNpDepthBridgeFinalContract) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_with_provider_of_bridge
      (d := h.depth)
      (hProvider := defaultStructuredLocalityProviderPartial h.defaultProvider)
      (hAsym := h.asymptotic)
      (hNPfam := h.npFamily)
      (formulaDepthToPpoly := h.formulaDepthToPpoly)

/--
Active conditional final `P ≠ NP` wrapper.

This default-engine form removes direct provider arguments from the interface,
but still depends on the explicit bridge `hFormulaToPpoly`.

Scope note:
the route is AC0-centric up to `NP_not_subset_PpolyFormula`; the last step to
`NP_not_subset_Ppoly` is externalized by design.
-/
theorem P_ne_NP_final
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Default-provider depth-aware final wrapper.

This keeps the AC0-side pipeline unchanged and only refines the final bridge
interface to the depth-bounded class `PpolyFormulaDepth d`.
-/
theorem P_ne_NP_final_depth
  (d : Nat)
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (formulaLiftToDepth :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
      ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d)
  (formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d →
      ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_with_provider
      (d := d)
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      (formulaLiftToDepth := formulaLiftToDepth)
      (formulaDepthToPpoly := formulaDepthToPpoly)

/--
Default-provider depth-aware wrapper with canonical formula-to-depth lift.
-/
theorem P_ne_NP_final_depth_of_bridge
  (d : Nat)
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d →
      ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_with_provider_of_bridge
      (d := d)
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      (formulaDepthToPpoly := formulaDepthToPpoly)

/-- Compatibility alias for callers already using the old default-provider name. -/
theorem P_ne_NP_final_default_provider
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact P_ne_NP_final hDefaultProvider hAsym hNPfam hFormulaToPpoly

/--
`P ≠ NP` wrapper through the default multi-switching asymptotic track.
This remains conditional on the explicit formula-to-P/poly bridge.
-/
theorem P_ne_NP_final_of_default_multiSwitching
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider := hDefaultProvider)
      (hAsym := asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS)
      (hNPfam := hNPfam)
      (hFormulaToPpoly := hFormulaToPpoly)

/--
Depth-aware `P ≠ NP` wrapper through the default multi-switching asymptotic
track, with canonical formula-to-depth lift.
-/
theorem P_ne_NP_final_depth_of_default_multiSwitching_bridge
  (d : Nat)
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d →
      ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_of_bridge
      (d := d)
      (hDefaultProvider := hDefaultProvider)
      (hAsym := asymptoticFormulaTrackHypothesis_of_defaultMultiSwitching hMS)
      (hNPfam := hNPfam)
      (formulaDepthToPpoly := formulaDepthToPpoly)

/--
Constructive-bridge variant for the AC0 asymptotic depth route:
consume `Ppoly -> PpolyFormulaDepth d` and derive the separation bridge
internally.
-/
theorem P_ne_NP_final_depth_of_default_multiSwitching_ppolyBridge
  (d : Nat)
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hPpolyToDepth : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth d) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_of_default_multiSwitching_bridge
      (d := d)
      (hDefaultProvider := hDefaultProvider)
      (hMS := hMS)
      (hNPfam := hNPfam)
      (formulaDepthToPpoly :=
        ComplexityInterfaces.NP_not_subset_Ppoly_of_Ppoly_to_PpolyFormulaDepth
          (d := d) hPpolyToDepth)

/--
AC0-oriented final depth contract (asymptotic default multi-switching route).

This packages exactly the remaining external ingredient for I-5 in the AC0
track: the bridge from depth-bounded formula separation to `P/poly` separation.
-/
structure ConditionalPneNpAC0DepthFinalContract where
  depth : Nat
  defaultProvider : hasDefaultStructuredLocalityProviderPartial
  defaultMultiSwitching : AsymptoticDefaultMultiSwitchingHypothesis
  npFamily : StrictGapNPFamily
  formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth depth →
      ComplexityInterfaces.NP_not_subset_Ppoly

/--
Constructive-bridge AC0 asymptotic depth contract:
stores `Ppoly -> PpolyFormulaDepth depth` directly.
-/
structure ConditionalPneNpAC0DepthPpolyBridgeFinalContract where
  depth : Nat
  defaultProvider : hasDefaultStructuredLocalityProviderPartial
  defaultMultiSwitching : AsymptoticDefaultMultiSwitchingHypothesis
  npFamily : StrictGapNPFamily
  ppolyToDepth : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth depth

/--
Contract entrypoint for the AC0-oriented asymptotic depth-aware final theorem.
-/
theorem P_ne_NP_final_AC0_depth_of_contract
  (h : ConditionalPneNpAC0DepthFinalContract) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_of_default_multiSwitching_bridge
      (d := h.depth)
      (hDefaultProvider := h.defaultProvider)
      (hMS := h.defaultMultiSwitching)
      (hNPfam := h.npFamily)
      (formulaDepthToPpoly := h.formulaDepthToPpoly)

/--
Contract entrypoint for the constructive-bridge AC0 asymptotic depth theorem.
-/
theorem P_ne_NP_final_AC0_depth_of_ppolyBridge_contract
  (h : ConditionalPneNpAC0DepthPpolyBridgeFinalContract) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_depth_of_default_multiSwitching_ppolyBridge
      (d := h.depth)
      (hDefaultProvider := h.defaultProvider)
      (hMS := h.defaultMultiSwitching)
      (hNPfam := h.npFamily)
      (hPpolyToDepth := h.ppolyToDepth)

/--
Automatic final `P ≠ NP` wiring from the uniform half-size condition.
-/
theorem P_ne_NP_final_of_halfSize
  (hHalf : FormulaHalfSizeBoundPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider := hasDefaultStructuredLocalityProviderPartial_of_halfSize hHalf)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Fixed-parameter AC0 wrapper to `P ≠ NP` through a depth-bounded bridge.

This uses the local AC0 endpoint (`NP_not_subset_AC0_at_param_with_provider`)
and then applies the canonical formula-to-depth lift.
-/
theorem P_ne_NP_at_param_AC0_depth_with_provider
  (d : Nat)
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d →
      ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  have hFormula : ComplexityInterfaces.NP_not_subset_PpolyFormula :=
    NP_not_subset_AC0_at_param_with_provider
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
  have hDepth : ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d :=
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth_of_NP_not_subset_PpolyFormula hFormula
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      (formulaDepthToPpoly hDepth)
      ComplexityInterfaces.P_subset_Ppoly_proof

/--
Engine-based fixed-parameter AC0 depth-aware `P ≠ NP` wrapper.
-/
theorem P_ne_NP_at_param_AC0_depth_of_engine
  (d : Nat)
  (E : ConstructiveLocalityEnginePartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth d →
      ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_depth_with_provider
      (d := d)
      (hProvider := structuredLocalityProviderPartial_of_engine E)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (formulaDepthToPpoly := formulaDepthToPpoly)

/--
Localized constructive AC0 bridge:
from a `Ppoly -> PpolyFormulaDepth` witness at `gapPartialMCSP_Language p`
(with explicit depth `ac0.d`) derive non-uniform separation at parameter `p`.
-/
theorem NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hBridge : ThirdPartyFacts.GapPartialMCSPPpolyToDepthViaAC0 p) :
  ComplexityInterfaces.NP_not_subset_Ppoly := by
  have hHyp : FormulaLowerBoundHypothesisPartial p (1 : Rat) :=
    formula_hypothesis_from_pipeline_partial_of_default_multiSwitching
      (p := p)
      (δ := (1 : Rat))
      (hδ := zero_lt_one)
      (hMS := hMSp)
  have hContra :
      (∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP_strict L → ComplexityInterfaces.Ppoly L) → False := by
    intro hAll
    have hPpoly : ComplexityInterfaces.Ppoly (gapPartialMCSP_Language p) :=
      hAll _ hNPstrict
    have hDepth :
        ComplexityInterfaces.PpolyFormulaDepth
          (gapPartialMCSP_Language p) hBridge.ac0.d :=
      hBridge.lift hPpoly
    have hFormula :
        ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
      ComplexityInterfaces.PpolyFormula_of_PpolyFormulaDepth hDepth
    obtain ⟨T, loc, hT, hℓ⟩ := hProvider p (1 : Rat) hHyp hFormula
    exact noSmallLocalCircuitSolver_partial_v2 loc
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_NP_strict_not_subset_Ppoly
    (ComplexityInterfaces.NP_strict_not_subset_Ppoly_of_contra hContra)

/--
Engine variant of
`NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider`.
-/
theorem NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_of_engine
  (E : ConstructiveLocalityEnginePartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hBridge : ThirdPartyFacts.GapPartialMCSPPpolyToDepthViaAC0 p) :
  ComplexityInterfaces.NP_not_subset_Ppoly := by
  exact
    NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := structuredLocalityProviderPartial_of_engine E)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hBridge := hBridge)

/--
Localized constructive AC0 bridge to `P ≠ NP` at one parameter `p`.
-/
theorem P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hBridge : ThirdPartyFacts.GapPartialMCSPPpolyToDepthViaAC0 p) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    ComplexityInterfaces.P_ne_NP_of_nonuniform_separation
      (NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider
        (hProvider := hProvider)
        (p := p)
        (hNPstrict := hNPstrict)
        (hMSp := hMSp)
        (hBridge := hBridge))
      ComplexityInterfaces.P_subset_Ppoly_proof

/--
Engine variant of `P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider`.
-/
theorem P_ne_NP_at_param_AC0_of_viaAC0Bridge_of_engine
  (E : ConstructiveLocalityEnginePartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hBridge : ThirdPartyFacts.GapPartialMCSPPpolyToDepthViaAC0 p) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := structuredLocalityProviderPartial_of_engine E)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hBridge := hBridge)

/--
Asymptotic AC0 final wrapper from a localized constructive bridge at the
anchor parameter `hMS.pAt hMS.N0 (le_rfl)`.
-/
theorem P_ne_NP_final_AC0_of_viaAC0Bridge
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hBridge :
    ThirdPartyFacts.GapPartialMCSPPpolyToDepthViaAC0
      (hMS.pAt hMS.N0 (le_rfl))) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := defaultStructuredLocalityProviderPartial hDefaultProvider)
      (p := hMS.pAt hMS.N0 (le_rfl))
      (hNPstrict := hNPfam (hMS.pAt hMS.N0 (le_rfl)))
      (hMSp := hMS.msAt hMS.N0 (le_rfl))
      (hBridge := hBridge)

/--
Reifier-based variant of
`NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider`.
-/
theorem NP_not_subset_Ppoly_at_param_AC0_of_reifier_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hR : ThirdPartyFacts.GapPartialMCSPPpolyDepthReifierViaAC0 p) :
  ComplexityInterfaces.NP_not_subset_Ppoly := by
  exact
    NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hBridge := ThirdPartyFacts.gapPartialMCSP_ppoly_to_depth_viaAC0_of_reifier p hR)

/--
Reifier-based variant of
`P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider`.
-/
theorem P_ne_NP_at_param_AC0_of_reifier_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hR : ThirdPartyFacts.GapPartialMCSPPpolyDepthReifierViaAC0 p) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hBridge := ThirdPartyFacts.gapPartialMCSP_ppoly_to_depth_viaAC0_of_reifier p hR)

/--
Reifier-based asymptotic AC0 final wrapper.
-/
theorem P_ne_NP_final_AC0_of_reifier
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hR :
    ThirdPartyFacts.GapPartialMCSPPpolyDepthReifierViaAC0
      (hMS.pAt hMS.N0 (le_rfl))) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_AC0_of_viaAC0Bridge
      (hDefaultProvider := hDefaultProvider)
      (hMS := hMS)
      (hNPfam := hNPfam)
      (hBridge :=
        ThirdPartyFacts.gapPartialMCSP_ppoly_to_depth_viaAC0_of_reifier
          (hMS.pAt hMS.N0 (le_rfl)) hR)

/--
Default-flag variant of
`NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider`.
-/
theorem NP_not_subset_Ppoly_at_param_AC0_of_default_viaAC0Bridge_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hBridge :
    ThirdPartyFacts.hasDefaultGapPartialMCSPPpolyToDepthViaAC0 p) :
  ComplexityInterfaces.NP_not_subset_Ppoly := by
  exact
    NP_not_subset_Ppoly_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hBridge :=
        ThirdPartyFacts.defaultGapPartialMCSPPpolyToDepthViaAC0 p hBridge)

/--
Default-flag variant of
`P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider`.
-/
theorem P_ne_NP_at_param_AC0_of_default_viaAC0Bridge_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hBridge :
    ThirdPartyFacts.hasDefaultGapPartialMCSPPpolyToDepthViaAC0 p) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hBridge :=
        ThirdPartyFacts.defaultGapPartialMCSPPpolyToDepthViaAC0 p hBridge)

/--
Default-flag variant of `P_ne_NP_final_AC0_of_viaAC0Bridge`.
-/
theorem P_ne_NP_final_AC0_of_default_viaAC0Bridge
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hBridge :
    ThirdPartyFacts.hasDefaultGapPartialMCSPPpolyToDepthViaAC0
      (hMS.pAt hMS.N0 (le_rfl))) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_AC0_of_viaAC0Bridge
      (hDefaultProvider := hDefaultProvider)
      (hMS := hMS)
      (hNPfam := hNPfam)
      (hBridge := ThirdPartyFacts.defaultGapPartialMCSPPpolyToDepthViaAC0
        (hMS.pAt hMS.N0 (le_rfl)) hBridge)

/--
Default-reifier variant of
`P_ne_NP_final_AC0_of_default_viaAC0Bridge`.
-/
theorem P_ne_NP_final_AC0_of_default_reifier
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hR :
    ThirdPartyFacts.hasDefaultGapPartialMCSPPpolyDepthReifierViaAC0
      (hMS.pAt hMS.N0 (le_rfl))) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_AC0_of_reifier
      (hDefaultProvider := hDefaultProvider)
      (hMS := hMS)
      (hNPfam := hNPfam)
      (hR := ThirdPartyFacts.defaultGapPartialMCSPPpolyDepthReifierViaAC0
        (hMS.pAt hMS.N0 (le_rfl)) hR)

/--
Global-depth-bridge variant at one AC0 parameter `p`.

This is a convenience constructor: from a global bridge at depth `ac0.d`
we build the localized `viaAC0` package internally.
-/
theorem P_ne_NP_at_param_AC0_of_global_depth_bridge_with_provider
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (ac0 : ThirdPartyFacts.AC0Parameters)
  (hsame : ac0.n = Models.partialInputLen p)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hGlobal : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth ac0.d) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_of_viaAC0Bridge_with_provider
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hBridge := ThirdPartyFacts.gapPartialMCSP_ppoly_to_depth_viaAC0_of_global_bridge
        p ac0 hsame hGlobal)

/--
Global-depth-bridge variant for the asymptotic AC0 final wrapper at the anchor
parameter `hMS.pAt hMS.N0 (le_rfl)`.
-/
theorem P_ne_NP_final_AC0_of_global_depth_bridge
  (hDefaultProvider : hasDefaultStructuredLocalityProviderPartial)
  (hMS : AsymptoticDefaultMultiSwitchingHypothesis)
  (hNPfam : StrictGapNPFamily)
  (ac0 :
    ThirdPartyFacts.AC0Parameters)
  (hsame :
    ac0.n = Models.partialInputLen (hMS.pAt hMS.N0 (le_rfl)))
  (hGlobal : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth ac0.d) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_AC0_of_viaAC0Bridge
      (hDefaultProvider := hDefaultProvider)
      (hMS := hMS)
      (hNPfam := hNPfam)
      (hBridge := ThirdPartyFacts.gapPartialMCSP_ppoly_to_depth_viaAC0_of_global_bridge
        (hMS.pAt hMS.N0 (le_rfl)) ac0 hsame hGlobal)

/--
Constructive-bridge fixed-parameter AC0 depth wrapper:
consume `Ppoly -> PpolyFormulaDepth d` directly.
-/
theorem P_ne_NP_at_param_AC0_depth_with_provider_of_ppolyBridge
  (d : Nat)
  (hProvider : StructuredLocalityProviderPartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hPpolyToDepth : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth d) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_depth_with_provider
      (d := d)
      (hProvider := hProvider)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (formulaDepthToPpoly :=
        ComplexityInterfaces.NP_not_subset_Ppoly_of_Ppoly_to_PpolyFormulaDepth
          (d := d) hPpolyToDepth)

/--
Constructive-bridge fixed-parameter AC0 depth wrapper via engine.
-/
theorem P_ne_NP_at_param_AC0_depth_of_engine_of_ppolyBridge
  (d : Nat)
  (E : ConstructiveLocalityEnginePartial)
  (p : GapPartialMCSPParams)
  (hNPstrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p))
  (hMSp : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0)
  (hPpolyToDepth : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth d) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_depth_with_provider_of_ppolyBridge
      (d := d)
      (hProvider := structuredLocalityProviderPartial_of_engine E)
      (p := p)
      (hNPstrict := hNPstrict)
      (hMSp := hMSp)
      (hPpolyToDepth := hPpolyToDepth)

/--
AC0 fixed-parameter depth contract.
-/
structure ConditionalPneNpAC0AtParamDepthContract where
  depth : Nat
  provider : StructuredLocalityProviderPartial
  p : GapPartialMCSPParams
  npStrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)
  msAtParam : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0
  formulaDepthToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormulaDepth depth →
      ComplexityInterfaces.NP_not_subset_Ppoly

/--
Constructive-bridge AC0 fixed-parameter depth contract.
-/
structure ConditionalPneNpAC0AtParamDepthPpolyBridgeContract where
  depth : Nat
  provider : StructuredLocalityProviderPartial
  p : GapPartialMCSPParams
  npStrict : ComplexityInterfaces.NP_strict (gapPartialMCSP_Language p)
  msAtParam : ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0
  ppolyToDepth : ComplexityInterfaces.Ppoly_to_PpolyFormulaDepth depth

/--
Contract entrypoint for the AC0 fixed-parameter depth-aware wrapper.
-/
theorem P_ne_NP_at_param_AC0_depth_of_contract
  (h : ConditionalPneNpAC0AtParamDepthContract) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_depth_with_provider
      (d := h.depth)
      (hProvider := h.provider)
      (p := h.p)
      (hNPstrict := h.npStrict)
      (hMSp := h.msAtParam)
      (formulaDepthToPpoly := h.formulaDepthToPpoly)

/--
Contract entrypoint for the constructive-bridge AC0 fixed-parameter theorem.
-/
theorem P_ne_NP_at_param_AC0_depth_of_ppolyBridge_contract
  (h : ConditionalPneNpAC0AtParamDepthPpolyBridgeContract) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_at_param_AC0_depth_with_provider_of_ppolyBridge
      (d := h.depth)
      (hProvider := h.provider)
      (p := h.p)
      (hNPstrict := h.npStrict)
      (hMSp := h.msAtParam)
      (hPpolyToDepth := h.ppolyToDepth)

/--
Automatic final `P ≠ NP` wiring from the default half-size flag.
-/
theorem P_ne_NP_final_of_default_halfSize
  (hHalf : hasDefaultFormulaHalfSizeBoundPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_default_halfSize hHalf)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Certificate-first final `P ≠ NP` wiring from an explicit formula-certificate
package.
-/
theorem P_ne_NP_final_of_formulaCertificate
  (hCert : FormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_formulaCertificate hCert)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Certificate-first final `P ≠ NP` wiring from the default
formula-certificate flag.
-/
theorem P_ne_NP_final_of_default_formulaCertificate
  (hCert : hasDefaultFormulaCertificateProviderPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final_of_formulaCertificate
      (hCert := defaultFormulaCertificateProviderPartial hCert)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Certificate-first final `P ≠ NP` wiring from explicit restriction-level
certificate data.
-/
theorem P_ne_NP_final_of_restrictionData
  (D : FormulaRestrictionCertificateDataPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_restrictionData D)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Certificate-first final `P ≠ NP` wiring from default restriction-level
certificate data.
-/
theorem P_ne_NP_final_of_default_restrictionData
  (hD : hasDefaultFormulaRestrictionCertificateDataPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_default_restrictionData hD)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Certificate-first final `P ≠ NP` wiring from support-based restriction bounds.
-/
theorem P_ne_NP_final_of_supportBounds
  (hB : FormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_supportBounds hB)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

/--
Certificate-first final `P ≠ NP` wiring from default support-bounds flag.
-/
theorem P_ne_NP_final_of_default_supportBounds
  (hB : hasDefaultFormulaSupportRestrictionBoundsPartial)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPfam : StrictGapNPFamily)
  (hFormulaToPpoly :
    ComplexityInterfaces.NP_not_subset_PpolyFormula →
    ComplexityInterfaces.NP_not_subset_Ppoly) :
  ComplexityInterfaces.P_ne_NP := by
  exact
    P_ne_NP_final
      (hDefaultProvider :=
        hasDefaultStructuredLocalityProviderPartial_of_default_supportBounds hB)
      (hAsym := hAsym)
      (hNPfam := hNPfam)
      hFormulaToPpoly

end Magnification
end Pnp3
