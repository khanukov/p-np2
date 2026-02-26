import Magnification.Bridge_to_Magnification_Partial
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
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_formulaCertificate hCert)
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
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_restrictionData D)
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
    NP_not_subset_PpolyFormula_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_supportBounds hB)
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
    P_ne_NP_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_formulaCertificate hCert)
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
    P_ne_NP_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_restrictionData D)
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
    P_ne_NP_final_with_provider
      (hProvider := structuredLocalityProviderPartial_of_supportBounds hB)
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
