import Magnification.FinalResult

/-!
# Weak-route final surface smoke tests

This module is intentionally lightweight: it does not attempt to construct
nontrivial witnesses, but it **does** force Lean to elaborate the exact theorem
types that define the current weak-route final interface.

Rationale:
- when endpoint names or signatures drift during refactors, these declarations
  fail immediately;
- this gives a small, explicit regression surface for the current roadmap:
  accepted-family endpoint, promise-YES endpoint, PRG-image backup, and
  restriction fallback wrappers in `Magnification.FinalResult`.
-/

namespace Pnp3.Tests

open Pnp3
open Pnp3.LowerBounds
open Pnp3.Magnification

/-!
## Type-level interface checks

Each `def` below pins one exported theorem to its current type.
If any theorem is renamed or its argument order/type changes, this file stops
compiling and signals an interface regression.
-/

/-- Surface accepted-family wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_acceptedFamilyStatement :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      SmallDAGImpliesAcceptedFamilyStatement F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_acceptedFamilyStatement

/-- Surface promise-YES statement wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_promiseYesSubcubeStatement :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_promiseYesSubcubeStatement

/-- Surface PRG-image backup wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_prgImageAcceptanceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      prgImageAcceptanceAtProviderOnSlices F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_prgImageAcceptanceProviderOnSlices

/-- Surface wrapper check for distributional easy-image PRG weak route. -/
def check_noSmallDAG_surface_of_easyImagePRGAtProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hEasy : easyImagePRGAtProviderOnSlices F SizeBound)
      (hEpsSmall :
        ∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice
            (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
            (hEasy n β ε W).epsilon <
              1 - ((Models.circuitCountBound (F.paramsOf n β).n
                      ((F.paramsOf n β).sNO - 1) : Rat) /
                    (2 ^ (Models.Partial.tableLen (F.paramsOf n β).n) : Rat))),
      ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_easyImagePRGAtProviderOnSlices

/-- Surface wrapper check for source-level easy-image fooling weak route. -/
def check_noSmallDAG_surface_of_smallDAGEasyImageFoolingSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hSource : smallDAGEasyImageFoolingSourceProviderOnSlices F SizeBound),
      ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_smallDAGEasyImageFoolingSourceProviderOnSlices

/-- Surface wrapper check for minimal canonical distributional source route. -/
def check_noSmallDAG_surface_of_smallDAGEasyDistSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hSource : smallDAGEasyDistSourceProviderOnSlices F SizeBound),
      ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_smallDAGEasyDistSourceProviderOnSlices

/-- Surface wrapper check for one-sided easy-HSG source route. -/
def check_noSmallDAG_surface_of_smallDAGEasyHSGSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hSource : smallDAGEasyHSGSourceProviderOnSlices F SizeBound),
      ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_smallDAGEasyHSGSourceProviderOnSlices

/-- Surface wrapper check for upstream average-case/hardness source route. -/
def check_noSmallDAG_surface_of_smallDAGAverageCaseHardnessSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hAvg : smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound),
      ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_smallDAGAverageCaseHardnessSourceProviderOnSlices

/-- Surface check: renamed source-first `¬ PpolyDAG` weak-route wrapper. -/
def check_not_globalPpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hEasyWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGEasyDistSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute

/-- Surface check: renamed minimal-source weak-route wrapper. -/
def check_not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hEasyWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGEasyDistSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute

/-- Surface check: one-sided easy-HSG weak-route wrapper. -/
def check_not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hEasyHSGWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGEasyHSGSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute

/-- Surface check: avg-hardness weak-route wrapper. -/
def check_not_globalPpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hAvgWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGAverageCaseHardnessSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute

/-- Surface check: renamed source-first `NP_not_subset_PpolyDAG` wrapper. -/
def check_NP_not_subset_PpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hEasyWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGEasyDistSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_smallDAGEasyImageFoolingSourceWeakRoute

/-- Surface check: renamed minimal-source class-level wrapper. -/
def check_NP_not_subset_PpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hEasyWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGEasyDistSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_smallDAGEasyDistSourceWeakRoute

/-- Surface check: one-sided easy-HSG class-level weak-route wrapper. -/
def check_NP_not_subset_PpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hEasyHSGWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGEasyHSGSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_smallDAGEasyHSGSourceWeakRoute

/-- Surface check: avg-hardness class-level wrapper. -/
def check_NP_not_subset_PpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hAvgWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGAverageCaseHardnessSourceProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_smallDAGAvgHardnessSourceWeakRoute

/--
Surface check: canonical easy-density debt -> global non-inclusion wrapper.
-/
def check_not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hCanonical : canonical_smallDAG_easyDensity_source_on_slices F),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt

/--
Surface check: canonical easy-density debt -> `NP_not_subset_PpolyDAG` wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hCanonical : canonical_smallDAG_easyDensity_source_on_slices F),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt

/--
Surface check: witness-indexed canonical easy-density debt -> global
non-inclusion wrapper.
-/
def check_not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hCanonical : canonical_smallDAG_witnessEasyDensity_source_on_slices F),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt

/--
Surface check: witness-indexed canonical easy-density debt ->
`NP_not_subset_PpolyDAG` wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hCanonical : canonical_smallDAG_witnessEasyDensity_source_on_slices F),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessEasyDensitySourceDebt

/--
Surface check: witness-uniform-lower debt -> global non-inclusion wrapper.
-/
def check_not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hUniform : canonical_smallDAG_witnessUniformLower_source_on_slices F),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt

/--
Surface check: witness-uniform-lower debt -> `NP_not_subset_PpolyDAG` wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hUniform : canonical_smallDAG_witnessUniformLower_source_on_slices F),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessUniformLowerSourceDebt

/--
Surface check: quarter-bounded witness-transfer debt -> global non-inclusion.
-/
def check_not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hQuarterTr : canonical_smallDAG_witnessTransferQuarter_source_on_slices F),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt

/--
Surface check: quarter-bounded witness-transfer debt -> `NP_not_subset_PpolyDAG`.
-/
def check_NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (hNP : ComplexityInterfaces.NP bridge.L)
      (hQuarterTr : canonical_smallDAG_witnessTransferQuarter_source_on_slices F),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGWitnessTransferQuarterSourceDebt

/-- Surface alias check for distributional PRG providers on slices. -/
def check_easyImagePRGAtProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      easyImagePRGAtProviderOnSlices F SizeBound → True := by
  intro _ _ _
  trivial

/-- Surface alias check for one-sided transfer providers on slices. -/
def check_easyImageTransferAtProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      easyImageTransferAtProviderOnSlices F SizeBound → True := by
  intro _ _ _
  trivial

/--
Surface check: accepted finite family gives lower bound on uniform acceptance.
-/
def check_dagUniformAcceptanceProbOnTotals_ge_cardRatio_of_family :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε)
      (A : Finset (Core.BitVec (Models.Partial.tableLen p.n))),
      (∀ g ∈ A, witnessAcceptsTotalTable W g = true) →
      ((A.card : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat)) ≤
        dagUniformAcceptanceProbOnTotals W :=
  dagUniformAcceptanceProbOnTotals_ge_cardRatio_of_family

/--
Surface check: YES-subcube certificate gives explicit subcube-ratio lower bound
on uniform acceptance.
-/
def check_dagUniformAcceptanceProbOnTotals_ge_subcubeRatio_of_yesSubcubeCertificateAt :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε)
      (cert : YesSubcubeCertificateAt W),
      ((2 ^ (Models.Partial.tableLen p.n - cert.S.card) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) ≤
          dagUniformAcceptanceProbOnTotals W :=
  dagUniformAcceptanceProbOnTotals_ge_subcubeRatio_of_yesSubcubeCertificateAt

/--
Surface check: YES-subcube certificate numerically separates subcube density
from the counting ratio.
-/
def check_subcubeRatio_gt_countRatio_of_yesSubcubeCertificateAt :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε)
      (cert : YesSubcubeCertificateAt W),
      ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) <
      ((2 ^ (Models.Partial.tableLen p.n - cert.S.card) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) :=
  subcubeRatio_gt_countRatio_of_yesSubcubeCertificateAt

/--
Surface check: YES-subcube certificate yields strict uniform lower bound above
the counting ratio.
-/
def check_dagUniformAcceptanceProbOnTotals_gt_countRatio_of_yesSubcubeCertificateAt :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε)
      (cert : YesSubcubeCertificateAt W),
      ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
        (2 ^ (Models.Partial.tableLen p.n) : Rat)) <
        dagUniformAcceptanceProbOnTotals W :=
  dagUniformAcceptanceProbOnTotals_gt_countRatio_of_yesSubcubeCertificateAt

/--
Surface check: purely quantitative contradiction endpoint for YES-subcube
certificates.
-/
def check_no_small_dag_solver_of_yesSubcubeCertificateAt_via_uniform_counting :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε)
      (cert : YesSubcubeCertificateAt W),
      False :=
  no_small_dag_solver_of_yesSubcubeCertificateAt_via_uniform_counting

/-- Surface alias check for source-level easy-image fooling providers. -/
def check_smallDAGEasyImageFoolingSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      smallDAGEasyImageFoolingSourceProviderOnSlices F SizeBound → True := by
  intro _ _ _
  trivial

/-- Surface alias check for minimal canonical distributional source providers. -/
def check_smallDAGEasyDistSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      smallDAGEasyDistSourceProviderOnSlices F SizeBound → True := by
  intro _ _ _
  trivial

/-- Surface alias check for one-sided easy-HSG source providers. -/
def check_smallDAGEasyHSGSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      smallDAGEasyHSGSourceProviderOnSlices F SizeBound → True := by
  intro _ _ _
  trivial

/-- Surface alias check for canonical easy-density source providers. -/
def check_canonicalSmallDAGEasyDensitySourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      canonicalSmallDAGEasyDensitySourceProviderOnSlices F SizeBound → True := by
  intro _ _ _
  trivial

/-- Surface alias check for avg-hardness source providers. -/
def check_smallDAGAverageCaseHardnessSourceProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound → True := by
  intro _ _ _
  trivial

/-- Surface check: canonical one-`hInDag` source statement alias. -/
def check_CanonicalSmallDAGEasyImageSourceStatement :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β))),
      Type :=
  CanonicalSmallDAGEasyImageSourceStatement

/-- Surface check: canonical avg-hardness statement alias. -/
def check_CanonicalSmallDAGAvgHardnessSourceStatement :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β))),
      Type :=
  CanonicalSmallDAGAvgHardnessSourceStatement

/-- Surface check: canonical easy-HSG statement alias. -/
def check_CanonicalSmallDAGEasyHSGSourceStatement :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β))),
      Type :=
  CanonicalSmallDAGEasyHSGSourceStatement

/-- Surface check: global canonical easy-density debt alias. -/
def check_canonical_smallDAG_easyDensity_source_on_slices :
    ∀ (F : GapSliceFamily), Type :=
  canonical_smallDAG_easyDensity_source_on_slices

/-- Surface check: global witness-indexed canonical easy-density debt alias. -/
def check_canonical_smallDAG_witnessEasyDensity_source_on_slices :
    ∀ (F : GapSliceFamily), Type :=
  canonical_smallDAG_witnessEasyDensity_source_on_slices

/-- Surface check: global witness-uniform-lower debt alias. -/
def check_canonical_smallDAG_witnessUniformLower_source_on_slices :
    ∀ (F : GapSliceFamily), Type :=
  canonical_smallDAG_witnessUniformLower_source_on_slices

/-- Surface check: global witness-transfer-quarter debt alias. -/
def check_canonical_smallDAG_witnessTransferQuarter_source_on_slices :
    ∀ (F : GapSliceFamily), Type :=
  canonical_smallDAG_witnessTransferQuarter_source_on_slices

/-- Surface check: global canonical source debt alias. -/
def check_canonical_smallDAG_easyImage_source_on_slices :
    ∀ (F : GapSliceFamily), Type :=
  canonical_smallDAG_easyImage_source_on_slices

/-- Surface check: global canonical avg-hardness debt alias. -/
def check_canonical_smallDAG_avgHardness_source_on_slices :
    ∀ (F : GapSliceFamily), Type :=
  canonical_smallDAG_avgHardness_source_on_slices

/-- Surface check: global canonical easy-HSG debt alias. -/
def check_canonical_smallDAG_easyHSG_source_on_slices :
    ∀ (F : GapSliceFamily), Type :=
  canonical_smallDAG_easyHSG_source_on_slices

/--
Surface check: global canonical density debt compiles to canonical HSG debt.
-/
def check_canonical_smallDAG_easyHSG_source_on_slices_of_canonical_smallDAG_easyDensity_source_on_slices :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_easyDensity_source_on_slices F →
        canonical_smallDAG_easyHSG_source_on_slices F :=
  canonical_smallDAG_easyHSG_source_on_slices_of_canonical_smallDAG_easyDensity_source_on_slices

/--
Surface check: global canonical HSG debt compiles to canonical density debt
for the current singleton canonical sampler.
-/
def check_canonical_smallDAG_easyDensity_source_on_slices_of_canonical_smallDAG_easyHSG_source_on_slices :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_easyHSG_source_on_slices F →
        canonical_smallDAG_easyDensity_source_on_slices F :=
  canonical_smallDAG_easyDensity_source_on_slices_of_canonical_smallDAG_easyHSG_source_on_slices

/--
Surface check: witness-indexed canonical easy-density debt closes no-small-DAG
at the `ppolyDAG` size bound family.
-/
def check_noSmallDAG_of_canonical_smallDAG_witnessEasyDensity_source_on_slices :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_witnessEasyDensity_source_on_slices F →
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
  noSmallDAG_of_canonical_smallDAG_witnessEasyDensity_source_on_slices

/--
Surface check: witness-uniform-lower debt compiles to witness-indexed canonical
easy-density debt.
-/
def check_canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_witnessUniformLower_source_on_slices F →
      canonical_smallDAG_witnessEasyDensity_source_on_slices F :=
  canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessUniformLower

/--
Surface check: global witness-easy-density debt iff witness-uniform-lower debt.
-/
def check_canonical_smallDAG_witnessEasyDensity_source_on_slices_iff_witnessUniformLower :
    ∀ (F : GapSliceFamily),
      Nonempty (canonical_smallDAG_witnessEasyDensity_source_on_slices F) ↔
        Nonempty (canonical_smallDAG_witnessUniformLower_source_on_slices F) :=
  canonical_smallDAG_witnessEasyDensity_source_on_slices_iff_witnessUniformLower

/--
Surface check: quarter-bounded witness-transfer debt compiles to witness-uniform
lower debt.
-/
def check_canonical_smallDAG_witnessUniformLower_source_on_slices_of_witnessTransferQuarter :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_witnessTransferQuarter_source_on_slices F →
      canonical_smallDAG_witnessUniformLower_source_on_slices F :=
  canonical_smallDAG_witnessUniformLower_source_on_slices_of_witnessTransferQuarter

/--
Surface check: witness-uniform-lower debt compiles to quarter-bounded
witness-transfer debt.
-/
def check_canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_witnessUniformLower :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_witnessUniformLower_source_on_slices F →
      canonical_smallDAG_witnessTransferQuarter_source_on_slices F :=
  canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_witnessUniformLower

/--
Surface check: witness-uniform-lower debt iff quarter-bounded witness-transfer
debt.
-/
def check_canonical_smallDAG_witnessUniformLower_source_on_slices_iff_witnessTransferQuarter :
    ∀ (F : GapSliceFamily),
      Nonempty (canonical_smallDAG_witnessUniformLower_source_on_slices F) ↔
        Nonempty (canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :=
  canonical_smallDAG_witnessUniformLower_source_on_slices_iff_witnessTransferQuarter

/--
Surface check: witness-easy-density debt iff quarter-bounded witness-transfer
debt.
-/
def check_canonical_smallDAG_witnessEasyDensity_source_on_slices_iff_witnessTransferQuarter :
    ∀ (F : GapSliceFamily),
      Nonempty (canonical_smallDAG_witnessEasyDensity_source_on_slices F) ↔
        Nonempty (canonical_smallDAG_witnessTransferQuarter_source_on_slices F) :=
  canonical_smallDAG_witnessEasyDensity_source_on_slices_iff_witnessTransferQuarter

/--
Surface check: quarter-bounded witness-transfer debt compiles to witness-indexed
canonical easy-density debt.
-/
def check_canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessTransferQuarter :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_witnessTransferQuarter_source_on_slices F →
      canonical_smallDAG_witnessEasyDensity_source_on_slices F :=
  canonical_smallDAG_witnessEasyDensity_source_on_slices_of_witnessTransferQuarter

/--
Surface check: quarter-bounded witness-transfer debt closes no-small-DAG at
canonical `ppolyDAG` bounds.
-/
def check_noSmallDAG_of_canonical_smallDAG_witnessTransferQuarter_source_on_slices :
    ∀ (F : GapSliceFamily),
      canonical_smallDAG_witnessTransferQuarter_source_on_slices F →
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        ∀ n : Nat, ∀ β ε : Rat,
          ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
  noSmallDAG_of_canonical_smallDAG_witnessTransferQuarter_source_on_slices

/--
Surface check: distributional PRG endpoint type at one witness.
-/
def check_easyImagePRGAt_surface
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :
    Type :=
  EasyImagePRGAt W

/-- Surface check: source-level easy-image fooling object type. -/
def check_smallDAGEasyImageFoolingSourceAt_surface
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop} :
    Type :=
  SmallDAGEasyImageFoolingSourceAt (p := p) SizeBound

/-- Surface check: minimal canonical distributional source object type. -/
def check_smallDAGEasyDistSourceAt_surface
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop} :
    Type :=
  SmallDAGEasyDistSourceAt (p := p) SizeBound

/-- Surface check: one-sided easy-HSG source object type. -/
def check_smallDAGEasyHSGSourceAt_surface
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop} :
    Type :=
  SmallDAGEasyHSGSourceAt (p := p) SizeBound

/-- Surface check: canonical fixed-sampler easy-HSG source object type. -/
def check_CanonicalSmallDAGEasyHSGSourceAt_surface
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop} :
    Type :=
  CanonicalSmallDAGEasyHSGSourceAt (p := p) SizeBound

/-- Surface check: upstream avg-hardness source object type. -/
def check_smallDAGAverageCaseHardnessSourceAt_surface
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop} :
    Type :=
  SmallDAGAverageCaseHardnessSourceAt (p := p) SizeBound

/-- Surface check: DAG-only evaluator on total tables. -/
def check_dagAcceptsTotalTableOfCircuit
    (p : Models.GapPartialMCSPParams)
    (D : ComplexityInterfaces.DagCircuit (Models.partialInputLen p)) :
    Core.BitVec (Models.Partial.tableLen p.n) → Bool :=
  dagAcceptsTotalTableOfCircuit p D

/-- Surface check: canonical easy-sampler seed length. -/
def check_canonicalEasySamplerSeedLen
    (p : Models.GapPartialMCSPParams) : Nat :=
  canonicalEasySamplerSeedLen p

/-- Surface check: canonical easy sampler function. -/
def check_canonicalEasySampler
    (p : Models.GapPartialMCSPParams) :
    Core.BitVec (canonicalEasySamplerSeedLen p) →
      Core.BitVec (Models.Partial.tableLen p.n) :=
  canonicalEasySampler p

/-- Surface check: canonical sampler YES-support theorem. -/
def check_canonicalEasySampler_supportEasy
    (p : Models.GapPartialMCSPParams) :
    ∀ z, Models.PartialMCSP_YES p (Models.totalTableToPartial (canonicalEasySampler p z)) :=
  canonicalEasySampler_supportEasy p

/-- Surface check: DAG-only uniform acceptance probability. -/
noncomputable def check_dagUniformAcceptanceProbOnTotalsOfCircuit
    (p : Models.GapPartialMCSPParams)
    (D : ComplexityInterfaces.DagCircuit (Models.partialInputLen p)) :
    Rat :=
  dagUniformAcceptanceProbOnTotalsOfCircuit p D

/-- Surface check: DAG-only seed acceptance probability. -/
noncomputable def check_dagSeedAcceptanceProbOnTotalsOfCircuit
    {seedLen : Nat}
    (p : Models.GapPartialMCSPParams)
    (gen : Core.BitVec seedLen → Core.BitVec (Models.Partial.tableLen p.n))
    (D : ComplexityInterfaces.DagCircuit (Models.partialInputLen p)) :
    Rat :=
  dagSeedAcceptanceProbOnTotalsOfCircuit p gen D

/--
Surface check: accepted-image core extractor (without fooling fields).
-/
def check_easyImageCore_of_prgImageAcceptanceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound ε} :
    PRGImageAcceptanceAt W → EasyImageCoreAt W :=
  easyImageCore_of_prgImageAcceptanceAt

/--
Surface check: seed-acceptance ratio equals `1` for `EasyImageCoreAt`.
-/
def check_dagSeedAcceptanceProbOnTotals_eq_one_of_easyImageCoreAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice} :
    (core : EasyImageCoreAt W) →
      dagSeedAcceptanceProbOnTotals W core.gen = 1 :=
  dagSeedAcceptanceProbOnTotals_eq_one_of_easyImageCoreAt

/--
Surface check: lower-transfer theorem for distributional PRG endpoint.
-/
def check_dagUniformAcceptanceProbOnTotals_ge_one_sub_epsilon_of_easyImagePRGAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice} :
    (cert : EasyImagePRGAt W) →
      1 - cert.epsilon ≤ dagUniformAcceptanceProbOnTotals W :=
  dagUniformAcceptanceProbOnTotals_ge_one_sub_epsilon_of_easyImagePRGAt

/--
Surface check: one-shot contradiction theorem for the distributional endpoint.
-/
def check_no_small_dag_solver_of_easyImagePRGAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : EasyImagePRGAt W)
    (_hUpper :
      dagUniformAcceptanceProbOnTotals W < 1 - cert.epsilon) :
    False :=
  no_small_dag_solver_of_easyImagePRGAt W cert _hUpper

/-- Surface check: counting upper bound for witness-uniform acceptance. -/
def check_dagUniformAcceptanceProbOnTotals_le_countRatio_of_correctWitness
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    dagUniformAcceptanceProbOnTotals W ≤
      (Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
      (2 ^ (Models.Partial.tableLen p.n) : Rat) :=
  dagUniformAcceptanceProbOnTotals_le_countRatio_of_correctWitness W

/-- Surface check: counting-closed one-shot contradiction. -/
def check_no_small_dag_solver_of_easyImagePRGAt_of_counting
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (cert : EasyImagePRGAt W)
    (hEpsSmall :
      cert.epsilon <
        1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen p.n) : Rat))) :
    False :=
  no_small_dag_solver_of_easyImagePRGAt_of_counting W cert hEpsSmall

/-- Surface check: counting-closed contradiction for one-sided transfer endpoint. -/
def check_no_small_dag_solver_of_easyImageTransferAt_of_counting
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (tr : EasyImageTransferAt W)
    (hEpsSmall :
      tr.epsilon <
        1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
              (2 ^ (Models.Partial.tableLen p.n) : Rat))) :
    False :=
  no_small_dag_solver_of_easyImageTransferAt_of_counting W tr hEpsSmall

/-- Surface check: source→endpoint compiler is available. -/
def check_easyImagePRGAt_of_smallDAGEasyImageFoolingSourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : SmallDAGEasyImageFoolingSourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImagePRGAt W :=
  easyImagePRGAt_of_smallDAGEasyImageFoolingSourceAt source W

/-- Surface check: minimal-source→endpoint compiler is available. -/
def check_easyImagePRGAt_of_smallDAGEasyDistSourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : SmallDAGEasyDistSourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImagePRGAt W :=
  easyImagePRGAt_of_smallDAGEasyDistSourceAt source W

/-- Surface check: avg-hardness→easy-dist object compiler is available. -/
def check_smallDAGEasyDistSourceAt_of_averageCaseHardnessSourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : SmallDAGAverageCaseHardnessSourceAt (p := p) SizeBound) :
  SmallDAGEasyDistSourceAt (p := p) SizeBound :=
  smallDAGEasyDistSourceAt_of_averageCaseHardnessSourceAt src

/-- Surface check: avg-hardness→easy-HSG object compiler is available. -/
def check_smallDAGEasyHSGSourceAt_of_averageCaseHardnessSourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : SmallDAGAverageCaseHardnessSourceAt (p := p) SizeBound) :
    SmallDAGEasyHSGSourceAt (p := p) SizeBound :=
  smallDAGEasyHSGSourceAt_of_averageCaseHardnessSourceAt src

/-- Surface check: canonical fixed-sampler source→generic easy-HSG compiler. -/
def check_smallDAGEasyHSGSourceAt_of_canonicalEasyHSGSourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalSmallDAGEasyHSGSourceAt (p := p) SizeBound) :
    SmallDAGEasyHSGSourceAt (p := p) SizeBound :=
  smallDAGEasyHSGSourceAt_of_canonicalEasyHSGSourceAt src

/-- Surface check: canonical density→canonical easy-HSG compiler. -/
def check_canonicalEasyHSGSourceAt_of_canonicalEasyDensitySourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalSmallDAGEasyDensitySourceAt (p := p) SizeBound) :
    CanonicalSmallDAGEasyHSGSourceAt (p := p) SizeBound :=
  canonicalEasyHSGSourceAt_of_canonicalEasyDensitySourceAt src

/--
Surface check: canonical easy-HSG→canonical density compiler (singleton
canonical sampler) is available.
-/
def check_canonicalEasyDensitySourceAt_of_canonicalEasyHSGSourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalSmallDAGEasyHSGSourceAt (p := p) SizeBound) :
    CanonicalSmallDAGEasyDensitySourceAt (p := p) SizeBound :=
  canonicalEasyDensitySourceAt_of_canonicalEasyHSGSourceAt src

/-- Surface check: one-sided source→transfer endpoint compiler is available. -/
def check_easyImageTransferAt_of_smallDAGEasyHSGSourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : SmallDAGEasyHSGSourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImageTransferAt W :=
  easyImageTransferAt_of_smallDAGEasyHSGSourceAt source W

/-- Surface check: canonical density→transfer endpoint compiler is available. -/
def check_easyImageTransferAt_of_canonicalEasyDensitySourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : CanonicalSmallDAGEasyDensitySourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImageTransferAt W :=
  easyImageTransferAt_of_canonicalEasyDensitySourceAt source W

/-- Surface check: canonical easy family object is available. -/
noncomputable def check_canonicalEasyFamilyFinset
    (p : Models.GapPartialMCSPParams) :
    Finset (Core.BitVec (Models.Partial.tableLen p.n)) :=
  canonicalEasyFamilyFinset p

/-- Surface check: canonical easy family support lemma is available. -/
def check_canonicalEasyFamily_supportEasy
    (p : Models.GapPartialMCSPParams) :
    ∀ t ∈ canonicalEasyFamilyFinset p,
      Models.PartialMCSP_YES p (Models.totalTableToPartial t) :=
  canonicalEasyFamily_supportEasy p

/-- Surface check: pattern-realization predicate on canonical easy family. -/
def check_canonicalEasyFamilyRealizesPatternOn
    (p : Models.GapPartialMCSPParams)
    (S : Finset (Fin (Models.Partial.tableLen p.n)))
    (σ : Fin (Models.Partial.tableLen p.n) → Bool) : Prop :=
  canonicalEasyFamilyRealizesPatternOn p S σ

/-- Surface check: all-patterns-up-to-budget canonical coverage contract. -/
def check_canonicalEasyFamilyRealizesAllPatternsUpTo
    (p : Models.GapPartialMCSPParams)
    (hardwireBudget : Nat) : Prop :=
  canonicalEasyFamilyRealizesAllPatternsUpTo p hardwireBudget

/-- Surface check: explicit coarse hardwire size budget function. -/
def check_hardwireCircuitSize (n k : Nat) : Nat :=
  hardwireCircuitSize n k

/-- Surface check: coverage theorem from hardwire budget is exposed. -/
theorem check_canonicalEasyFamilyRealizesAllPatternsUpTo_of_hardwireCircuitBound
    (p : Models.GapPartialMCSPParams)
    (hardwireBudget : Nat)
    (hSize : hardwireCircuitSize p.n hardwireBudget < p.sYES) :
    canonicalEasyFamilyRealizesAllPatternsUpTo p hardwireBudget :=
  canonicalEasyFamilyRealizesAllPatternsUpTo_of_hardwireCircuitBound p hardwireBudget hSize

/-- Surface check: canonical value-only alive set extracted from restriction extraction. -/
def check_canonicalValueAliveSet
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (E : SmallDAGWitnessRestrictionExtractionAt W) :
    Finset (Fin (Models.Partial.tableLen p.n)) :=
  canonicalValueAliveSet E

/-- Surface check: extraction implies stability on the canonical value-alive set. -/
theorem check_stableOn_canonicalValueAliveSet_of_extraction
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (E : SmallDAGWitnessRestrictionExtractionAt W) :
    ∀ x y : Core.BitVec (Models.Partial.tableLen p.n),
      (∀ j ∈ canonicalValueAliveSet E, x j = y j) →
      dagAcceptsTotalTableOfCircuit p W.C y =
        dagAcceptsTotalTableOfCircuit p W.C x :=
  stableOn_canonicalValueAliveSet_of_extraction E

/-- Surface check: canonical value-alive set inherits extraction alive bound. -/
theorem check_canonicalValueAliveSet_card_le_aliveBound
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    {W : SmallDAGWitnessOnSlice p SizeBound εslice}
    (E : SmallDAGWitnessRestrictionExtractionAt W) :
    (canonicalValueAliveSet E).card ≤ E.aliveBound :=
  canonicalValueAliveSet_card_le_aliveBound E

/-- Surface check: canonical-family reject-density observable is available. -/
noncomputable def check_canonicalEasyRejectProbOnFamilyOfCircuit
    (p : Models.GapPartialMCSPParams)
    (D : ComplexityInterfaces.DagCircuit (Models.partialInputLen p)) : Rat :=
  canonicalEasyRejectProbOnFamilyOfCircuit p D

/--
Surface check: one rejected canonical-family point yields positive density lower
bound `1 / 2^tableLen`.
-/
theorem check_canonicalEasyRejectProbOnFamilyOfCircuit_ge_one_div_twoPow_of_exists_reject
    {p : Models.GapPartialMCSPParams}
    (D : ComplexityInterfaces.DagCircuit (Models.partialInputLen p))
    (hReject :
      ∃ t ∈ canonicalEasyFamilyFinset p,
        dagAcceptsTotalTableOfCircuit p D t = false) :
    (1 : Rat) / (2 ^ (Models.Partial.tableLen p.n) : Rat) ≤
      canonicalEasyRejectProbOnFamilyOfCircuit p D :=
  canonicalEasyRejectProbOnFamilyOfCircuit_ge_one_div_twoPow_of_exists_reject D hReject

/-- Surface check: `uniform < 1` implies existence of a rejected total table. -/
theorem check_exists_reject_of_uniformAcceptanceProbOnTotals_lt_one
    {p : Models.GapPartialMCSPParams}
    (D : ComplexityInterfaces.DagCircuit (Models.partialInputLen p))
    (hLtOne : dagUniformAcceptanceProbOnTotalsOfCircuit p D < 1) :
    ∃ t : Core.BitVec (Models.Partial.tableLen p.n),
      dagAcceptsTotalTableOfCircuit p D t = false :=
  exists_reject_of_uniformAcceptanceProbOnTotals_lt_one D hLtOne

/-- Surface check: witness-indexed canonical-density source→transfer compiler. -/
def check_easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (source : CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImageTransferAt W :=
  easyImageTransferAt_of_canonicalWitnessEasyDensitySourceAt source W

/--
Surface check: witness-density target statement is exposed in direct
low-uniform → canonical-family-reject-density form.
-/
def check_canonicalWitnessEasyDensity_lowUniform_implies_familyRejectDensity
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (src : CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound)
    {εslice : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound εslice)
    (hUniformLow : dagUniformAcceptanceProbOnTotals W < 1 - src.epsilon) :
    src.delta ≤ canonicalEasyRejectProbOnFamily W :=
  canonicalWitnessEasyDensity_lowUniform_implies_familyRejectDensity src W hUniformLow

/--
Surface check: central bridge constructor from
restriction/local-dependence+coverage to witness family-density source.
-/
def check_canonicalWitnessEasyDensitySourceAt_of_restrictionExtractionAndCoverage
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (SOf :
      ∀ {εslice : Rat},
        SmallDAGWitnessOnSlice p SizeBound εslice →
          Finset (Fin (Models.Partial.tableLen p.n)))
    (hBudget :
      ∀ {εslice : Rat}
        (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (SOf W).card ≤ hardwireBudget)
    (hCover :
      canonicalEasyFamilyRealizesAllPatternsUpTo p hardwireBudget)
    (hStableOnS :
      ∀ {εslice : Rat}
        (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        ∀ x y : Core.BitVec (Models.Partial.tableLen p.n),
          (∀ i ∈ SOf W, x i = y i) →
            dagAcceptsTotalTableOfCircuit p W.C y =
              dagAcceptsTotalTableOfCircuit p W.C x)
    : CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound :=
  canonicalWitnessEasyDensitySourceAt_of_restrictionExtractionAndCoverage
    epsilon hEpsQuarter hEpsNonneg hardwireBudget SOf hBudget hCover hStableOnS

/--
Surface check: normalized bridge constructor with canonical extracted coordinate
set and derived stability.
-/
def check_canonicalWitnessEasyDensitySourceAt_of_extractionBudgetAndCoverage
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (hExtract :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        SmallDAGWitnessRestrictionExtractionAt W)
    (hBudget :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (canonicalValueAliveSet (hExtract W)).card ≤ hardwireBudget)
    (hCover :
      canonicalEasyFamilyRealizesAllPatternsUpTo p hardwireBudget) :
    CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound :=
  canonicalWitnessEasyDensitySourceAt_of_extractionBudgetAndCoverage
    epsilon hEpsQuarter hEpsNonneg hardwireBudget hExtract hBudget hCover

/-- Surface check: final normalized bridge (coverage discharged from budget). -/
def check_canonicalWitnessEasyDensitySourceAt_of_extractionBudget
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (hCoverBudget :
      hardwireCircuitSize p.n hardwireBudget < p.sYES)
    (hExtract :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        SmallDAGWitnessRestrictionExtractionAt W)
    (hBudget :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (canonicalValueAliveSet (hExtract W)).card ≤ hardwireBudget) :
    CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound :=
  canonicalWitnessEasyDensitySourceAt_of_extractionBudget
    epsilon hEpsQuarter hEpsNonneg hardwireBudget hCoverBudget hExtract hBudget

/-- Surface check: support-specialized normalized bridge is available. -/
noncomputable def check_canonicalWitnessEasyDensitySourceAt_of_supportBudget
    {p : Models.GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    (epsilon : Rat)
    (hEpsQuarter : epsilon ≤ (1 / 4 : Rat))
    (hEpsNonneg : 0 ≤ epsilon)
    (hardwireBudget : Nat)
    (hCoverBudget : hardwireCircuitSize p.n hardwireBudget < p.sYES)
    (hSupportBudget :
      ∀ {εslice : Rat} (W : SmallDAGWitnessOnSlice p SizeBound εslice),
        (ComplexityInterfaces.DagCircuit.support W.C).card ≤ hardwireBudget) :
    CanonicalWitnessEasyDensitySourceAt (p := p) SizeBound :=
  canonicalWitnessEasyDensitySourceAt_of_supportBudget
    epsilon hEpsQuarter hEpsNonneg hardwireBudget hCoverBudget hSupportBudget

/-- Surface check: provider-level avg-hardness→easy-dist compiler is available. -/
def check_smallDAGEasyDistSourceProviderOnSlices_of_avgHardnessSource
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) :
    smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound →
      smallDAGEasyDistSourceProviderOnSlices F SizeBound :=
  smallDAGEasyDistSourceProviderOnSlices_of_avgHardnessSource F SizeBound

/-- Surface check: one-sided source→transfer provider compiler is available. -/
def check_easyImageTransferAtProviderOnSlices_of_smallDAGEasyHSGSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) :
    smallDAGEasyHSGSourceProviderOnSlices F SizeBound →
      easyImageTransferAtProviderOnSlices F SizeBound :=
  easyImageTransferAtProviderOnSlices_of_smallDAGEasyHSGSourceProviderOnSlices F SizeBound

/--
Surface check: canonical fixed-sampler provider→generic easy-HSG provider
compiler is available.
-/
def check_smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyHSGSourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) :
    (∀ n : Nat, ∀ β : Rat,
      CanonicalSmallDAGEasyHSGSourceAt
        (p := F.paramsOf n β) (fun ε' s => SizeBound n β ε' s)) →
      smallDAGEasyHSGSourceProviderOnSlices F SizeBound :=
  smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyHSGSourceProviderOnSlices
    F SizeBound

/--
Surface check: canonical easy-density provider→generic one-sided easy-HSG
provider compiler is available.
-/
def check_smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyDensitySourceProviderOnSlices
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) :
    canonicalSmallDAGEasyDensitySourceProviderOnSlices F SizeBound →
      smallDAGEasyHSGSourceProviderOnSlices F SizeBound :=
  smallDAGEasyHSGSourceProviderOnSlices_of_canonicalEasyDensitySourceProviderOnSlices
    F SizeBound

/-- Surface check: provider-level avg-hardness→easy-HSG compiler is available. -/
def check_smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) :
    smallDAGAverageCaseHardnessSourceProviderOnSlices F SizeBound →
      smallDAGEasyHSGSourceProviderOnSlices F SizeBound :=
  smallDAGEasyHSGSourceProviderOnSlices_of_avgHardnessSource F SizeBound

/-- Surface check: quarter slack from `circuit_bound_ok`. -/
def check_quarter_lt_one_sub_countRatio_of_circuit_bound_ok
    (p : Models.GapPartialMCSPParams) :
    (1 / 4 : Rat) <
      1 - ((Models.circuitCountBound p.n (p.sNO - 1) : Rat) /
            (2 ^ (Models.Partial.tableLen p.n) : Rat)) :=
  quarter_lt_one_sub_countRatio_of_circuit_bound_ok p

/-- Surface restriction-fallback wrapper is available with the expected type. -/
def check_noSmallDAG_surface_of_restrictionFallbackOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hExtract : smallDAGWitnessRestrictionExtractionProviderOnSlices F SizeBound),
      smallDAGWitnessRestrictionNumericDataProviderOnSlices F SizeBound hExtract →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_surface_of_restrictionFallbackOnSlices

/--
Technical source-level reduction from pairwise promise/value packages to the
mainline promise-YES statement remains in the lower-bounds producer layer
(not in `Magnification.FinalResult`).
-/
def check_smallDAGPromiseYesSubcubeStatement_of_packageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound →
        SmallDAGImpliesPromiseYesSubcubeStatement F SizeBound :=
  smallDAGPromiseYesSubcubeStatement_of_packageProvider

/--
Gate-G1 Route-B item (3) wrapper is available with the expected type:
a DAG-native certificate provider compiles directly to the canonical
stable-restriction goal family over `dagCanonicalPayload`.
-/
def check_gateG1_routeB_stableRestrictionGoal_of_certificateProvider :
    ∀ {p : Models.GapPartialMCSPParams}
      (_hCert : dagStableRestrictionCertificateProvider p),
      ∀ hDag : ComplexityInterfaces.PpolyDAG (Models.gapPartialMCSP_Language p),
        stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag) :=
  gateG1_routeB_stableRestrictionGoal_of_certificateProvider

/--
Q1/Q2 split-provider compilation to promise-YES certificate provider is
available with the expected type.
-/
def check_promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound),
      promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv →
        (∀ n : Nat, ∀ β ε : Rat,
          ∀ W : SmallDAGWitnessOnSlice (F.paramsOf n β) (fun ε' s => SizeBound n β ε' s) ε,
            PromiseYesSubcubeCertificateAt W) :=
  promiseYesSubcubeCertificateAtProviderOnSlices_of_semanticAndSlackProvider

/-- Q1/Q2 split-provider no-small-DAG closure is available with the expected type. -/
def check_noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound),
      promiseYesSlackOnInvariantProviderOnSlices F SizeBound hInv →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices

/--
Q1 semantic provider + required-budget provider compiles directly to no-small-DAG
with the expected type.
-/
def check_noSmallDAG_of_promiseYesRequiredBudgetProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hInv : promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound),
      promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound hInv →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_promiseYesRequiredBudgetProviderOnSlices

/--
Strict-semantics specialization of the required-budget closure is available with
the expected type.
-/
def check_noSmallDAG_of_strictSemanticsAndRequiredBudgetProviderOnSlices :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (_hBudget :
        promiseYesRequiredBudgetOnInvariantProviderOnSlices F SizeBound
          (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
            F SizeBound)),
      ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_strictSemanticsAndRequiredBudgetProviderOnSlices

/--
Canonical-surface strict-mainline blocker is available with the expected type:
at any concrete solver index, strict required-budget provider is impossible.
-/
def check_not_strictRequiredBudgetProvider_onCanonicalBound_of_smallDAGSolver :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)))
      (n : Nat) (β ε : Rat),
      SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε →
        ¬ promiseYesRequiredBudgetOnInvariantProviderOnSlices
            F
            (ppolyDAGSizeBoundOnSlices F hInDag)
            (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
              F (ppolyDAGSizeBoundOnSlices F hInDag)) :=
  not_strictRequiredBudgetProvider_onCanonicalBound_of_smallDAGSolver

/--
Pointwise contradiction wrapper for strict canonical required-budget route is
available with expected type.
-/
def check_false_of_smallDAGSolver_and_strictRequiredBudgetProvider_onCanonicalBound :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)))
      (n : Nat) (β ε : Rat),
      SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε →
      promiseYesRequiredBudgetOnInvariantProviderOnSlices
        F
        (ppolyDAGSizeBoundOnSlices F hInDag)
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics
          F (ppolyDAGSizeBoundOnSlices F hInDag)) →
        False :=
  false_of_smallDAGSolver_and_strictRequiredBudgetProvider_onCanonicalBound

/--
Package-provider -> Q1 semantic-provider reduction is available with the
expected type.
-/
noncomputable def check_promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound →
        promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound :=
  promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider

/--
Strict-DAG-semantics witness-level Q1 constructor is available with the expected
type.
-/
def check_promiseYesAcceptanceInvariantAt_of_strictDAGSemantics :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      PromiseYesAcceptanceInvariantAt W :=
  promiseYesAcceptanceInvariantAt_of_strictDAGSemantics

/--
Strict-DAG-semantics family-level Q1 provider is available with the expected
type.
-/
def check_promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseYesAcceptanceInvariantAtProviderOnSlices F SizeBound :=
  promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics

/--
Route-B source constructor from a concrete strict DAG witness plus support-half
bound is available with expected type.
-/
noncomputable def check_dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf :
    ∀ {p : Models.GapPartialMCSPParams}
      (w : ComplexityInterfaces.InPpolyDAG (Models.gapPartialMCSP_Language p))
      (_hHalf :
        (ComplexityInterfaces.DagCircuit.support (w.family (Models.partialInputLen p))).card ≤
          Models.Partial.tableLen p.n / 2),
      DAGStableRestrictionInvariantPackage
        (show ComplexityInterfaces.PpolyDAG (Models.gapPartialMCSP_Language p) from ⟨w, trivial⟩) :=
  dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf

/--
Route-B Task-1 reduction theorem is available with expected type:
uniform strict-witness support-half bounds imply the invariant provider.
-/
noncomputable def check_dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf :
    ∀ {p : Models.GapPartialMCSPParams}
      (_hSupportHalf :
        ∀ w : ComplexityInterfaces.InPpolyDAG (Models.gapPartialMCSP_Language p),
          (ComplexityInterfaces.DagCircuit.support (w.family (Models.partialInputLen p))).card ≤
            Models.Partial.tableLen p.n / 2),
      dagStableRestrictionInvariantProvider p :=
  dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf

/--
Localized Route-B blocker alias is exposed with the expected type.
-/
def check_dagRouteBSourceBlocker :
    Models.GapPartialMCSPParams → Prop :=
  dagRouteBSourceBlocker

/--
Localized Route-B closure package is exposed with the expected type.
-/
def check_DAGRouteBSourceClosure :
    Models.GapPartialMCSPParams → Type :=
  DAGRouteBSourceClosure

/--
Canonical constructor from the localized blocker to closure package is
available with the expected type.
-/
noncomputable def check_dagRouteBSourceClosure_of_blocker :
    ∀ {p : Models.GapPartialMCSPParams},
      dagRouteBSourceBlocker p → DAGRouteBSourceClosure p :=
  dagRouteBSourceClosure_of_blocker

/--
One-way nonempty closure packaging from the named Route-B blocker is available
with the expected type.
-/
theorem check_nonempty_sourceClosure_of_dagRouteBSourceBlocker :
    ∀ {p : Models.GapPartialMCSPParams},
      dagRouteBSourceBlocker p → Nonempty (DAGRouteBSourceClosure p) :=
  nonempty_sourceClosure_of_dagRouteBSourceBlocker

/--
Final wrapper from localized Route-B closure to DAG separation is available with
the expected type.
-/
def check_NP_not_subset_PpolyDAG_final_of_sourceClosure_TM :
    ∀ {p : Models.GapPartialMCSPParams},
      Models.GapPartialMCSP_TMWitness p →
      DAGRouteBSourceClosure p →
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_final_of_sourceClosure_TM

/--
Companion `P ≠ NP` final wrapper for the same localized source closure is
available with the expected type.
-/
def check_P_ne_NP_final_of_sourceClosure_TM :
    ∀ {p : Models.GapPartialMCSPParams},
      Models.GapPartialMCSP_TMWitness p →
      DAGRouteBSourceClosure p →
      ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_final_of_sourceClosure_TM

/--
Direct final DAG-separation wrapper from the named Route-B blocker is available
with the expected type.
-/
def check_NP_not_subset_PpolyDAG_final_of_blocker_TM :
    ∀ {p : Models.GapPartialMCSPParams},
      Models.GapPartialMCSP_TMWitness p →
      dagRouteBSourceBlocker p →
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_final_of_blocker_TM

/--
Companion direct `P ≠ NP` wrapper from the same Route-B blocker gate is
available with the expected type.
-/
def check_P_ne_NP_final_of_blocker_TM :
    ∀ {p : Models.GapPartialMCSPParams},
      Models.GapPartialMCSP_TMWitness p →
      dagRouteBSourceBlocker p →
      ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_final_of_blocker_TM

/--
Branch-A strengthened provider target (nontrivial `S`) is exposed with the
expected type.
-/
def check_promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices :
    (GapSliceFamily → (Nat → Rat → Rat → Nat → Prop) → Type) :=
  promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices

/--
Alternative positive-source route package with formula-track export hooks is
available with the expected type.
-/
def check_NontrivialSAlternativeProducerRoute :
    Type :=
  NontrivialSAlternativeProducerRoute

/--
Projection to `FormulaSupportRestrictionBoundsPartial` is available with the
expected type.
-/
def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSAlternativeProducerRoute :
    NontrivialSAlternativeProducerRoute →
      Magnification.FormulaSupportRestrictionBoundsPartial :=
  formulaSupportRestrictionBoundsPartial_of_nontrivialSAlternativeProducerRoute

/--
Projection to `FormulaRestrictionCertificateDataPartial` is available with the
expected type.
-/
noncomputable def check_formulaRestrictionCertificateDataPartial_of_nontrivialSAlternativeProducerRoute :
    NontrivialSAlternativeProducerRoute →
      Magnification.FormulaRestrictionCertificateDataPartial :=
  formulaRestrictionCertificateDataPartial_of_nontrivialSAlternativeProducerRoute

/--
First concrete inhabitant builder for the alternative route package is available
with the expected type.
-/
noncomputable def check_nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.FormulaSupportRestrictionBoundsPartial →
      NontrivialSAlternativeProducerRoute :=
  nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds

/--
Class-shaped export theorem to `FormulaSupportRestrictionBoundsPartial` is
available with the expected type.
-/
noncomputable def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.FormulaSupportRestrictionBoundsPartial →
      Magnification.FormulaSupportRestrictionBoundsPartial :=
  formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andSupportBounds

/--
I-2 ladder theorem from the same class-shaped source is available with the
expected type.
-/
noncomputable def check_hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.FormulaSupportRestrictionBoundsPartial →
      Magnification.hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andSupportBounds

/--
Support-bounds closure from non-full-`S` slice source plus multi-switching
contract is available with the expected type.
-/
noncomputable def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andMultiswitching :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract →
      Magnification.FormulaSupportRestrictionBoundsPartial :=
  formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andMultiswitching

/--
I-2 default structured-provider closure from the same assumptions is available
with the expected type.
-/
noncomputable def check_hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andMultiswitching :
    (∀ (F : GapSliceFamily) (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound) →
    Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract →
      Magnification.hasDefaultStructuredLocalityProviderPartial :=
  hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andMultiswitching

/--
Current strict-Q1 route explicitly pins `S = Finset.univ`.
-/
def check_strictDAGSemantics_S_eq_univ :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S = Finset.univ :=
  strictDAGSemantics_S_eq_univ

/--
Current strict-Q1 route cannot satisfy the Branch-A nontrivial-`S` target.
-/
def check_no_nontrivialS_acceptanceInvariant_of_strictDAGSemantics :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      ((promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S ≠ Finset.univ) → False :=
  strictDAGSemantics_nontrivialS_false

/--
N2 impossibility theorem for the current strict-semantics Q1 set choice is
available with the expected type.
-/
def check_no_sameSetSlack_of_strictDAGSemantics :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      (W : SmallDAGWitnessOnSlice p SizeBound ε),
      ¬ Models.circuitCountBound p.n (p.sNO - 1) <
          2 ^ (Models.Partial.tableLen p.n - (promiseYesAcceptanceInvariantAt_of_strictDAGSemantics W).S.card) :=
  no_sameSetSlack_of_strictDAGSemantics

/--
Branch-C quantitative nontriviality from promise/value packages is available.
-/
def check_nontrivialS_of_promiseValueLocalityPackageAt :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      {W : SmallDAGWitnessOnSlice p SizeBound ε}
      (cert : PromiseValueLocalityPackageAt W),
      cert.S ≠ Finset.univ :=
  nontrivialS_of_promiseValueLocalityPackageAt

/--
Branch-C witness-level bridge to nontrivial-Q1 invariant is available.
-/
noncomputable def check_promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt :
    ∀ {p : Models.GapPartialMCSPParams}
      {SizeBound : Rat → Nat → Prop}
      {ε : Rat}
      {W : SmallDAGWitnessOnSlice p SizeBound ε}
      (_cert : PromiseValueLocalityPackageAt W),
      PromiseYesAcceptanceInvariantAtNontrivialS W :=
  promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt

/--
Branch-C provider-level bridge to nontrivial-Q1 invariants is available.
-/
noncomputable def
    check_promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices_of_promiseValueLocalityPackageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (_hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound),
      promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices F SizeBound :=
  promiseYesAcceptanceInvariantAtNontrivialSProviderOnSlices_of_promiseValueLocalityPackageProvider

/--
Package-provider -> Q2 slack-provider reduction is available with the expected
dependent-provider type.
-/
noncomputable def check_promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (hPkg : promiseValueLocalityPackageAtProviderOnSlices F SizeBound),
      promiseYesSlackOnInvariantProviderOnSlices
        F SizeBound
        (promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider
          F SizeBound hPkg) :=
  promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider

/--
Package-provider closure through split Q1/Q2 interface is available with the
expected type.
-/
noncomputable def check_noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices_viaSemanticAndSlack :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop),
      promiseValueLocalityPackageAtProviderOnSlices F SizeBound →
        ∀ n : Nat, ∀ β ε : Rat, ¬ SmallDAGSolver F SizeBound n β ε :=
  noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices_viaSemanticAndSlack

/-- Asymptotic eventual accepted-family surface wrapper is available. -/
def check_magnificationStyleNoSmallDAG_surface_of_eventuallyAcceptedFamily :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      (∀ β : Rat, 0 < β → β < β0 →
        ∃ nAcc : Nat, ∀ n ≥ nAcc, SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε) →
      MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound) :=
  magnificationStyleNoSmallDAG_surface_of_eventuallyAcceptedFamily

/-- Asymptotic eventual promise-YES surface wrapper is available. -/
def check_magnificationStyleNoSmallDAG_surface_of_eventuallyPromiseYesSubcube :
    ∀ (F : GapSliceFamily)
      (SizeBound : Nat → Rat → Rat → Nat → Prop)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      (∀ β : Rat, 0 < β → β < β0 →
        ∃ nYes : Nat, ∀ n ≥ nYes, SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε) →
      MagnificationStyleNoSmallDAG (SmallDAGSolver F SizeBound) :=
  magnificationStyleNoSmallDAG_surface_of_eventuallyPromiseYesSubcube

/--
Q3 bridge skeleton (witness-level): slice-indexed strict `InPpolyDAG` witnesses
compile into explicit `SmallDAGSolver` witnesses for all `(n,β,ε)`.
-/
def check_smallDAGSolver_of_inPpolyDAGFamilyOnSlices :
    ∀ (F : GapSliceFamily)
      (hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β))),
      ∀ n : Nat, ∀ β ε : Rat,
        SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
  smallDAGSolver_of_inPpolyDAGFamilyOnSlices

/--
Q3 bridge skeleton (membership-level): per-slice `PpolyDAG` assumptions are
lifted to strict witnesses and then to `SmallDAGSolver`.
-/
def check_smallDAGSolver_of_PpolyDAGOnSlices :
    ∀ (F : GapSliceFamily)
      (hDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.PpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β))),
      let hInDag := inPpolyDAGFamilyOnSlices_of_PpolyDAG F hDag
      ∀ n : Nat, ∀ β ε : Rat,
        SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε :=
  smallDAGSolver_of_PpolyDAGOnSlices

/--
Eventual strict-witness family bridge exposes the canonical eventual
`SmallDAGSolver` surface.
-/
def check_eventuallySmallDAGSolverSurface_of_eventuallyInPpolyDAGWitnessFamily :
    ∀ (F : GapSliceFamily)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      EventuallyInPpolyDAGWitnessFamily F β0 →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_of_eventuallyInPpolyDAGWitnessFamily

/--
Eventual proposition-level witness family bridge also lands at the same
eventual `SmallDAGSolver` surface.
-/
def check_eventuallySmallDAGSolverSurface_of_eventuallyPpolyDAGWitnessFamily :
    ∀ (F : GapSliceFamily)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      EventuallyPpolyDAGWitnessFamily F β0 →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_of_eventuallyPpolyDAGWitnessFamily

/--
Global-language bridge package and transport theorem are available with expected
types (single-global witness -> slice-wise `PpolyDAG`).
-/
def check_ppolyDAGOnSlices_of_globalWitness :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F),
      ComplexityInterfaces.PpolyDAG bridge.L →
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.PpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)) :=
  ppolyDAGOnSlices_of_globalWitness

/--
Global `PpolyDAG` witness bridge to eventual `SmallDAGSolver` surface is
available with expected type.
-/
def check_eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      ComplexityInterfaces.PpolyDAG bridge.L →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness

/--
FinalResult exports the thin wrapper for the new global-witness bridge.
-/
def check_eventuallySmallDAGSolverSurface_surface_of_globalPpolyDAGWitness :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (ε β0 : Rat),
      0 < ε →
      0 < β0 →
      ComplexityInterfaces.PpolyDAG bridge.L →
      EventuallySmallDAGSolverSurface F :=
  eventuallySmallDAGSolverSurface_surface_of_globalPpolyDAGWitness

/--
Global contradiction schema in lower-bounds bridge layer is available.
-/
def check_not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNoSmall :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ ε : Rat, 0 < ε ∧
            ∃ β0 : Rat, 0 < β0 ∧
              ∀ β : Rat, 0 < β → β < β0 →
                ∃ n0 : Nat, ∀ n ≥ n0,
                  ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies

/--
FinalResult exports the same contradiction schema as a thin boundary wrapper.
-/
def check_not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNoSmall :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ ε : Rat, 0 < ε ∧
            ∃ β0 : Rat, 0 < β0 ∧
              ∀ β : Rat, 0 < β → β < β0 →
                ∃ n0 : Nat, ∀ n ≥ n0,
                  ¬ SmallDAGSolver F (ppolyDAGSizeBoundOnSlices F hInDag) n β ε),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_noSmallCanonicalWitnessFamilies

/--
Concrete accepted-family weak-route contradiction theorem is available.
-/
def check_not_globalPpolyDAG_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_of_acceptedFamilyWeakRoute

/--
Concrete promise-YES weak-route contradiction theorem is available.
-/
def check_not_globalPpolyDAG_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_of_promiseYesWeakRoute

/--
Accepted-family weak route + NP witness closure to class-level separation is
available.
-/
def check_NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute

/--
Promise-YES weak route + NP witness closure to class-level separation is
available.
-/
def check_NP_not_subset_PpolyDAG_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_promiseYesWeakRoute

/--
G1 Route-A item (2) gate wrapper is available with the expected type:
provider-family assumptions specialized to canonical `ppolyDAG` size bounds
compile to the accepted-family source theorem schema.
-/
def check_gateG1_routeA2_acceptedFamily_of_providerFamily :
    ∀ (F : GapSliceFamily)
      (_hAccepted :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          acceptedFamilyCertificateAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA2_acceptedFamily_of_providerFamily

/--
G1 Route-A item (1) gate wrapper is available with the expected type:
provider-family assumptions specialized to canonical `ppolyDAG` size bounds
compile to the promise-YES source theorem schema.
-/
def check_gateG1_routeA1_promiseYes_of_providerFamily :
    ∀ (F : GapSliceFamily)
      (_hYes :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          promiseYesSubcubeCertificateAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesPromiseYesSubcubeStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA1_promiseYes_of_providerFamily

/--
Concrete Route-A.2 G1 compiler from restriction-certificate-data families is
available with the expected type.
-/
def check_gateG1_routeA2_acceptedFamily_of_restrictionDataFamily :
    ∀ (F : GapSliceFamily)
      (_hData :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGWitnessRestrictionCertificateDataProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA2_acceptedFamily_of_restrictionDataFamily

/--
Concrete Route-A.2 G1 compiler from extraction+numeric source families is
available with the expected type.
-/
def check_gateG1_routeA2_acceptedFamily_of_restrictionExtractionAndNumericFamily :
    ∀ (F : GapSliceFamily)
      (_hExtract :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGWitnessRestrictionExtractionProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag))
      (_hNumeric :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          smallDAGWitnessRestrictionNumericDataProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)
            (_hExtract hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA2_acceptedFamily_of_restrictionExtractionAndNumericFamily

/--
Concrete Route-A.1 G1 compiler from promise/value package families is available
with the expected type.
-/
def check_gateG1_routeA1_promiseYes_of_packageFamily :
    ∀ (F : GapSliceFamily)
      (_hPkg :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          promiseValueLocalityPackageAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (Models.gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesPromiseYesSubcubeStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag) :=
  gateG1_routeA1_promiseYes_of_packageFamily

/--
FinalResult exports the accepted-family weak-route contradiction wrapper.
-/
def check_not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_acceptedFamilyWeakRoute

/--
FinalResult exports the promise-YES weak-route contradiction wrapper.
-/
def check_not_globalPpolyDAG_surface_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_promiseYesWeakRoute

/--
FinalResult exports the PRG-image weak-route contradiction wrapper.
-/
def check_not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hPrgWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          prgImageAcceptanceAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute

/--
FinalResult exports the stronger restriction-extraction+numeric fallback
contradiction wrapper via the same bridge template.
-/
def check_not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hFallbackWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ hExtract :
            smallDAGWitnessRestrictionExtractionProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag),
            smallDAGWitnessRestrictionNumericDataProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag) hExtract),
      ¬ ComplexityInterfaces.PpolyDAG bridge.L :=
  not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute

/--
FinalResult exports accepted-family weak-route class-level separation wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hAcceptedWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesAcceptedFamilyStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_acceptedFamilyWeakRoute

/--
FinalResult exports promise-YES weak-route class-level separation wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_promiseYesWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hYesWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          SmallDAGImpliesPromiseYesSubcubeStatement
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_promiseYesWeakRoute

/--
FinalResult exports PRG-image weak-route class-level separation wrapper.
-/
def check_NP_not_subset_PpolyDAG_surface_of_prgImageAcceptanceWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hPrgWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          prgImageAcceptanceAtProviderOnSlices
            F (ppolyDAGSizeBoundOnSlices F hInDag)),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_prgImageAcceptanceWeakRoute

/--
FinalResult exports stronger restriction-extraction+numeric fallback class-level
separation wrapper via the shared bridge template.
-/
def check_NP_not_subset_PpolyDAG_surface_of_restrictionExtractionNumericWeakRoute :
    ∀ (F : GapSliceFamily)
      (bridge : AsymptoticDAGLanguageBridge F)
      (_hNP : ComplexityInterfaces.NP bridge.L)
      (_hFallbackWeak :
        ∀ hInDag :
          ∀ n : Nat, ∀ β : Rat,
            ComplexityInterfaces.InPpolyDAG
              (Models.gapPartialMCSP_Language (F.paramsOf n β)),
          ∃ hExtract :
            smallDAGWitnessRestrictionExtractionProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag),
            smallDAGWitnessRestrictionNumericDataProviderOnSlices
              F (ppolyDAGSizeBoundOnSlices F hInDag) hExtract),
      ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_surface_of_restrictionExtractionNumericWeakRoute

end Pnp3.Tests
