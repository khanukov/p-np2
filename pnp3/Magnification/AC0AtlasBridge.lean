import Magnification.AC0LocalityBridge
import LowerBounds.LB_Formulas

/-!
  pnp3/Magnification/AC0AtlasBridge.lean

  Named bridges from source-side semantic switching certificates to the
  atlas/scenario-budget objects already consumed by the lower-bound layer.

  This module intentionally stops before contradiction.
  In the current tree it does three things:
  1) packages source certificates into atlas/scenario-budget objects;
  2) records no-go results for the false downstream routes
     (`ScenarioBudget -> strict large-family gap`,
      `ApproxClass -> generic small mismatch`);
  3) exposes the provenance-aware stronger-source frontier
     (`SemanticSwitchingSmallMismatchPackagePartial`).
-/

namespace Pnp3
namespace Magnification
namespace AC0AtlasBridge

open Models
open ComplexityInterfaces

/--
Source-side atlas package extracted from one semantic switching certificate.

This stays on the atlas/SAL side and does not attempt to choose any exact
restriction witness.
-/
structure SemanticSwitchingBoundedAtlasScenarioPartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  cert : AC0LocalityBridge.SemanticSwitchingCertificatePartial hFormula
  k : Nat
  scenario : LowerBounds.BoundedAtlasScenario cert.ac0.n
  family_eq : scenario.family = cert.F

/--
Source-side scenario-budget package extracted from one semantic switching
certificate.
-/
structure SemanticSwitchingScenarioBudgetPartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  cert : AC0LocalityBridge.SemanticSwitchingCertificatePartial hFormula
  pack : LowerBounds.ScenarioBudget cert.ac0.n cert.F

/-- Provider-level version of bounded atlas scenarios from source certificates. -/
def SemanticSwitchingBoundedAtlasScenarioProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (SemanticSwitchingBoundedAtlasScenarioPartial hFormula)

/-- Provider-level version of scenario budgets from source certificates. -/
def SemanticSwitchingScenarioBudgetProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (SemanticSwitchingScenarioBudgetPartial hFormula)

/--
Provenance-aware stronger source package for the current atlas route.

This asks only for one source-produced bounded atlas package together with one
linked bounded-union witness whose full mismatch set is already
polylogarithmically small.
-/
structure SemanticSwitchingSmallMismatchPackagePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  pack : SemanticSwitchingBoundedAtlasScenarioPartial hFormula
  f : Core.BitVec pack.cert.ac0.n → Bool
  hfF : f ∈ pack.cert.F
  hfEval :
    ∀ x : Core.BitVec pack.cert.ac0.n,
      f x = ComplexityInterfaces.FormulaCircuit.eval
        ((Classical.choose hFormula).family (Models.partialInputLen p))
        (ThirdPartyFacts.castBitVec pack.cert.hsame x)
  S : List (Core.Subcube pack.cert.ac0.n)
  hlen : S.length ≤ pack.k
  hsub : Core.listSubset S pack.scenario.atlas.dict
  hsmall :
    (Counting.mismatchSet (fun x => Core.coveredB S x) f).card
      ≤ Models.polylogBudget pack.cert.ac0.n

/--
Provider-level version of the stronger small-mismatch source package.
-/
def SemanticSwitchingSmallMismatchProviderPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)),
    Nonempty (SemanticSwitchingSmallMismatchPackagePartial hFormula)

/--
Compatibility-only global form of the stronger source target.

This is stronger than the provenance-aware package/provider formulation above,
because it quantifies over every bounded atlas package, not just the one
actually produced by the source route.

This is strictly stronger than the currently available density control
`errU ≤ ε`. It is the precise additional input needed to recover the small
testset route from the existing atlas package.
-/
def SemanticSwitchingSmallMismatchExtractionPartial : Prop :=
  ∀ {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pack : SemanticSwitchingBoundedAtlasScenarioPartial hFormula),
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ f : Core.BitVec pack.cert.ac0.n → Bool,
      f ∈ pack.cert.F ∧
      (∀ x : Core.BitVec pack.cert.ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec pack.cert.hsame x)) ∧
      ∃ S : List (Core.Subcube pack.cert.ac0.n),
        S.length ≤ pack.k ∧
        Core.listSubset S pack.scenario.atlas.dict ∧
        (Counting.mismatchSet (fun x => Core.coveredB S x) f).card
          ≤ Models.polylogBudget pack.cert.ac0.n

/--
Named bridge: one semantic switching certificate yields one bounded atlas
scenario through the existing polylog AC0-to-atlas route.
-/
theorem boundedAtlasScenario_of_semanticSwitchingCertificate
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (cert : AC0LocalityBridge.SemanticSwitchingCertificatePartial hFormula) :
    Nonempty (SemanticSwitchingBoundedAtlasScenarioPartial hFormula) := by
  classical
  let base := LowerBounds.scenarioFromAC0_with_polylog
    cert.ac0 cert.F cert.hFam cert.hpolyW
  refine ⟨{
    cert := cert
    k := base.1
    scenario := base.2
    family_eq := ?_
  }⟩
  simpa [base] using
    LowerBounds.scenarioFromAC0_with_polylog_family_eq
      cert.ac0 cert.F cert.hFam cert.hpolyW

/--
Named bridge: one semantic switching certificate yields one scenario budget.
-/
theorem scenarioBudget_of_semanticSwitchingCertificate
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (cert : AC0LocalityBridge.SemanticSwitchingCertificatePartial hFormula) :
    Nonempty (SemanticSwitchingScenarioBudgetPartial hFormula) := by
  exact ⟨{
    cert := cert
    pack := LowerBounds.scenarioBudgetFromAC0 cert.ac0 cert.F cert.hFam
  }⟩

/--
No-go corollary for the current atlas route:
the packaged scenario budget cannot by itself produce the strict large-family
gap required by the current `AntiChecker_Partial` contradiction endpoint.
-/
theorem semanticSwitchingScenarioBudget_no_large_gap
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pack : SemanticSwitchingScenarioBudgetPartial hFormula) :
    ¬ ∃ Y : Finset (Core.BitVec pack.cert.ac0.n → Bool),
        Y ⊆ LowerBounds.familyFinset (sc := pack.pack.scenario) ∧
        LowerBounds.scenarioCapacity (sc := pack.pack.scenario) < Y.card := by
  exact LowerBounds.no_large_subset_of_boundedAtlasScenario pack.pack.scenario

/--
The current source-side scenario budget yields a concrete linked function `f`
and a natural testset `T = mismatchSet (coveredB S) f` whose size is controlled
by the atlas error bound.

This is the exact singleton-compatible payload extracted from the current
`WorksFor` witness before any attempt to force `T` to be polylogarithmically
small.
-/
theorem linked_testset_of_semanticSwitchingScenarioBudget
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pack : SemanticSwitchingScenarioBudgetPartial hFormula) :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ f : Core.BitVec pack.cert.ac0.n → Bool,
      f ∈ pack.cert.F ∧
      (∀ x : Core.BitVec pack.cert.ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec pack.cert.hsame x)) ∧
      ∃ T : Finset (Core.BitVec pack.cert.ac0.n),
        f ∈ Counting.ApproxOnTestset
          (R := pack.pack.scenario.atlas.dict)
          (k := pack.pack.scenario.k)
          (T := T) ∧
        ((T.card : Core.Q)
          ≤ (1 : Core.Q) / (pack.cert.ac0.n + 2) *
              ((Nat.pow 2 pack.cert.ac0.n : Nat) : Core.Q)) := by
  classical
  intro wf c
  rcases pack.cert.hLink with ⟨f, hfF, hfEval⟩
  have hfSc : f ∈ pack.pack.scenario.family := by
    simpa [pack.pack.family_eq] using hfF
  rcases pack.pack.scenario.bounded f hfSc with ⟨S, hlen, hsub, herr⟩
  let T : Finset (Core.BitVec pack.cert.ac0.n) :=
    Counting.mismatchSet (fun x => Core.coveredB S x) f
  have hApprox :
      f ∈ Counting.ApproxOnTestset
        (R := pack.pack.scenario.atlas.dict)
        (k := pack.pack.scenario.k)
        (T := T) := by
    exact Counting.approxOnTestset_of_mismatchSet hlen hsub
  have hCardErr :
      ((T.card : Core.Q)
        ≤ pack.pack.scenario.atlas.epsilon *
            ((Nat.pow 2 pack.cert.ac0.n : Nat) : Core.Q)) := by
    exact Counting.mismatchSet_card_le_of_errU_le f S
      pack.pack.scenario.atlas.epsilon herr
  have hPowNonneg :
      (0 : Core.Q) ≤ ((Nat.pow 2 pack.cert.ac0.n : Nat) : Core.Q) := by
    positivity
  have hCard :
      ((T.card : Core.Q)
        ≤ (1 : Core.Q) / (pack.cert.ac0.n + 2) *
            ((Nat.pow 2 pack.cert.ac0.n : Nat) : Core.Q)) := by
    exact le_trans hCardErr <|
      mul_le_mul_of_nonneg_right pack.pack.epsilon_le_inv hPowNonneg
  refine ⟨f, hfF, hfEval, T, hApprox, hCard⟩

/--
If a source-side bounded atlas package additionally comes with a bounded-union
witness whose mismatch set is already polylogarithmically small, then the
current small-testset layer is recovered immediately.

This is the exact downstream reuse point for any future stronger source
theorem. It still does **not** bypass the separate large-family obstruction in
the current `AntiChecker_Partial` endpoint.
-/
theorem linked_small_testset_of_boundedAtlasScenario
    (hExtract : SemanticSwitchingSmallMismatchExtractionPartial)
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pack : SemanticSwitchingBoundedAtlasScenarioPartial hFormula) :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ f : Core.BitVec pack.cert.ac0.n → Bool,
      f ∈ pack.cert.F ∧
      (∀ x : Core.BitVec pack.cert.ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec pack.cert.hsame x)) ∧
      ∃ T : Finset (Core.BitVec pack.cert.ac0.n),
        T.card ≤ Models.polylogBudget pack.cert.ac0.n ∧
        f ∈ Counting.ApproxOnTestset
          (R := pack.scenario.atlas.dict)
          (k := pack.k)
          (T := T) := by
  classical
  intro wf c
  rcases hExtract pack with ⟨f, hfF, hfEval, S, hlen, hsub, hcard⟩
  refine ⟨f, hfF, ?_, ?_⟩
  · simpa using hfEval
  · exact
      (Counting.exists_small_testset_iff_exists_small_mismatch_approximant
        (R := pack.scenario.atlas.dict)
        (k := pack.k)
        (B := Models.polylogBudget pack.cert.ac0.n)
        (f := f)).2
        ⟨S, hlen, hsub, hcard⟩

/--
Compatibility bridge: a global extraction theorem on all bounded atlas
packages yields a provenance-aware source package for each such package.
-/
theorem semanticSwitchingSmallMismatchPackage_of_extraction
    (hExtract : SemanticSwitchingSmallMismatchExtractionPartial)
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pack : SemanticSwitchingBoundedAtlasScenarioPartial hFormula) :
    Nonempty (SemanticSwitchingSmallMismatchPackagePartial hFormula) := by
  classical
  rcases hExtract pack with ⟨f, hfF, hfEval, S, hlen, hsub, hsmall⟩
  exact ⟨{
    pack := pack
    f := f
    hfF := hfF
    hfEval := hfEval
    S := S
    hlen := hlen
    hsub := hsub
    hsmall := hsmall
  }⟩

/--
One provenance-aware small-mismatch package immediately yields one linked
polylog-small testset for the current atlas route.
-/
theorem linked_small_testset_of_semanticSwitchingSmallMismatchPackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (smallPack : SemanticSwitchingSmallMismatchPackagePartial hFormula) :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ f : Core.BitVec smallPack.pack.cert.ac0.n → Bool,
      f ∈ smallPack.pack.cert.F ∧
      (∀ x : Core.BitVec smallPack.pack.cert.ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec smallPack.pack.cert.hsame x)) ∧
      ∃ T : Finset (Core.BitVec smallPack.pack.cert.ac0.n),
        T.card ≤ Models.polylogBudget smallPack.pack.cert.ac0.n ∧
        f ∈ Counting.ApproxOnTestset
          (R := smallPack.pack.scenario.atlas.dict)
          (k := smallPack.pack.k)
          (T := T) := by
  classical
  intro wf c
  refine ⟨smallPack.f, smallPack.hfF, smallPack.hfEval, ?_⟩
  exact
    (Counting.exists_small_testset_iff_exists_small_mismatch_approximant
      (R := smallPack.pack.scenario.atlas.dict)
      (k := smallPack.pack.k)
      (B := Models.polylogBudget smallPack.pack.cert.ac0.n)
      (f := smallPack.f)).2
      ⟨smallPack.S, smallPack.hlen, smallPack.hsub, smallPack.hsmall⟩

/--
Provider-level bridge from provenance-aware small-mismatch packages to the
linked polylog-small testset layer.
-/
theorem linked_small_testset_provider_of_semanticSwitchingSmallMismatchProvider
    (hSmall : SemanticSwitchingSmallMismatchProviderPartial)
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let smallPack := Classical.choice (hSmall hFormula)
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ f : Core.BitVec smallPack.pack.cert.ac0.n → Bool,
      f ∈ smallPack.pack.cert.F ∧
      (∀ x : Core.BitVec smallPack.pack.cert.ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec smallPack.pack.cert.hsame x)) ∧
      ∃ T : Finset (Core.BitVec smallPack.pack.cert.ac0.n),
        T.card ≤ Models.polylogBudget smallPack.pack.cert.ac0.n ∧
        f ∈ Counting.ApproxOnTestset
          (R := smallPack.pack.scenario.atlas.dict)
          (k := smallPack.pack.k)
          (T := T) := by
  classical
  let smallPack := Classical.choice (hSmall hFormula)
  simpa [smallPack] using
    linked_small_testset_of_semanticSwitchingSmallMismatchPackage smallPack

/--
Compatibility bridge: a bounded-atlas provider plus the old global extraction
target yields the provenance-aware small-mismatch provider.
-/
theorem semanticSwitchingSmallMismatchProvider_of_boundedAtlasScenarioProvider_and_extraction
    (hPack : SemanticSwitchingBoundedAtlasScenarioProviderPartial)
    (hExtract : SemanticSwitchingSmallMismatchExtractionPartial) :
    SemanticSwitchingSmallMismatchProviderPartial := by
  intro p hFormula
  rcases hPack (p := p) hFormula with ⟨pack⟩
  exact semanticSwitchingSmallMismatchPackage_of_extraction hExtract pack

/--
Lift the atlas bridge to the provider level.
-/
theorem boundedAtlasScenarioProvider_of_semanticSwitchingCertificateProvider
    (hCert : AC0LocalityBridge.SemanticSwitchingCertificateProviderPartial) :
    SemanticSwitchingBoundedAtlasScenarioProviderPartial := by
  intro p hFormula
  rcases hCert (p := p) hFormula with ⟨cert⟩
  exact boundedAtlasScenario_of_semanticSwitchingCertificate cert

/--
Lift the scenario-budget bridge to the provider level.
-/
theorem scenarioBudgetProvider_of_semanticSwitchingCertificateProvider
    (hCert : AC0LocalityBridge.SemanticSwitchingCertificateProviderPartial) :
    SemanticSwitchingScenarioBudgetProviderPartial := by
  intro p hFormula
  rcases hCert (p := p) hFormula with ⟨cert⟩
  exact scenarioBudget_of_semanticSwitchingCertificate cert

/--
Direct atlas-scenario provider from the current semantic multi-switching
provider.
-/
theorem boundedAtlasScenarioProvider_of_formulaSemanticMultiSwitchingProvider
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider) :
    SemanticSwitchingBoundedAtlasScenarioProviderPartial := by
  exact
    boundedAtlasScenarioProvider_of_semanticSwitchingCertificateProvider
      (AC0LocalityBridge.semanticSwitchingCertificateProvider_of_provider hSem)

/--
Direct scenario-budget provider from the current semantic multi-switching
provider.
-/
theorem scenarioBudgetProvider_of_formulaSemanticMultiSwitchingProvider
    (hSem : AC0LocalityBridge.FormulaSemanticMultiSwitchingProvider) :
    SemanticSwitchingScenarioBudgetProviderPartial := by
  exact
    scenarioBudgetProvider_of_semanticSwitchingCertificateProvider
      (AC0LocalityBridge.semanticSwitchingCertificateProvider_of_provider hSem)

/--
Internal provider instance for the current source-side semantic package.
-/
theorem scenarioBudgetProvider_of_formulaSemanticMultiSwitchingProvider_internal :
    SemanticSwitchingScenarioBudgetProviderPartial := by
  exact
    scenarioBudgetProvider_of_formulaSemanticMultiSwitchingProvider
      AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal

/--
Internal atlas-scenario provider instance for the current source-side semantic
package.
-/
theorem boundedAtlasScenarioProvider_of_formulaSemanticMultiSwitchingProvider_internal :
    SemanticSwitchingBoundedAtlasScenarioProviderPartial := by
  exact
    boundedAtlasScenarioProvider_of_formulaSemanticMultiSwitchingProvider
      AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal

end AC0AtlasBridge
end Magnification
end Pnp3
