import Magnification.AC0LocalityBridge
import LowerBounds.LB_Formulas

/-!
  pnp3/Magnification/AC0AtlasBridge.lean

  Named bridges from source-side semantic switching certificates to the
  atlas/scenario-budget objects already consumed by the lower-bound layer.

  This module intentionally stops on the atlas/SAL side. It does not attempt
  to recover a chosen restriction witness or the easy-family/cardinality
  contradiction payload from `AntiChecker_Partial`; that remains the next
  constructive frontier.
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
