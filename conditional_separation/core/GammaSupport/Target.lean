import Body.Raw
import Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownIterationBridge
namespace GammaSupport
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds
/-- Accepted-content feasibility only, not runtime parsing or a verdict. -/
def Exact : Prop :=
  ∀ (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr →
    contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = true →
    3 ≤ pr.2.n → ∀ g,
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some g →
    9+2*g ≤ a+m
end GammaSupport
