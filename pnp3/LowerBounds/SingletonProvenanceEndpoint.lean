import Magnification.AC0AtlasBridge

/-!
  pnp3/LowerBounds/SingletonProvenanceEndpoint.lean

  Minimal endpoint-facing packaging for the active singleton source line.

  This module intentionally does not attempt to prove a contradiction. It
  isolates the strongest object that the current internal source route really
  exports after the family-valued route has been closed:

  * one source-produced bounded atlas package,
  * one linked function `f`,
  * an explicit singleton identity `pack.cert.F = [f]`.

  The point of this layer is to support the next endpoint probe: determine
  which additional singleton/provenance invariant, beyond `ApproxClass`
  membership, would be needed for a contradiction route that does not rely on
  large families.
-/

namespace Pnp3
namespace LowerBounds

open Models
open ComplexityInterfaces

/--
Minimal provenance-aware singleton package exported by the current source line.
-/
structure SemanticSwitchingSingletonProvenancePackagePartial
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) where
  pack : Magnification.AC0AtlasBridge.SemanticSwitchingBoundedAtlasScenarioPartial hFormula
  f : Core.BitVec pack.cert.ac0.n → Bool
  hSingleton : pack.cert.F = [f]
  hEval :
    ∀ x : Core.BitVec pack.cert.ac0.n,
      f x = ComplexityInterfaces.FormulaCircuit.eval
        ((Classical.choose hFormula).family (Models.partialInputLen p))
        (ThirdPartyFacts.castBitVec pack.cert.hsame x)

/--
The current internal semantic provider already realizes the singleton
provenance package.
-/
theorem singletonProvenancePackage_of_internal_provider
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    Nonempty (SemanticSwitchingSingletonProvenancePackagePartial hFormula) := by
  classical
  let cert := Magnification.AC0LocalityBridge.semanticSwitchingCertificate_internal hFormula
  let base := LowerBounds.scenarioFromAC0_with_polylog
    cert.ac0 cert.F cert.hFam cert.hpolyW
  let pack : Magnification.AC0AtlasBridge.SemanticSwitchingBoundedAtlasScenarioPartial hFormula := {
    cert := cert
    k := base.1
    scenario := base.2
    family_eq := by
      simpa [base] using
        LowerBounds.scenarioFromAC0_with_polylog_family_eq
          cert.ac0 cert.F cert.hFam cert.hpolyW
  }
  let f : Core.BitVec pack.cert.ac0.n → Bool :=
    fun x => ComplexityInterfaces.FormulaCircuit.eval
      ((Classical.choose hFormula).family (Models.partialInputLen p))
      (ThirdPartyFacts.castBitVec pack.cert.hsame x)
  refine ⟨{
    pack := pack
    f := f
    hSingleton := ?_
    hEval := ?_
  }⟩
  · simp [pack, cert, f, Magnification.AC0LocalityBridge.semanticSwitchingCertificate_internal]
    funext x
    rfl
  · intro x
    simp [f]

/--
Any singleton provenance package already places its distinguished function in
its source-produced `ApproxClass`.
-/
theorem linked_function_in_approxClass_of_singletonProvenancePackage
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pkg : SemanticSwitchingSingletonProvenancePackagePartial hFormula) :
    pkg.f ∈ Counting.ApproxClass
      (R := pkg.pack.scenario.atlas.dict)
      (k := pkg.pack.scenario.k)
      (ε := pkg.pack.scenario.atlas.epsilon) := by
  have hfF : pkg.f ∈ pkg.pack.cert.F := by
    simpa [pkg.hSingleton]
  have hfSc : pkg.f ∈ pkg.pack.scenario.family := by
    simpa [pkg.pack.family_eq] using hfF
  exact
    Counting.approx_mem_of_errU_le
      (R := pkg.pack.scenario.atlas.dict)
      (k := pkg.pack.scenario.k)
      (ε := pkg.pack.scenario.atlas.epsilon)
      (f := pkg.f)
      (pkg.pack.scenario.bounded pkg.f hfSc)

end LowerBounds
end Pnp3
