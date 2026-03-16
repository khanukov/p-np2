import Magnification.AC0AtlasBridge

/-!
  pnp3/LowerBounds/ApproxClassContradiction.lean

  Thin entry points for the next contradiction track:
  move from source-side semantic switching packages to a single linked function
  lying in `ApproxClass`, with exact singleton error on the current internal
  route.

  This module intentionally does not try to derive a contradiction yet. It
  only packages the current source output in the form naturally suited for a
  future single-function approximation endpoint.
-/

namespace Pnp3
namespace LowerBounds

open Models
open ComplexityInterfaces

/--
Any packaged semantic switching scenario budget already places one linked
function in the corresponding `ApproxClass`.
-/
theorem linked_function_in_approxClass_of_semanticSwitchingScenarioBudget
    {p : GapPartialMCSPParams}
    {hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)}
    (pack : Magnification.AC0AtlasBridge.SemanticSwitchingScenarioBudgetPartial hFormula) :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    ∃ f : Core.BitVec pack.cert.ac0.n → Bool,
      f ∈ pack.cert.F ∧
      (∀ x : Core.BitVec pack.cert.ac0.n,
        f x = ComplexityInterfaces.FormulaCircuit.eval c
          (ThirdPartyFacts.castBitVec pack.cert.hsame x)) ∧
      f ∈ Counting.ApproxClass
        (R := pack.pack.scenario.atlas.dict)
        (k := pack.pack.scenario.k)
        (ε := pack.pack.scenario.atlas.epsilon) := by
  classical
  intro wf c
  rcases pack.cert.hLink with ⟨f, hfF, hfEval⟩
  have hfSc : f ∈ pack.pack.scenario.family := by
    simpa [pack.pack.family_eq] using hfF
  have hApprox :
      f ∈ Counting.ApproxClass
        (R := pack.pack.scenario.atlas.dict)
        (k := pack.pack.scenario.k)
        (ε := pack.pack.scenario.atlas.epsilon) := by
    exact
      Counting.approx_mem_of_errU_le
        (R := pack.pack.scenario.atlas.dict)
        (k := pack.pack.scenario.k)
        (ε := pack.pack.scenario.atlas.epsilon)
        (f := f)
        (pack.pack.scenario.bounded f hfSc)
  exact ⟨f, hfF, hfEval, hApprox⟩

/--
Public contradiction-layer entry point for the current singleton source route:
the linked slice function already lies in some `ApproxClass` with exact error
`1 / (n + 2)`.
-/
theorem current_source_route_gives_singleton_approxClass
    {p : GapPartialMCSPParams}
    (hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p)) :
    let wf : ComplexityInterfaces.InPpolyFormula (gapPartialMCSP_Language p) :=
      Classical.choose hFormula
    let c := wf.family (Models.partialInputLen p)
    let f : Core.BitVec (Models.partialInputLen p) → Bool :=
      fun x => ComplexityInterfaces.FormulaCircuit.eval c x
    ∃ (R : List (Core.Subcube (Models.partialInputLen p))) (k : Nat) (ε : Core.Q),
      f ∈ Counting.ApproxClass (R := R) (k := k) (ε := ε) ∧
      ε = (1 : Core.Q) / (Models.partialInputLen p + 2) := by
  simpa using Magnification.AC0LocalityBridge.current_singleton_linked_function_in_approxClass hFormula

end LowerBounds
end Pnp3
