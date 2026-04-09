import LowerBounds.AsymptoticDAGBarrierTheorems

namespace Pnp3
namespace LowerBounds

/-!
`RouteNextStep_AcceptedFamily`

Active continuation route after closing/deprecating the table-force dead-end.

This module intentionally contains only forwarding statements for the accepted
family surface, so downstream files can import one stable "next step" module
without touching deprecated convenience paths or failed-route diagnostics.
-/

/--
Primary active endpoint alias.

Use this route when the source side can provide accepted-family witnesses for
small DAG solvers (`SmallDAGImpliesAcceptedFamilyStatement`).
-/
theorem NP_not_subset_PpolyDAG_viaAcceptedFamilyRoute
    (F : GapSliceFamily)
    (bridge : AsymptoticDAGLanguageBridge F)
    (hNP : ComplexityInterfaces.NP bridge.L)
    (hAcceptedWeak :
      ∀ hInDag :
        ∀ n : Nat, ∀ β : Rat,
          ComplexityInterfaces.InPpolyDAG
            (gapPartialMCSP_Language (F.paramsOf n β)),
        SmallDAGImpliesAcceptedFamilyStatement
          F (ppolyDAGSizeBoundOnSlices F hInDag)) :
    ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute
    F bridge hNP hAcceptedWeak

end LowerBounds
end Pnp3
