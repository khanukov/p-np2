import LowerBounds.TraceSetAntiChecker
import Magnification.UnconditionalResearchGap

namespace Pnp3
namespace Magnification
namespace AuditRoutes

open Core
open Models
open LowerBounds

/--
Structured trace language assembled from the route ingredients.

Current interface version keeps the language as an explicit field passed by the
source record, while requiring a definitional link to route ingredients.
-/
noncomputable def traceMEMLanguageFromStructure
    (spec : Models.GapPartialMCSPAsymptoticSpec)
    (nOfLen mOfLen : Nat → Nat)
    (rows : ∀ t, Fin (mOfLen t) → Core.BitVec (nOfLen t))
    (red : ∀ t, LowerBounds.TraceToPartialReduction)
    (N : Nat) (x : ComplexityInterfaces.Bitstring N) : Bool := by
  classical
  exact
    if h : ∃ t, mOfLen t = N then
      let t := Classical.choose h
      let p := (red t).p
      let x' : Core.BitVec (mOfLen t) := by simpa [Classical.choose_spec h] using x
      Models.gapPartialMCSP_Language p (Models.partialInputLen p) ((red t).encodeY x')
    else
      false

/--
Structured source theorem interface for the Trace-Set route.

Unlike an unstructured `∃ L, NP L ∧ ¬PpolyDAG L`, this record requires
explicit parameter functions, rows, reduction artifacts and a definitional link
between `traceLang` and the structured route data.
-/
structure StructuredTraceSetHardnessSource where
  spec : Models.GapPartialMCSPAsymptoticSpec
  nOfLen : Nat → Nat
  mOfLen : Nat → Nat
  rows : ∀ t, Fin (mOfLen t) → Core.BitVec (nOfLen t)
  rowsInj : ∀ t, Function.Injective (fun j : Fin (mOfLen t) => Models.assignmentIndex (rows t j))
  traceToPartialReduction : ∀ t, LowerBounds.TraceToPartialReduction
  polyLength : ∀ t,
    LowerBounds.PolyLengthDominance
      (mOfLen t)
      (Models.partialInputLen ((traceToPartialReduction t).p))
  traceLang : ComplexityInterfaces.Language
  traceLang_def :
    traceLang =
      traceMEMLanguageFromStructure
        spec nOfLen mOfLen rows traceToPartialReduction
  traceMEM_in_NP : ComplexityInterfaces.NP traceLang
  traceMEM_not_in_PpolyDAG : ¬ ComplexityInterfaces.PpolyDAG traceLang

/-- Bridge from the structured Trace-Set source interface to the project gap witness. -/
noncomputable def researchGapWitness_of_structuredTraceSetHardness
    (H : StructuredTraceSetHardnessSource) :
    Magnification.ResearchGapWitness := by
  refine ⟨?_⟩
  exact ⟨H.traceLang, H.traceMEM_in_NP, H.traceMEM_not_in_PpolyDAG⟩

end AuditRoutes
end Magnification
end Pnp3
