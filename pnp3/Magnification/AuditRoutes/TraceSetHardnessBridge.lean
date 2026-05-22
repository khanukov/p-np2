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
    (params : ∀ t, Models.GapPartialMCSPParams)
    (rows : ∀ t, Fin (mOfLen t) → Core.BitVec ((params t).n))
    (red : ∀ t, LowerBounds.TraceToPartialReduction
      ((params t).n) (mOfLen t) (params t) (rows t))
    (N : Nat) (x : ComplexityInterfaces.Bitstring N) : Bool := by
  classical
  exact
    if h : ∃ t, mOfLen t = N then
      let t := Classical.choose h
      let hEq : N = mOfLen t := (Classical.choose_spec h).symm
      let x' : Core.BitVec (mOfLen t) := by simpa [hEq] using x
      Models.gapPartialMCSP_Language (params t)
        (Models.partialInputLen (params t))
        ((red t).encodeY x')
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
  params : ∀ t, Models.GapPartialMCSPParams
  params_n : ∀ t, (params t).n = nOfLen t
  rows : ∀ t, Fin (mOfLen t) → Core.BitVec ((params t).n)
  rowsInj : ∀ t, Function.Injective (fun j : Fin (mOfLen t) => Models.assignmentIndex (rows t j))
  traceToPartialReduction : ∀ t, LowerBounds.TraceToPartialReduction
    ((params t).n) (mOfLen t) (params t) (rows t)
  polyLength : ∀ t,
    LowerBounds.PolyLengthDominance
      (mOfLen t)
      (Models.partialInputLen (params t))
  traceLang : ComplexityInterfaces.Language
  traceLang_def :
    traceLang =
      traceMEMLanguageFromStructure
        spec nOfLen mOfLen params rows traceToPartialReduction
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
