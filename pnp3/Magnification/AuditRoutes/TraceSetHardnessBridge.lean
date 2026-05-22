import LowerBounds.TraceSetAntiChecker
import Magnification.UnconditionalResearchGap

namespace Pnp3
namespace Magnification
namespace AuditRoutes

open Core
open Models
open LowerBounds

/-- Explicit coercion helper from interface bitstrings to core bit-vectors. -/
def bitstringToBitVec {N : Nat} (x : ComplexityInterfaces.Bitstring N) : Core.BitVec N := x

/--
Structured trace language assembled from the route ingredients.

Current interface version keeps the language as an explicit field passed by the
source record, while requiring a definitional link to route ingredients.
-/
noncomputable def traceMEMLanguageFromStructure
    (spec : Models.GapPartialMCSPAsymptoticSpec)
    (nOfLen mOfLen : Nat → Nat)
    (params : ∀ t : Nat, Models.GapPartialMCSPParams)
    (rows : ∀ t : Nat, Fin (mOfLen t) → Core.BitVec ((params t).n))
    (red : ∀ t : Nat, LowerBounds.TraceToPartialReduction
      ((params t).n) (mOfLen t) (params t) (rows t))
    (N : Nat) (x : ComplexityInterfaces.Bitstring N) : Bool := by
  classical
  exact
    if h : ∃ t, mOfLen t = N then
      let t := Classical.choose h
      let hEq : N = mOfLen t := (Classical.choose_spec h).symm
      let x' : Core.BitVec (mOfLen t) := by
        simpa [hEq] using (bitstringToBitVec x)
      Models.gapPartialMCSP_Language (params t)
        (Models.partialInputLen (params t))
        ((LowerBounds.TraceToPartialReduction.encode (R := red t)) x')
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
  params : ∀ t : Nat, Models.GapPartialMCSPParams
  params_n : ∀ t : Nat, (params t).n = nOfLen t
  rows : ∀ t : Nat, Fin (mOfLen t) → Core.BitVec ((params t).n)
  rowsInj : ∀ t : Nat, Function.Injective (fun j : Fin (mOfLen t) => Models.assignmentIndex (rows t j))
  traceToPartialReduction : ∀ t : Nat, LowerBounds.TraceToPartialReduction
    ((params t).n) (mOfLen t) (params t) (rows t)
  polyLength : ∀ t : Nat,
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
