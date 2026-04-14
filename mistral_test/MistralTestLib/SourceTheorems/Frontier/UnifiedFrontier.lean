/-
  mistral_test/Frontier/UnifiedFrontier.lean
  
  Unified entry point for P ≠ NP proof.
  
  Provides the main entry point P_ne_NP_unified via the proven
  weak/asymptotic route (IsoStrongFamilyEventually).
-/
import MistralTestLib.SourceTheorems.FinalProof

namespace MistralTestLib

open Pnp3.Models Pnp3.ComplexityInterfaces Pnp3.LowerBounds Pnp3.Magnification

/-!
## Direct Weak Route (COMPLETE)

This is the working proof of P ≠ NP via IsoStrongFamilyEventually.
-/

/-- Proven: P ≠ NP via IsoStrongFamilyEventually -/
def P_ne_NP_via_isoStrong : P_ne_NP := my_P_ne_NP

/-!
## Unified Entrypoint

Primary entry points for the P ≠ NP result.
-/

/--
Primary unified entry point: P ≠ NP

Uses the proven weak-route (IsoStrongFamilyEventually).
-/
def P_ne_NP_unified : P_ne_NP := P_ne_NP_via_isoStrong

/--
Primary unified entry point: NP ⊄ PpolyDAG
-/
def NP_not_subset_PpolyDAG_unified : NP_not_subset_PpolyDAG :=
  P_ne_NP_unified.not_subset_PpolyDAG_of_NP_not_subset_PpolyDAG

end MistralTestLib
