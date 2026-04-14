/- 
Unified compatibility entry points for `mistral_test`.

These wrappers intentionally expose the current honest interface: the library
can forward a supplied DAG-separation witness to `P ≠ NP`, but it does not
manufacture an unconditional endpoint that the active `pnp3` tree does not yet
prove.
-/
import MistralTestLib.SourceTheorems.FinalProof

namespace MistralTestLib

open Pnp3.ComplexityInterfaces

/-- DAG-separation to `P ≠ NP`, via the current `mistral_test` compatibility layer. -/
def P_ne_NP_via_isoStrong
    (hNPDag : NP_not_subset_PpolyDAG) :
    P_ne_NP :=
  my_P_ne_NP hNPDag

/-- Primary unified compatibility entry point. -/
def P_ne_NP_unified
    (hNPDag : NP_not_subset_PpolyDAG) :
    P_ne_NP :=
  P_ne_NP_via_isoStrong hNPDag

/-- Unified `NP ⊄ PpolyDAG` entry point. -/
def NP_not_subset_PpolyDAG_unified
    (hNPDag : NP_not_subset_PpolyDAG) :
    NP_not_subset_PpolyDAG :=
  my_NP_not_subset_PpolyDAG hNPDag

end MistralTestLib
