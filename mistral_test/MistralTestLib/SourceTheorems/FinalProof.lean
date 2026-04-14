/- 
Compatibility final wrappers for `mistral_test`.

The original file attempted to close the full canonical-length route for the
experimental `concreteFamily`.  The active `pnp3` tree still lacks an
unconditional `NP_not_subset_PpolyDAG` endpoint for that route, so this module
keeps only the honest consequence wrappers that are available today.
-/
import MistralTestLib.SourceTheorems.IsoStrongMain
import MistralTestLib.SourceTheorems.ConcreteGlobalNP
import MistralTestLib.SourceTheorems.ConcreteFamily
import Magnification.FinalResultMainline
import LowerBounds.DAGStableRestrictionProducer
import Frontier.UnconditionalPneNpFrontier

namespace MistralTestLib

open Pnp3
open Pnp3.ComplexityInterfaces
open Pnp3.Magnification
open Pnp3.Models
open Pnp3.LowerBounds

/-- Re-export the compatibility NP witness language. -/
noncomputable abbrev concreteGlobalLanguage : Language :=
  ConcreteGlobalNP.concreteGlobalLanguage

/-- Re-export the compatibility NP witness. -/
theorem concreteGlobalLanguage_in_NP : NP concreteGlobalLanguage :=
  ConcreteGlobalNP.concreteGlobalLanguage_in_NP



/-- Current final wrapper: once DAG separation is supplied, nothing more is needed here. -/
theorem my_NP_not_subset_PpolyDAG
    (hNPDag : NP_not_subset_PpolyDAG) :
    NP_not_subset_PpolyDAG :=
  hNPDag

/-- Current final wrapper to `P ≠ NP`, matching the active mainline DAG-only endpoint. -/
theorem my_P_ne_NP
    (hNPDag : NP_not_subset_PpolyDAG) :
    P_ne_NP :=
  P_ne_NP_final_dag_only hNPDag

end MistralTestLib
