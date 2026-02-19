import Magnification.Facts_Magnification_Partial
import Magnification.Bridge_to_Magnification_Partial
import LowerBounds.LB_GeneralFromLocal_Partial
import LowerBounds.LB_LocalCircuits_Partial
import LowerBounds.LB_Formulas_Core_Partial
import Complexity.Interfaces

/-!
  pnp3/Tests/CoreConeAxiomsAudit.lean

  Core-cone audit (realized route): all intermediate nodes below final
  theorems should depend only on Lean's classical base axioms
  (`propext`, `Classical.choice`, `Quot.sound`) and not on project-specific
  external scaffolding.
-/

open Pnp3
open Pnp3.Magnification
open Pnp3.LowerBounds
open Pnp3.ComplexityInterfaces

#print axioms P_ne_NP_from_partial_formulas_realized
#print axioms NP_not_subset_Ppoly_from_partial_formulas_realized
#print axioms OPS_trigger_formulas_partial_realized
#print axioms OPS_trigger_general_contra_partial_realized
#print axioms LB_GeneralFromLocal_partial_realized
#print axioms LB_LocalCircuits_core_partial_realized
#print axioms LB_Formulas_core_partial_realized
#print axioms P_ne_NP_of_nonuniform_separation
