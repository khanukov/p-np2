import LowerBounds.AntiChecker_Partial
import LowerBounds.LB_Formulas_Core_Partial
import LowerBounds.LB_LocalCircuits_Partial

/-!
  pnp3/Tests/AntiCheckerConeAxiomsAudit.lean

  Focused audit for the Anti-Checker cone (Part C, partial track):
  these statements should not depend on project-specific axioms.
-/

open Pnp3
open Pnp3.LowerBounds

#print axioms antiChecker_largeY_certificate_partial_witness
#print axioms antiChecker_largeY_certificate_local_partial_witness
#print axioms noSmallAC0Solver_partial_witness
#print axioms noSmallLocalCircuitSolver_partial_witness
#print axioms LB_Formulas_core_partial_witness
#print axioms LB_LocalCircuits_core_partial_witness
