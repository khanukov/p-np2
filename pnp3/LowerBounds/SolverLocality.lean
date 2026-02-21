import LowerBounds.AntiChecker_Partial

/-!
  pnp3/LowerBounds/SolverLocality.lean

  Re-export of `solver_is_local` from `AntiChecker_Partial`.

  `solver_is_local` is a trivial theorem that extracts the `decideLocal`
  field from `SmallLocalCircuitSolver_Partial`.  The locality is supplied
  during solver construction via an explicit external goal witness.
-/
