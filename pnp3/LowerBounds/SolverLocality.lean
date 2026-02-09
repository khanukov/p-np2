import LowerBounds.AntiChecker_Partial

/-!
  pnp3/LowerBounds/SolverLocality.lean

  Re-export of `solver_is_local` from `AntiChecker_Partial`.

  `solver_is_local` is a trivial theorem that extracts the `decideLocal`
  field from `SmallLocalCircuitSolver_Partial`.  The locality is provided
  during solver construction via `ppoly_circuit_locality`.
-/
