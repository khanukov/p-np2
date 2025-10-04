import Core.BooleanBasics

/-!
A lightweight smoke test that ensures the core `Pnp3` modules compile and
can be imported in a standalone Lean executable.  If module resolution or
compilation fails, running this script will error out, making it a handy
CI guard.
-/
open Pnp3

/--
Entry point used by `lake env lean --run scripts/smoke.lean`.  When this
script runs successfully it prints a short confirmation message.
-/
def main : IO Unit := do
  -- Touch the `BitVec` abbreviation to confirm the namespace is live.
  let _ : BitVec 0 = BitVec 0 := rfl
  IO.println "Pnp3 core modules are available and basic definitions type-check."
