/-
  Minimal `lake test` executable.

  Runtime checks are executed via:
    lake env lean --run pnp3/Tests/TestDriver.lean
  in `scripts/check.sh` to avoid native runtime instability.
-/

def main : IO Unit := pure ()
