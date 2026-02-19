/-- Minimal `lake test` entry point.

This avoids runtime segfaults observed when launching a heavily-linked test
executable in this environment. Functional runtime checks are executed via
`lake env lean --run pnp3/Tests/TestDriver.lean` from `scripts/check.sh`.
-/
def main : IO Unit := pure ()
