import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation

/-!
# T1 true uniform-seek examples

These examples instantiate the canonical encoder round trip and the proved
read-only validation/rewind trace at one concrete request.  `startMutation` is
the T1a→T1b entry point: T1b-A1 makes it an active mutation mode, so reaching
it is a validation/rewind result, not an addressing-success result.  Nothing
here executes cursor installation, a unary decrement, restoration, output, or
acceptance.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- A small canonical request used to instantiate the T1 theorems. -/
def t1aExampleRequest : T1Request := ⟨2, [true, false, true]⟩

example : decodeT1Tape? (encodeT1 t1aExampleRequest) = some t1aExampleRequest :=
  decodeT1Tape_encode t1aExampleRequest

/-- The exact validation/rewind execution theorem at the concrete request:
`2 * n + 9` genuine TM steps land on the now-active `startMutation` boundary
with the complete initial tape unchanged. -/
example :
    let n := (encodeT1 t1aExampleRequest).length
    TM.runConfig (M := T1M)
        (T1M.initialConfig (t1Point (encodeT1 t1aExampleRequest)))
        (2 * n + 9) =
      t1AlignedConfig n 0 (by
        simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength])
        (T1M.initialConfig (t1Point (encodeT1 t1aExampleRequest))).tape
        .startMutation :=
  t1CS_validate_rewind_encoded_exact t1aExampleRequest

end Pnp3.Internal.PsubsetPpoly.TM
