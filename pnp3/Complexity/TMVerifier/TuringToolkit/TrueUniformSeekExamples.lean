import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation

/-!
# T1a true uniform-seek examples

These examples exercise only the canonical encoder and the proved read-only
validation/rewind handoff.  The idle `startMutation` state is the end of T1a,
not an addressing-success result.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- A small canonical request used to instantiate the T1a theorems. -/
def t1aExampleRequest : T1Request := ⟨2, [true, false, true]⟩

example : decodeT1Tape? (encodeT1 t1aExampleRequest) = some t1aExampleRequest :=
  decodeT1Tape_encode t1aExampleRequest

end Pnp3.Internal.PsubsetPpoly.TM
