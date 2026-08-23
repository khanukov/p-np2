import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation

/-!
# T1a true uniform-seek surface tests

These compile-time probes pin the canonical codec, public quadratic clock,
and exact read-only validation/rewind handoff.  They deliberately expose no
T1b addressing-success surface.
-/

namespace Pnp3.Tests.TMTrueUniformSeekSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

theorem check_decodeT1Tape_encode (r : T1Request) :
    decodeT1Tape? (encodeT1 r) = some r :=
  decodeT1Tape_encode r

theorem check_t1CS_runTime (N : Nat) :
    t1CS.toPhased.toTM.runTime N = 128 * (N + 1) ^ 2 + 128 :=
  t1CS_runTime N

theorem check_t1CS_validate_rewind_encoded_exact (r : T1Request) :
    let n := (encodeT1 r).length
    TM.runConfig (M := t1CS.toPhased.toTM)
        ((t1CS.toPhased.toTM).initialConfig (t1Point (encodeT1 r)))
        (2 * n + 9) =
      t1AlignedConfig n 0 (by
        simp [t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength])
        ((t1CS.toPhased.toTM).initialConfig
          (t1Point (encodeT1 r))).tape .startMutation :=
  t1CS_validate_rewind_encoded_exact r

theorem check_t1CS_run_encoded_reaches_mutation (r : T1Request) :
    let n := (encodeT1 r).length
    (t1CS.toPhased.toTM).run (t1Point (encodeT1 r)) =
      t1AlignedConfig n 0 (by
        simp [t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength])
        ((t1CS.toPhased.toTM).initialConfig
          (t1Point (encodeT1 r))).tape .startMutation :=
  t1CS_run_encoded_reaches_mutation r

end Pnp3.Tests.TMTrueUniformSeekSurface
