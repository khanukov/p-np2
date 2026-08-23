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

theorem check_decodeT1Tape?_eq_some {bits : List Bool} {r : T1Request}
    (h : decodeT1Tape? bits = some r) : bits = encodeT1 r :=
  decodeT1Tape?_eq_some h

theorem check_t1CS_runTime (N : Nat) :
    t1CS.toPhased.toTM.runTime N = 128 * (N + 1) ^ 2 + 128 :=
  t1CS_runTime N

theorem check_t1CS_frame_macrostep
    (n h : Nat) (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (mode : T1Mode) (frame : T1Frame)
    (hmode : T1ForwardMode mode)
    (hnext : t1Advance mode frame ≠ .reject)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape mode) 4 =
      t1AlignedConfig n (h+4) hsafe tape (t1Advance mode frame) :=
  t1CS_frame_macrostep n h hsafe tape mode frame hmode hnext hbits

theorem check_t1CS_scan_frames
    (n : Nat) (pre frames suffix : List T1Frame) (mode : T1Mode)
    (hpath : T1ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < T1M.tapeLength n) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * pre.length) (by omega)
          (t1ListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits)) mode)
        (4 * frames.length) =
      t1AlignedConfig n (4 * (pre.length + frames.length)) hsafe
        (t1ListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits))
        (t1AdvanceList mode frames) :=
  t1CS_scan_frames n pre frames suffix mode hpath hsafe

theorem check_t1CanonicalEncoderAutomatonTrace (r : T1Request) :
    T1ValidPath .validateBof (encodeT1Frames r ++ [.blank]) ∧
      t1AdvanceList .validateBof (encodeT1Frames r ++ [.blank]) =
        .rewindStart :=
  t1CanonicalEncoderAutomatonTrace r

theorem check_t1CS_rewind_tail
    (n : Nat) (tail suffix : List T1Frame)
    (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < T1M.tapeLength n) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
          .rewind .p3) (4 * tail.length) =
      t1AlignedConfig n 3 (by omega)
        (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
        .rewind .p3 :=
  t1CS_rewind_tail n tail suffix hne hsafe

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

-- T1b-A1 fixed-control and generic-step reuse surfaces.
#check @t1Transition_startMutation_active
#check @t1Transition_probeData_p3_data
#check @t1Transition_probeData_p3_oob
#check @t1Transition_writeCursor
#check @t1Transition_seekIndexBack_p0_mark
#check @t1Transition_markSpent
#check @t1Transition_backupCursor
#check @t1Transition_writeData
#check @t1MutationFrames_length
#check @t1MutationFrames_zero
#check @t1CS_aligned_step_right
#check @t1CS_aligned_step_left
#check @t1CS_aligned_step_stay
#check @t1CS_runConfig_successStart
#check @t1CS_runConfig_oobStart

end Pnp3.Tests.TMTrueUniformSeekSurface
