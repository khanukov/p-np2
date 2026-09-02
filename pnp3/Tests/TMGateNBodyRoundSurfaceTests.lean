import Complexity.TMVerifier.TuringToolkit.GateNBodyRound

/-!
# GN-E2-3a body-round surface (2026-09-02)

Definition/constructor pins and one direct full-proposition wrapper for every
public theorem.  Private dispatcher glue is deliberately excluded.
-/

namespace Pnp3.Tests.TMGateNBodyRoundSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.GNFixedDelegateProbes

#check @GNState.recordDone
#check @gnInstallExitState
#check @GNInstallExitContinue
#check @GNInstallExitInvalid
#check @gnInstallExitDispatch
#check @GNBodyRoundSource
#check @gnBodyRoundMiddle
#check @gnBodyRoundFrames
#check @GNBodyRoundInvariant
#check @GNBodyRoundInvariant.mk
#check @GNBodyRoundInvariant.previous_continue
#check @GNBodyRoundInvariant.source
#check @GNBodyRoundInvariant.middle_admissible
#check @GNBodyRoundInvariant.room
#check @gnBodyRoundConfig
#check @gnBodyRoundSteps
#check @gnBodyTerminalSteps
#check @GNBodyRoundProbes.oneConstFalseTagConfig
#synth Fintype GNState
#synth DecidableEq GNState

theorem check_gnTransition_install_exit_dispatch (phase : Fin 1)
    (scan : Bool) :
    (∀ aux, GNInstallExitContinue aux →
      gnTransition phase (gnInstallExitState aux) scan =
        (0, .install .probe .p0 .empty, scan, .stay)) ∧
    gnTransition phase (gnInstallExitState (.carried .finish)) scan =
      (0, .recordDone, scan, .stay) ∧
    (∀ aux, GNInstallExitInvalid aux →
      gnTransition phase (gnInstallExitState aux) scan =
        (0, .reject, scan, .stay)) ∧
    (∀ buffer aux, buffer ≠ GNInstallBuffer.p0 →
      gnTransition phase (.install .exit buffer aux) scan =
        (0, .reject, scan, .stay)) :=
  gnTransition_install_exit_dispatch phase scan

theorem check_gnBodyRoundConfig_structure (n : Nat)
    (fixed done : List G1Frame) (current : G1Frame)
    (todo seed rest : List G1Frame) (previous : GNInstallAux)
    (hroom : 4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done todo seed).length + 2) < GNM.tapeLength n) :
    (gnBodyRoundConfig n fixed done current todo seed rest previous hroom).state =
        ⟨(0 : Fin 1), gnInstallExitState previous⟩ ∧
      ((gnBodyRoundConfig n fixed done current todo seed rest previous hroom).head :
        Nat) = 4 * (fixed ++ done).length ∧
      (gnBodyRoundConfig n fixed done current todo seed rest previous hroom).tape =
        frameListTape
          ((gnBodyRoundFrames fixed done current todo seed rest).flatMap
            G1Frame.bits) :=
  gnBodyRoundConfig_structure n fixed done current todo seed rest previous hroom

theorem check_gnBodyRoundSteps_provenance (distance : Nat) :
    gnBodyRoundSteps distance = 1 + (8 * distance + 29) ∧
      gnBodyTerminalSteps distance = gnBodyRoundSteps distance + 1 :=
  gnBodyRoundSteps_provenance distance

theorem check_gnBodyRoundMiddle_length_constant
    (done later seed : List G1Frame) (current next : G1Frame) :
    (gnBodyRoundMiddle done (next :: later) seed).length =
      (gnBodyRoundMiddle (done ++ [current]) later seed).length :=
  gnBodyRoundMiddle_length_constant done later seed current next

theorem check_gnCS_bodyRound_exact (n : Nat) (fixed done : List G1Frame)
    (current : G1Frame) (todo seed rest : List G1Frame)
    (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done current todo seed previous)
    (hbody : GNInstallBody current) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done current todo seed rest previous hinv.room)
        (gnBodyRoundSteps (gnBodyRoundMiddle done todo seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ done).length + 4) (by
          change 4 * (fixed ++ done).length + 4 < GNM.tapeLength n
          have h := hinv.room
          omega)
        (frameListTape
          (((fixed ++ done) ++ current ::
            gnBodyRoundMiddle done todo seed ++
              gnInstallImage current :: .blank :: rest).flatMap G1Frame.bits))
        (gnInstallExitState (.carried current)) :=
  gnCS_bodyRound_exact n fixed done current todo seed rest previous hinv hbody

theorem check_gnCS_bodyRound_iteration_exact (n : Nat)
    (fixed done : List G1Frame) (current next : G1Frame)
    (later seed : List G1Frame) (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done current (next :: later) seed
      previous)
    (hbody : GNInstallBody current)
    (hnextRoom : 4 * ((fixed ++ (done ++ [current])).length +
      (gnBodyRoundMiddle (done ++ [current]) later seed).length + 2) <
        GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done current (next :: later) seed []
          previous hinv.room)
        (gnBodyRoundSteps
          (gnBodyRoundMiddle done (next :: later) seed).length) =
      gnBodyRoundConfig n fixed (done ++ [current]) next later seed []
        (.carried current) hnextRoom :=
  gnCS_bodyRound_iteration_exact n fixed done current next later seed previous
    hinv hbody hnextRoom

theorem check_gnCS_bodyFinishRound_exact (n : Nat)
    (fixed done : List G1Frame) (todo seed rest : List G1Frame)
    (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done .finish todo seed previous) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done .finish todo seed rest previous hinv.room)
        (gnBodyRoundSteps (gnBodyRoundMiddle done todo seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ done).length + 4) (by
          change 4 * (fixed ++ done).length + 4 < GNM.tapeLength n
          have h := hinv.room
          omega)
        (frameListTape
          (((fixed ++ done) ++ G1Frame.finish ::
            gnBodyRoundMiddle done todo seed ++
              G1Frame.separator :: .blank :: rest).flatMap G1Frame.bits))
        (gnInstallExitState (.carried .finish)) :=
  gnCS_bodyFinishRound_exact n fixed done todo seed rest previous hinv

theorem check_gnCS_finishExit_to_recordDone_one (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape
          (gnInstallExitState (.carried .finish))) 1 =
      gnCopyShuttle.cfg n head hhead tape .recordDone :=
  gnCS_finishExit_to_recordDone_one n head hhead tape

theorem check_gnCS_bodyFinishRound_recordDone_exact (n : Nat)
    (fixed done : List G1Frame) (todo seed rest : List G1Frame)
    (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done .finish todo seed previous) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done .finish todo seed rest previous hinv.room)
        (gnBodyTerminalSteps (gnBodyRoundMiddle done todo seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ done).length + 4) (by
          change 4 * (fixed ++ done).length + 4 < GNM.tapeLength n
          have h := hinv.room
          omega)
        (frameListTape
          (((fixed ++ done) ++ G1Frame.finish ::
            gnBodyRoundMiddle done todo seed ++
              G1Frame.separator :: .blank :: rest).flatMap G1Frame.bits))
        .recordDone :=
  gnCS_bodyFinishRound_recordDone_exact n fixed done todo seed rest previous hinv

theorem check_gnCS_install_exit_invalid_reject_one (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (aux : GNInstallAux)
    (hinvalid : GNInstallExitInvalid aux) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape (gnInstallExitState aux)) 1 =
      gnCopyShuttle.cfg n head hhead tape .reject :=
  gnCS_install_exit_invalid_reject_one n head hhead tape aux hinvalid

theorem check_gnCS_install_exit_badBuffer_reject_one (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (buffer : GNInstallBuffer)
    (aux : GNInstallAux) (hbuffer : buffer ≠ .p0) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape (.install .exit buffer aux)) 1 =
      gnCopyShuttle.cfg n head hhead tape .reject :=
  gnCS_install_exit_badBuffer_reject_one n head hhead tape buffer aux hbuffer

theorem check_gnCS_install_exit_reserved1101_reject_five (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true])
    (aux : GNInstallAux) (haux : GNInstallExitContinue aux) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape (gnInstallExitState aux)) 5 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape .reject :=
  gnCS_install_exit_reserved1101_reject_five n base hsafe tape hbits aux haux

theorem check_gnCS_install_exit_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true])
    (aux : GNInstallAux) (haux : GNInstallExitContinue aux) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape (gnInstallExitState aux)) (5 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape .reject :=
  gnCS_install_exit_reserved1101_reject_stable n base hsafe tape hbits aux haux k

theorem check_gnBodyTerminalSteps_le_gnClock {n distance : Nat}
    (hspan : 4 * (distance + 2) ≤ n) :
    gnBodyTerminalSteps distance ≤ gnClock n :=
  gnBodyTerminalSteps_le_gnClock hspan

theorem check_literal_oneConstFalse_tagRound :
    TM.runConfig (M := GNM)
        (gnBofSeedConfig oneConstFalseProgram
          (SLGate.const false : SLGate 0) (by rfl)) 94 =
      GNBodyRoundProbes.oneConstFalseTagConfig ∧
    (GNBodyRoundProbes.oneConstFalseTagConfig.head : Nat) = 20 ∧
    GNBodyRoundProbes.oneConstFalseTagConfig.state =
      ⟨(0 : Fin 1), gnInstallExitState (.carried .tag)⟩ ∧
    GNBodyRoundProbes.oneConstFalseTagConfig.tape = frameListTape
      ([G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
        .argSep, .argSep, .finish, .separator, .output false, .finish,
        .bof, .tag, .blank].flatMap G1Frame.bits) :=
  GNBodyRoundProbes.literal_oneConstFalse_tagRound

end Pnp3.Tests.TMGateNBodyRoundSurface
