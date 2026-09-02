import Complexity.TMVerifier.TuringToolkit.GateNFrameShuttle

/-!
# GN-E2-2 boundary-image GNM shuttle owner surface (2026-09-02)

Definition/constructor pins and direct full-proposition wrappers for the
image capstones, body-identity corollaries, exact boundary rows, raw rejection
laws, and literal probes.
-/

namespace Pnp3.Tests.TMGateNFrameShuttleSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly

#check @GNInstallMode
#check @GNInstallMode.probe
#check @GNInstallMode.turnBack
#check @GNInstallMode.mark
#check @GNInstallMode.seek
#check @GNInstallMode.destinationTurn
#check @GNInstallMode.destination
#check @GNInstallMode.reverse
#check @GNInstallMode.reverseStop
#check @GNInstallMode.restore
#check @GNInstallMode.exit
#check @GNInstallMode.reject
#check @GNInstallBuffer
#check @GNInstallBuffer.p0
#check @GNInstallBuffer.p1
#check @GNInstallBuffer.p2
#check @GNInstallBuffer.p3
#check @GNInstallBuffer.r3
#check @GNInstallBuffer.r2
#check @GNInstallBuffer.r1
#check @GNInstallBuffer.r0
#check @GNInstallAux
#check @GNInstallAux.empty
#check @GNInstallAux.carried
#check @GNInstallAux.frame
#check @GNState.install
#check @gnInstallLatch
#check @gnInstallBit0
#check @gnInstallBit1
#check @gnInstallBit2
#check @gnInstallBit3
#check @gnInstallImage
#check @gnInstallImageBit0
#check @gnInstallImageBit1
#check @gnInstallImageBit2
#check @gnInstallImageBit3
#check @GNInstallBody
#check @GNInstallAdmissible
#check @gnInstallControl
#check @GNInstallForward
#check @gnInstallAdvance
#check @gnInstallComplete
#check @GNInstallReverseStop
#check @GNInstallReverse
#check @gnInstallRevAdvance
#check @gnInstallRevComplete
#check @gnInstallExitState
#check @gnInstallCore
#check @gnCopyShuttle
#check @gnCopyLiteralInput
#check @gnCopyLiteralOutput
#synth Fintype GNInstallMode
#synth DecidableEq GNInstallMode
#synth Fintype GNInstallBuffer
#synth DecidableEq GNInstallBuffer
#synth Fintype GNInstallAux
#synth DecidableEq GNInstallAux

theorem check_gnInstallImage_laws :
    gnInstallImage .cursor = .bof ∧
      gnInstallImage .finish = .separator ∧
      (∀ frame, GNInstallBody frame → gnInstallImage frame = frame) ∧
      (∀ frame, GNInstallAdmissible frame →
        gnInstallImage frame ≠ .blank ∧
          gnInstallImage frame ≠ .output true) :=
  gnInstallImage_laws

theorem check_gnCS_copyShuttle_onList (n : Nat) (pre : List G1Frame)
    (f : G1Frame) (middle rest : List G1Frame) (a : GNInstallAux)
    (hsource : f ≠ .blank ∧ f ≠ .output true)
    (hmiddle : ∀ g ∈ middle, g ≠ .blank ∧ g ≠ .output true)
    (hsafe : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n
          omega)
          (frameListTape
            ((pre ++ f :: middle ++ .blank :: rest).flatMap G1Frame.bits))
          (.install .probe .p0 a))
        (8 * middle.length + 29) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n
        omega)
        (frameListTape
          ((pre ++ f :: middle ++ gnInstallImage f :: rest).flatMap
            G1Frame.bits))
        gnInstallExitState :=
  gnCS_copyShuttle_onList n pre f middle rest a hsource hmiddle hsafe

theorem check_gnCS_copyShuttle_nextBlank (n : Nat) (pre : List G1Frame)
    (f : G1Frame) (middle rest : List G1Frame) (a : GNInstallAux)
    (hsource : f ≠ .blank ∧ f ≠ .output true)
    (hmiddle : ∀ g ∈ middle, g ≠ .blank ∧ g ≠ .output true)
    (hsafe : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n
          omega)
          (frameListTape ((pre ++ f :: middle ++ .blank :: .blank :: rest).flatMap
            G1Frame.bits)) (.install .probe .p0 a))
        (8 * middle.length + 29) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n
        omega)
        (frameListTape
          ((pre ++ f :: middle ++ gnInstallImage f :: .blank :: rest).flatMap
            G1Frame.bits)) gnInstallExitState :=
  gnCS_copyShuttle_nextBlank n pre f middle rest a hsource hmiddle hsafe

theorem check_gnCS_copyShuttle_body_onList (n : Nat) (pre : List G1Frame)
    (f : G1Frame) (middle rest : List G1Frame) (a : GNInstallAux)
    (hbody : GNInstallBody f)
    (hmiddle : ∀ g ∈ middle, g ≠ .blank ∧ g ≠ .output true)
    (hsafe : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n
          omega)
          (frameListTape
            ((pre ++ f :: middle ++ .blank :: rest).flatMap G1Frame.bits))
          (.install .probe .p0 a))
        (8 * middle.length + 29) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n
        omega)
        (frameListTape
          ((pre ++ f :: middle ++ f :: rest).flatMap G1Frame.bits))
        gnInstallExitState :=
  gnCS_copyShuttle_body_onList n pre f middle rest a hbody hmiddle hsafe

theorem check_gnCS_copyShuttle_body_nextBlank (n : Nat)
    (pre : List G1Frame) (f : G1Frame) (middle rest : List G1Frame)
    (a : GNInstallAux) (hbody : GNInstallBody f)
    (hmiddle : ∀ g ∈ middle, g ≠ .blank ∧ g ≠ .output true)
    (hsafe : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n
          omega)
          (frameListTape
            ((pre ++ f :: middle ++ .blank :: .blank :: rest).flatMap
              G1Frame.bits)) (.install .probe .p0 a))
        (8 * middle.length + 29) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n
        omega)
        (frameListTape
          ((pre ++ f :: middle ++ f :: .blank :: rest).flatMap G1Frame.bits))
        gnInstallExitState :=
  gnCS_copyShuttle_body_nextBlank n pre f middle rest a hbody hmiddle hsafe

theorem check_gnTransition_install_cursor_destination_restore
    (phase : Fin 1) (scan : Bool) :
    gnTransition phase
        (.install .destination (.p3 false false false) (.carried .cursor)) scan =
        (0, .install .destination (.p2 false false) (.carried .cursor),
          true, .left) ∧
      gnTransition phase
        (.install .destination (.p2 false false) (.carried .cursor)) scan =
        (0, .install .destination (.p1 false) (.carried .cursor),
          false, .left) ∧
      gnTransition phase
        (.install .destination (.p1 false) (.carried .cursor)) scan =
        (0, .install .destination .p0 (.carried .cursor), false, .left) ∧
      gnTransition phase
        (.install .destination .p0 (.carried .cursor)) scan =
        (0, .install .reverse .r3 (.carried .cursor), false, .left) ∧
      gnTransition phase
        (.install .reverseStop .p0 (.carried .cursor)) scan =
        (0, .install .restore (.p1 false) (.carried .cursor), false, .right) ∧
      gnTransition phase
        (.install .restore (.p1 false) (.carried .cursor)) scan =
        (0, .install .restore (.p2 false true) (.carried .cursor), true, .right) ∧
      gnTransition phase
        (.install .restore (.p2 false true) (.carried .cursor)) scan =
        (0, .install .restore (.p3 false true true) (.carried .cursor),
          true, .right) ∧
      gnTransition phase
        (.install .restore (.p3 false true true) (.carried .cursor)) scan =
        (0, .install .exit .p0 .empty, true, .right) :=
  gnTransition_install_cursor_destination_restore phase scan

theorem check_gnTransition_install_finish_destination_restore
    (phase : Fin 1) (scan : Bool) :
    gnTransition phase
        (.install .destination (.p3 false false false) (.carried .finish)) scan =
        (0, .install .destination (.p2 false false) (.carried .finish),
          false, .left) ∧
      gnTransition phase
        (.install .destination (.p2 false false) (.carried .finish)) scan =
        (0, .install .destination (.p1 false) (.carried .finish),
          false, .left) ∧
      gnTransition phase
        (.install .destination (.p1 false) (.carried .finish)) scan =
        (0, .install .destination .p0 (.carried .finish), true, .left) ∧
      gnTransition phase
        (.install .destination .p0 (.carried .finish)) scan =
        (0, .install .reverse .r3 (.carried .finish), false, .left) ∧
      gnTransition phase
        (.install .reverseStop .p0 (.carried .finish)) scan =
        (0, .install .restore (.p1 true) (.carried .finish), true, .right) ∧
      gnTransition phase
        (.install .restore (.p1 true) (.carried .finish)) scan =
        (0, .install .restore (.p2 true false) (.carried .finish), false, .right) ∧
      gnTransition phase
        (.install .restore (.p2 true false) (.carried .finish)) scan =
        (0, .install .restore (.p3 true false true) (.carried .finish),
          true, .right) ∧
      gnTransition phase
        (.install .restore (.p3 true false true) (.carried .finish)) scan =
        (0, .install .exit .p0 .empty, false, .right) :=
  gnTransition_install_finish_destination_restore phase scan

theorem check_gnTransition_install_forward_none (phase : Fin 1)
    (mode : GNInstallMode) (aux : GNInstallAux) (b0 b1 b2 b3 : Bool)
    (hmode : mode = .probe ∨ mode = .seek)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    gnTransition phase (.install mode (.p3 b0 b1 b2) aux) b3 =
      (0, .reject, b3, .stay) :=
  gnTransition_install_forward_none phase mode aux b0 b1 b2 b3 hmode hbad

theorem check_gnTransition_install_reverse_none (phase : Fin 1)
    (aux : GNInstallAux) (b0 b1 b2 b3 : Bool)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    gnTransition phase (.install .reverse (.r0 b1 b2 b3) aux) b0 =
      (0, .reject, b0, .stay) :=
  gnTransition_install_reverse_none phase aux b0 b1 b2 b3 hbad

theorem check_gnTransition_install_reserved (phase : Fin 1)
    (aux : GNInstallAux) :
    (∀ mode, mode = GNInstallMode.probe ∨ mode = .seek →
      gnTransition phase (.install mode (.p3 true true false) aux) true =
        (0, .reject, true, .stay)) ∧
    (∀ mode, mode = GNInstallMode.probe ∨ mode = .seek →
      gnTransition phase (.install mode (.p3 true true true) aux) false =
        (0, .reject, false, .stay) ∧
      gnTransition phase (.install mode (.p3 true true true) aux) true =
        (0, .reject, true, .stay)) ∧
    gnTransition phase (.install .reverse (.r0 true false true) aux) true =
      (0, .reject, true, .stay) ∧
    gnTransition phase (.install .reverse (.r0 true true false) aux) true =
      (0, .reject, true, .stay) ∧
    gnTransition phase (.install .reverse (.r0 true true true) aux) true =
      (0, .reject, true, .stay) :=
  gnTransition_install_reserved phase aux

theorem check_gnTransition_install_marker_modes (phase : Fin 1)
    (aux : GNInstallAux) :
    gnTransition phase (.install .probe (.p3 true false false) aux) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.install .seek (.p3 true false false) aux) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.install .reverse (.r0 false false true) aux) true =
        (0, .install .reverseStop .p0 aux, true, .stay) :=
  gnTransition_install_marker_modes phase aux

theorem check_gnCS_install_reject_stable {n : Nat}
    (c : Configuration (M := GNM) n)
    (hstate : c.state = ⟨(0 : Fin 1), GNState.reject⟩) (k : Nat) :
    TM.runConfig (M := GNM) c k = c :=
  gnCS_install_reject_stable c hstate k

set_option maxRecDepth 2048 in
theorem check_gnCS_copyShuttle_tag_run45 (n : Nat) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n 0 (by
          change 0 < GNM.tapeLength n
          simp [TM.tapeLength, gnCS, gnClock, g1Clock])
          (frameListTape (gnCopyLiteralInput.flatMap G1Frame.bits))
          (.install .probe .p0 .empty)) 45 =
      gnCopyShuttle.cfg n 4 (by
        change 4 < GNM.tapeLength n
        simp [TM.tapeLength, gnCS, gnClock, g1Clock]
        omega)
        (frameListTape (gnCopyLiteralOutput.flatMap G1Frame.bits))
        gnInstallExitState :=
  gnCS_copyShuttle_tag_run45 n

set_option maxRecDepth 2048 in
theorem check_gnCS_copyShuttle_cursor_run37 (n : Nat) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n 0 (by
          change 0 < GNM.tapeLength n
          simp [TM.tapeLength, gnCS, gnClock, g1Clock])
          (frameListTape
            ([.cursor, .tag, .blank, .blank].flatMap G1Frame.bits))
          (.install .probe .p0 .empty)) 37 =
      gnCopyShuttle.cfg n 4 (by
        change 4 < GNM.tapeLength n
        simp [TM.tapeLength, gnCS, gnClock, g1Clock]
        omega)
        (frameListTape ([.cursor, .tag, .bof, .blank].flatMap G1Frame.bits))
        gnInstallExitState :=
  gnCS_copyShuttle_cursor_run37 n

set_option maxRecDepth 2048 in
theorem check_gnCS_copyShuttle_finish_run37 (n : Nat) :
    TM.runConfig (M := gnCopyShuttle.machine)
        (gnCopyShuttle.cfg n 0 (by
          change 0 < GNM.tapeLength n
          simp [TM.tapeLength, gnCS, gnClock, g1Clock])
          (frameListTape
            ([.finish, .tag, .blank, .blank].flatMap G1Frame.bits))
          (.install .probe .p0 .empty)) 37 =
      gnCopyShuttle.cfg n 4 (by
        change 4 < GNM.tapeLength n
        simp [TM.tapeLength, gnCS, gnClock, g1Clock]
        omega)
        (frameListTape
          ([.finish, .tag, .separator, .blank].flatMap G1Frame.bits))
        gnInstallExitState :=
  gnCS_copyShuttle_finish_run37 n

theorem check_gnCopyShuttle_marker_middle_rejected :
    ¬ gnCopyShuttle.core.ValidPath gnCopyShuttle.seekMode
      [.argSep, .output true, .index] :=
  gnCopyShuttle_marker_middle_rejected

end Pnp3.Tests.TMGateNFrameShuttleSurface
