import Complexity.TMVerifier.TuringToolkit.GateNBoundaryShuttle

/-!
# GN-E2-2 live boundary shuttle surface (2026-09-02)

Definitions receive direct type pins.  Every public source theorem has one
full-proposition wrapper rooted directly in that theorem; there are no inferred
aliases or Lean `example` declarations.
-/

namespace Pnp3.Tests.TMGateNBoundaryShuttleSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.GNFixedDelegateProbes

#check @gnFirstRecordProbeConfig
#check @gnBofSeedConfig
#check @gnCursorSeedSteps
#check @gnBofSeedSteps
#check @gnFirstBodyMiddle

theorem check_gnTransition_boundary_rows (phase : Fin 1) (scan : Bool) :
    gnTransition phase .firstRecord scan =
        (0, .install .probe .p0 .empty, scan, .stay) ∧
      gnTransition phase .noGate scan = (0, .noGate, scan, .stay) :=
  gnTransition_boundary_rows phase scan

theorem check_gnFirstRecord_image_request_prefix (r : GNProgram)
    (g : SLGate r.inputs.length) :
    (gnRecordFrames .cursor g).map gnInstallImage ++ r.inputs.map .data =
      g1PrefixFrames (gnFirstRequest r g) :=
  gnFirstRecord_image_request_prefix r g

theorem check_gnCS_firstRecord_to_probe_exact (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnFirstRecordConfig r g hg) 1 =
      gnFirstRecordProbeConfig r g hg :=
  gnCS_firstRecord_to_probe_exact r g hg

theorem check_gnBofSeedSteps_provenance (r : GNProgram) :
    gnBofSeedSteps r =
      ((encodeGN r).length + 9) +
        (1 + 4 * (gnFirstRecordMiddle r).length + 4) +
        (1 + (8 * (gnFirstRecordMiddle r).length + 29)) :=
  gnBofSeedSteps_provenance r

theorem check_gnCS_firstRecord_to_bofSeed_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnFirstRecordConfig r g hg)
        (gnCursorSeedSteps r) = gnBofSeedConfig r g hg :=
  gnCS_firstRecord_to_bofSeed_exact hg

theorem check_gnCS_encodeGN_bofSeed_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r))) (gnBofSeedSteps r) =
      gnBofSeedConfig r g hg :=
  gnCS_encodeGN_bofSeed_exact hg

theorem check_gnBofSeedConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnBofSeedConfig r g hg).state =
        ⟨(0 : Fin 1), gnInstallExitState (.carried .cursor)⟩ ∧
      ((gnBofSeedConfig r g hg).head : Nat) = 4 * (gnRecordsStart r + 1) ∧
      (gnBofSeedConfig r g hg).tape = frameListTape
        ((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
          [G1Frame.bof, G1Frame.blank]).flatMap G1Frame.bits) ∧
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r =
        encodeGNFrames r :=
  gnBofSeedConfig_structure hg

theorem check_gnBofSeed_firstBody_handoff {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordMiddle r = G1Frame.tag :: (gnFirstRecordMiddle r).drop 1 ∧
      (gnBofSeedConfig r g hg).tape = frameListTape
        (((gnLocatePrefix r ++ [G1Frame.cursor]) ++
          G1Frame.tag :: gnFirstBodyMiddle r ++ [G1Frame.blank]).flatMap
            G1Frame.bits) ∧
      GNInstallBody G1Frame.tag ∧
      (∀ frame ∈ gnFirstBodyMiddle r, GNInstallAdmissible frame) ∧
      4 * ((gnLocatePrefix r ++ [G1Frame.cursor]).length +
        (gnFirstBodyMiddle r).length + 2) <
          GNM.tapeLength (encodeGN r).length :=
  gnBofSeed_firstBody_handoff hg

theorem check_gnBofSeedSteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnBofSeedSteps r ≤ gnClock (encodeGN r).length :=
  gnBofSeedSteps_le_gnClock hg

theorem check_gnCS_firstRecord_reserved1101_reject_five (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape
          .firstRecord) 5 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape
        .reject :=
  gnCS_firstRecord_reserved1101_reject_five n base hsafe tape hbits

theorem check_gnCS_firstRecord_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape
          .firstRecord) (5 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape
        .reject :=
  gnCS_firstRecord_reserved1101_reject_stable n base hsafe tape hbits k

theorem check_literal_oneConstFalse_bofSeed :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 188 =
      gnBofSeedConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0) (by rfl) ∧
    ((gnBofSeedConfig oneConstFalseProgram
      (SLGate.const false : SLGate 0) (by rfl)).head : Nat) = 16 :=
  GNBoundaryShuttleProbes.literal_oneConstFalse_bofSeed

end Pnp3.Tests.TMGateNBoundaryShuttleSurface
