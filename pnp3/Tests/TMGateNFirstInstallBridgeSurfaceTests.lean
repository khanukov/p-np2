import Complexity.TMVerifier.TuringToolkit.GateNFirstInstallBridge

/-!
# GN-E2-0 pure physical first-install bridge surface (2026-09-01)

Definitions and concrete configurations receive `#check` pins.  Every public
source theorem has a direct wrapper with an explicit proposition; this file
contains no inferred aliases and no Lean `example` declarations.
-/

namespace Pnp3.Tests.TMGateNFirstInstallBridgeSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.GNFixedDelegateProbes
open Pnp3.Internal.PsubsetPpoly.TM.G1AResultProbes

#check @gnStageTape
#check @GateNPhysicalTapeState
#check @gnFirstRequest
#check @gnFirstInstalledConfig
#check @gnFirstInstalledPhysicalConfig

theorem check_gnStageWord_length (r : GNProgram) (prior : List Bool)
    (hfit : prior.length ≤ gnOutputSlotsLength r) :
    (encodeGNAt r prior).length = (encodeGN r).length :=
  gnStageWord_length r prior hfit

theorem check_gnStageTape_zero (r : GNProgram) :
    gnStageTape r [] = (GNM.initialConfig (gnPoint (encodeGN r))).tape :=
  gnStageTape_zero r

theorem check_gnStageTape_cell (r : GNProgram) (prior : List Bool)
    (i : Fin (GNM.tapeLength (encodeGN r).length))
    (hi : i.val < (encodeGNAt r prior).length) :
    gnStageTape r prior i = (encodeGNAt r prior)[i.val] :=
  gnStageTape_cell r prior i hi

theorem check_gnStageTape_outside_blank (r : GNProgram) (prior : List Bool)
    (i : Fin (GNM.tapeLength (encodeGN r).length))
    (hi : (encodeGNAt r prior).length ≤ i.val) :
    gnStageTape r prior i = false :=
  gnStageTape_outside_blank r prior i hi

theorem check_GateNTapeState_physical_tape_eq {r : GNProgram}
    {prior : List Bool} {fs : List G1Frame}
    (h : GateNTapeState r prior fs) :
    frameListTape (L := GNM.tapeLength (encodeGN r).length)
        (fs.flatMap G1Frame.bits) = gnStageTape r prior :=
  h.physical_tape_eq

theorem check_GateNTapeState_toPhysical {r : GNProgram}
    {prior : List Bool} {fs : List G1Frame}
    (h : GateNTapeState r prior fs) :
    GateNPhysicalTapeState r prior
      (frameListTape (L := GNM.tapeLength (encodeGN r).length)
        (fs.flatMap G1Frame.bits)) :=
  h.toPhysical

theorem check_gnScratchEntryConfig_stage_zero (r : GNProgram) :
    (gnScratchEntryConfig r).state = gnScratchEntryQ ∧
      ((gnScratchEntryConfig r).head : Nat) = (encodeGN r).length ∧
      (gnScratchEntryConfig r).tape = gnStageTape r [] :=
  gnScratchEntryConfig_stage_zero r

theorem check_gnScratchEntryConfig_physical_state (r : GNProgram) :
    GateNPhysicalTapeState r [] (gnScratchEntryConfig r).tape :=
  gnScratchEntryConfig_physical_state r

theorem check_gnCurrentValues_zero (r : GNProgram) :
    gnCurrentValues r [] = r.inputs :=
  gnCurrentValues_zero r

theorem check_gnWorkRequest?_zero {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnWorkRequest? r [] = some (gnFirstRequest r g) :=
  gnWorkRequest?_zero hg

theorem check_gnFirstRequest_canonical (r : GNProgram)
    (g : SLGate r.inputs.length) : (gnFirstRequest r g).Canonical :=
  gnFirstRequest_canonical r g

theorem check_gnFirstRequest_width (r : GNProgram)
    (g : SLGate r.inputs.length) :
    (encodeG1 (gnFirstRequest r g)).length =
      4 * (gnRecordSize (gnGateFields g) + r.inputs.length + 2) :=
  gnFirstRequest_width r g

theorem check_gnFirstRequest_add_sixteen_le {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (encodeG1 (gnFirstRequest r g)).length + 16 ≤ (encodeGN r).length :=
  gnFirstRequest_add_sixteen_le hg

theorem check_gnFirstRequest_room {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (encodeGN r).length + gnLocalSpan (encodeG1 (gnFirstRequest r g)).length ≤
      GNM.tapeLength (encodeGN r).length :=
  gnFirstRequest_room hg

theorem check_encodeGNAtFrames_zero_first_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    encodeGNAtFrames r [] =
      [.bof] ++ r.inputs.map .data ++ gnSlotFrames (gnOutputSlotsLength r) ++
        [.separator] ++ gnRecordFrames .cursor g ++
        gnUniformRecordsFrames .bof (r.program.gates.drop 1) ++
        gnFinalTail false :=
  encodeGNAtFrames_zero_first_split hg

theorem check_encodeGNAtFrames_zero_cursor_unique {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnRecordsAtFrames 0 r.program.gates).count .cursor = 1 :=
  encodeGNAtFrames_zero_cursor_unique hg

theorem check_encodeGNAtFrames_zero_no_spent (r : GNProgram) :
    (gnRecordsAtFrames 0 r.program.gates).count .spent = 0 :=
  encodeGNAtFrames_zero_no_spent r

theorem check_encodeG1Frames_first_no_internal_markers (r : GNProgram)
    (g : SLGate r.inputs.length) :
    (encodeG1Frames (gnFirstRequest r g)).count .cursor = 0 ∧
      (encodeG1Frames (gnFirstRequest r g)).count .spent = 0 :=
  encodeG1Frames_first_no_internal_markers r g

theorem check_gnFirstInstalledConfig_eq_physical {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstInstalledConfig r g hg = gnFirstInstalledPhysicalConfig r g :=
  gnFirstInstalledConfig_eq_physical hg

theorem check_gnFirstInstalledPhysicalConfig_structure (r : GNProgram)
    (g : SLGate r.inputs.length) :
    let q := gnFirstRequest r g
    let N := (encodeGN r).length
    let W := (encodeG1 q).length
    (gnFirstInstalledPhysicalConfig r g).state =
        gnEmbed (G1M.initialConfig (g1Point (encodeG1 q))).state ∧
      ((gnFirstInstalledPhysicalConfig r g).head : Nat) = N ∧
      (gnFirstInstalledPhysicalConfig r g).tape =
        frameListTape (encodeGN r ++ encodeG1 q) ∧
      (∀ i : Fin (GNM.tapeLength N), i.val < N →
        (gnFirstInstalledPhysicalConfig r g).tape i =
          (GNM.initialConfig (gnPoint (encodeGN r))).tape i) ∧
      (∀ (i : Fin (GNM.tapeLength N))
        (hi : N ≤ i.val ∧ i.val < N + W),
        (gnFirstInstalledPhysicalConfig r g).tape i =
          (encodeG1 q).get ⟨i.val - N, by omega⟩) ∧
      (∀ i : Fin (GNM.tapeLength N), N + W ≤ i.val → i.val < N + W + 5 →
        (gnFirstInstalledPhysicalConfig r g).tape i = false) ∧
      (∀ i : Fin (GNM.tapeLength N),
        (i.val < N ∨ N + W + 5 ≤ i.val) →
        (gnFirstInstalledPhysicalConfig r g).tape i =
          (GNM.initialConfig (gnPoint (encodeGN r))).tape i) :=
  gnFirstInstalledPhysicalConfig_structure r g

theorem check_oneConstFalse_first_gate :
    oneConstFalseProgram.program.gates[0]? =
      some (SLGate.const false : SLGate 0) :=
  GNFirstInstallProbes.oneConstFalse_first_gate

theorem check_oneConstFalse_first_request :
    gnFirstRequest oneConstFalseProgram (SLGate.const false : SLGate 0) =
      reqConstF :=
  GNFirstInstallProbes.oneConstFalse_first_request

theorem check_oneConstFalse_width_room :
    (encodeGN oneConstFalseProgram).length = 48 ∧
      (encodeG1 (gnFirstRequest oneConstFalseProgram
        (SLGate.const false : SLGate 0))).length = 32 ∧
      48 + gnLocalSpan 32 ≤ GNM.tapeLength 48 :=
  GNFirstInstallProbes.oneConstFalse_width_room

theorem check_oneConstFalse_installed_physical :
    gnFirstInstalledConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0)
        GNFirstInstallProbes.oneConstFalse_first_gate =
      gnFirstInstalledPhysicalConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0) :=
  GNFirstInstallProbes.oneConstFalse_installed_physical

theorem check_empty_no_first_gate : emptyProgram.program.gates[0]? = none :=
  GNFirstInstallProbes.empty_no_first_gate

end Pnp3.Tests.TMGateNFirstInstallBridgeSurface
