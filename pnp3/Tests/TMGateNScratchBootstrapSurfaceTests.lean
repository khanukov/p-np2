import Complexity.TMVerifier.TuringToolkit.GateNScratchBootstrap

/-!
# GN-E2-1c live scratch-bootstrap surface (2026-09-02)

Constructor/definition/instance pins and direct full-proposition wrappers for
the strict reverse grammar, exact read-only endpoints, rejection rows,
schedule/clock facts, E2-2 premise package, and literal real-initial runs.
-/

namespace Pnp3.Tests.TMGateNScratchBootstrapSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

#check @GNLocateMode
#check @GNLocateMode.tailFinish
#check @GNLocateMode.tailOutput
#check @GNLocateMode.tailSeparator
#check @GNLocateMode.recordEdge
#check @GNLocateMode.moreRecord
#check @GNLocateMode.arg2
#check @GNLocateMode.arg1
#check @GNLocateMode.tag0
#check @GNLocateMode.tag1
#check @GNLocateMode.tag2
#check @GNLocateMode.tag3
#check @GNLocateMode.tag4
#check @GNLocateMode.tag5
#check @GNLocateMode.firstRecord
#check @GNLocateMode.noGate
#check @GNLocateMode.reject
#check @GNLocateBuffer
#check @GNLocateBuffer.r3
#check @GNLocateBuffer.r2
#check @GNLocateBuffer.r1
#check @GNLocateBuffer.r0
#check @GNLocateState
#check @GNLocateState.mk
#check @GNLocateState.mode
#check @GNLocateState.buffer
#check @GNState.locating
#check @GNState.firstRecord
#check @GNState.noGate
#synth Fintype GNLocateMode
#synth DecidableEq GNLocateMode
#synth Repr GNLocateMode
#synth Fintype GNLocateBuffer
#synth DecidableEq GNLocateBuffer
#synth Repr GNLocateBuffer
#synth Fintype GNLocateState
#synth DecidableEq GNLocateState
#synth Repr GNLocateState

#check @GNLocateMode.Stop
#check @GNLocateMode.Reverse
#check @gnLocateAdvance
#check @gnLocateComplete
#check @GNLocateRevPathFrom
#check @GNLocateRevValidPath
#check @gnLocateAdvanceList
#check @gnLocatePrefix
#check @gnFirstRecordInner
#check @gnFirstRecordMiddle
#check @gnLocateStopState
#check @gnLocateScanner
#check @gnFirstRecordQ
#check @gnNoGateQ
#check @gnFirstRecordConfig
#check @gnNoGateConfig
#check @gnFirstRecordLocateSteps
#check @gnFirstRecordSteps
#check @gnNoGateLocateSteps
#check @gnNoGateSteps

theorem check_gnLocateComplete_reserved (mode : GNLocateMode) :
    gnLocateComplete mode true true false true = .reject ∧
      gnLocateComplete mode true true true false = .reject ∧
        gnLocateComplete mode true true true true = .reject :=
  gnLocateComplete_reserved mode

theorem check_gnLocateAdvance_tail_and_edge :
    gnLocateAdvance .tailFinish .finish = .tailOutput ∧
      gnLocateAdvance .tailOutput (.output false) = .tailSeparator ∧
      gnLocateAdvance .tailSeparator .separator = .recordEdge ∧
      gnLocateAdvance .recordEdge .separator = .noGate ∧
      gnLocateAdvance .recordEdge .finish = .arg2 :=
  gnLocateAdvance_tail_and_edge

theorem check_gnLocateAdvance_stageZero_malformed :
    gnLocateAdvance .tailFinish .blank = .reject ∧
      gnLocateAdvance .tailFinish (.output false) = .reject ∧
      gnLocateAdvance .tailOutput (.output true) = .reject ∧
      gnLocateAdvance .recordEdge .blank = .reject ∧
      gnLocateAdvance .recordEdge (.data false) = .reject ∧
      gnLocateAdvance .recordEdge (.output false) = .reject ∧
      gnLocateAdvance .recordEdge (.output true) = .reject ∧
      gnLocateAdvance .recordEdge .spent = .reject :=
  gnLocateAdvance_stageZero_malformed

theorem check_encodeGNFrames_firstRecord_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    encodeGNFrames r =
        gnLocatePrefix r ++ .cursor :: gnFirstRecordInner r ++
          [.separator, .output false, .finish] ∧
      (gnLocatePrefix r).length = gnRecordsStart r ∧
      (gnFirstRecordInner r).length + 1 = gnRecordsLength r :=
  encodeGNFrames_firstRecord_split hg

theorem check_encodeGNFrames_noGate_split {r : GNProgram}
    (hg : r.program.gates = []) :
    encodeGNFrames r = [.bof] ++ gnAssignFrames r.inputs ++
      [.separator] ++ [.separator] ++ [.output false, .finish] :=
  encodeGNFrames_noGate_split hg

theorem check_encodeGNFrames_no_blank_no_outputTrue (r : GNProgram) :
    ∀ frame ∈ encodeGNFrames r,
      frame ≠ G1Frame.blank ∧ frame ≠ .output true :=
  encodeGNFrames_no_blank_no_outputTrue r

theorem check_encodeGNFrames_cursor_unique {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (encodeGNFrames r).count .cursor = 1 :=
  encodeGNFrames_cursor_unique hg

theorem check_gnTransition_locate_none (phase : Fin 1)
    (mode : GNLocateMode) (b0 b1 b2 b3 : Bool)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    gnTransition phase (.locating ⟨mode, .r0 b1 b2 b3⟩) b0 =
      (0, .reject, b0, .stay) :=
  gnTransition_locate_none phase mode b0 b1 b2 b3 hbad

theorem check_gnTransition_locate_decoded_reject (phase : Fin 1)
    (mode : GNLocateMode) (frame : G1Frame) (b0 b1 b2 b3 : Bool)
    (hdecode : decodeG1Frame? [b0, b1, b2, b3] = some frame)
    (hbad : gnLocateAdvance mode frame = .reject) :
    gnTransition phase (.locating ⟨mode, .r0 b1 b2 b3⟩) b0 =
      (0, .reject, b0, .stay) :=
  gnTransition_locate_decoded_reject phase mode frame b0 b1 b2 b3 hdecode hbad

theorem check_gnTransition_locate_reserved (phase : Fin 1)
    (mode : GNLocateMode) :
    gnTransition phase (.locating ⟨mode, .r0 true false true⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.locating ⟨mode, .r0 true true false⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.locating ⟨mode, .r0 true true true⟩) true =
        (0, .reject, true, .stay) :=
  gnTransition_locate_reserved phase mode

theorem check_gnLocate_firstRecord_path {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    GNLocateRevValidPath .tailFinish (gnFirstRecordMiddle r) ∧
      (gnLocateAdvanceList .tailFinish (gnFirstRecordMiddle r)).Reverse ∧
      gnLocateAdvance
        (gnLocateAdvanceList .tailFinish (gnFirstRecordMiddle r)) .cursor =
          .firstRecord :=
  gnLocate_firstRecord_path hg

theorem check_gnLocate_noGate_path {r : GNProgram}
    (hg : r.program.gates = []) :
    GNLocateRevValidPath .tailFinish
        [.separator, .output false, .finish] ∧
      gnLocateAdvanceList .tailFinish
        [.separator, .output false, .finish] = .recordEdge ∧
      gnLocateAdvance .recordEdge .separator = .noGate :=
  gnLocate_noGate_path hg

theorem check_gnFirstRecordSteps_provenance (r : GNProgram) :
    gnFirstRecordSteps r = ((encodeGN r).length + 9) +
      (1 + 4 * (gnFirstRecordMiddle r).length + 4) :=
  gnFirstRecordSteps_provenance r

theorem check_gnNoGateSteps_provenance (r : GNProgram) :
    gnNoGateSteps r = ((encodeGN r).length + 9) + 17 :=
  gnNoGateSteps_provenance r

theorem check_gnFirstRecordConfig_scratch_blank (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g)
    (j : Fin (GNM.tapeLength (encodeGN r).length))
    (hj : (encodeGN r).length ≤ (j : Nat)) :
    (gnFirstRecordConfig r g hg).tape j = false :=
  gnFirstRecordConfig_scratch_blank r g hg j hj

theorem check_gnNoGateConfig_scratch_blank (r : GNProgram)
    (j : Fin (GNM.tapeLength (encodeGN r).length))
    (hj : (encodeGN r).length ≤ (j : Nat)) :
    (gnNoGateConfig r).tape j = false :=
  gnNoGateConfig_scratch_blank r j hj

theorem check_gnFirstRecordConfig_structure (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    (gnFirstRecordConfig r g hg).state = gnFirstRecordQ ∧
      ((gnFirstRecordConfig r g hg).head : Nat) = 4 * gnRecordsStart r ∧
      (gnFirstRecordConfig r g hg).tape =
        (GNM.initialConfig (gnPoint (encodeGN r))).tape :=
  gnFirstRecordConfig_structure r g hg

theorem check_gnNoGateConfig_structure (r : GNProgram) :
    (gnNoGateConfig r).state = gnNoGateQ ∧
      ((gnNoGateConfig r).head : Nat) = 4 * (r.inputs.length + 1) ∧
      (gnNoGateConfig r).tape =
        (GNM.initialConfig (gnPoint (encodeGN r))).tape :=
  gnNoGateConfig_structure r

theorem check_gnFirstRecord_copyShuttle_handoff {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    GNInstallAdmissible G1Frame.cursor ∧
      (∀ frame ∈ gnFirstRecordMiddle r, GNInstallAdmissible frame) ∧
      4 * ((gnLocatePrefix r).length +
        (gnFirstRecordMiddle r).length + 2) <
          GNM.tapeLength (encodeGN r).length ∧
      frameListTape
          (((gnLocatePrefix r ++ .cursor :: gnFirstRecordMiddle r) ++
            [G1Frame.blank]).flatMap G1Frame.bits) =
        (gnFirstRecordConfig r g hg).tape :=
  gnFirstRecord_copyShuttle_handoff hg

theorem check_gnCS_scratchEntry_to_firstRecord (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnScratchEntryConfig r)
        (gnFirstRecordLocateSteps r) = gnFirstRecordConfig r g hg :=
  gnCS_scratchEntry_to_firstRecord r g hg

theorem check_gnCS_scratchEntry_to_noGate (r : GNProgram)
    (hg : r.program.gates = []) :
    TM.runConfig (M := GNM) (gnScratchEntryConfig r) gnNoGateLocateSteps =
      gnNoGateConfig r :=
  gnCS_scratchEntry_to_noGate r hg

theorem check_gnCS_encodeGN_firstRecord (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r))) (gnFirstRecordSteps r) =
      gnFirstRecordConfig r g hg :=
  gnCS_encodeGN_firstRecord r g hg

theorem check_gnCS_encodeGN_noGate (r : GNProgram)
    (hg : r.program.gates = []) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r))) (gnNoGateSteps r) =
      gnNoGateConfig r :=
  gnCS_encodeGN_noGate r hg

theorem check_gnFirstRecordSteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordSteps r ≤ gnClock (encodeGN r).length :=
  gnFirstRecordSteps_le_gnClock hg

theorem check_gnNoGateSteps_le_gnClock (r : GNProgram) :
    gnNoGateSteps r ≤ gnClock (encodeGN r).length :=
  gnNoGateSteps_le_gnClock r

open GNFixedDelegateProbes in
theorem check_literal_oneConstFalse_firstRecord :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 94 =
      gnFirstRecordConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0) (by rfl) ∧
    ((gnFirstRecordConfig oneConstFalseProgram
      (SLGate.const false : SLGate 0) (by rfl)).head : Nat) = 12 :=
  GNScratchBootstrapProbes.literal_oneConstFalse_firstRecord

open GNFixedDelegateProbes in
theorem check_literal_empty_noGate :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN emptyProgram))) 46 =
      gnNoGateConfig emptyProgram ∧
    ((gnNoGateConfig emptyProgram).head : Nat) = 4 :=
  GNScratchBootstrapProbes.literal_empty_noGate

end Pnp3.Tests.TMGateNScratchBootstrapSurface
