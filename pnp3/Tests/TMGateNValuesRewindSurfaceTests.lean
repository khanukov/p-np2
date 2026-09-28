import Complexity.TMVerifier.TuringToolkit.GateNValuesRewind

/-!
# GN-E2-4a values-rewind surface (2026-09-27)

Definition pins and one direct full-proposition wrapper for every public
theorem of `GateNValuesRewind`, together with definition pins for the new
public control pieces `GN-E2-4a` adds to `GateNFixedDelegateRelocation`: the
two `GNState` constructors `rewind` and `valuesEntry`, the finite rewind mode
type, its frame- and bit-level tables, and the one-buffer row set.  Private
kernel glue is deliberately excluded.  A bare `#check @name` pins only the
name, so every substantive signature is restated in full here.
-/

namespace Pnp3.Tests.TMGateNValuesRewindSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.GNFixedDelegateProbes

/-! ## New public control pieces -/

#check @GNState.rewind
#check @GNState.valuesEntry
#check @GNRewindMode
#check @GNRewindMode.scan
#check @GNRewindMode.anchor
#check @GNRewindMode.reject
#check @gnRewindAdvance
#check @gnRewindComplete
#check @gnRewindControl

/-! ## New public definitions of the slice -/

#check @GNRewindMode.Stop
#check @GNRewindMode.Reverse
#check @gnRewindStopState
#check @gnRewindScanner
#check @gnValuesRewindSteps
#check @gnRewindTape
#check @gnValuesRewindConfig
#check @gnValuesEntryConfigOf
#check @gnValuesRewindPre
#check @gnValuesRewindPost
#check @gnValuesEntrySteps
#check @gnValuesEntryConfig
#check @GNValuesRewindProbes.oneConstFalseValuesEntryConfig

/-! ## New public theorems of the slice -/

#check @gnTransition_rewind_rows
#check @gnTransition_rewind_decision
#check @gnTransition_rewind_reserved
#check @gnRewindAdvance_laws
#check @GNRewindMode.Reverse.eq
#check @gnRewind_validPath
#check @gnCS_rewind_reserved1101_reject_four
#check @gnCS_rewind_reserved1101_reject_stable
#check @gnValuesRewindSteps_provenance
#check @gnCS_valuesRewind_exact
#check @gnValuesRewindPre_length
#check @gnValuesRewindPre_ne_bof
#check @gnValuesRewind_frames
#check @gnCS_encodeGN_valuesEntry_exact
#check @gnValuesEntryConfig_structure
#check @gnValuesEntrySteps_le_gnClock
#check @GNValuesRewindProbes.literal_oneConstFalse_valuesEntry

/-! ## Full-proposition wrappers -/

theorem check_gnTransition_rewind_rows (phase : Fin 1)
    (b0 b1 b2 b3 scan : Bool) :
    gnTransition phase .recordDone scan = (0, .rewind .r3, scan, .left) ∧
      gnTransition phase (.rewind .r3) scan =
        (0, .rewind (.r2 scan), scan, .left) ∧
      gnTransition phase (.rewind (.r2 b3)) scan =
        (0, .rewind (.r1 scan b3), scan, .left) ∧
      gnTransition phase (.rewind (.r1 b2 b3)) scan =
        (0, .rewind (.r0 scan b2 b3), scan, .left) ∧
      gnTransition phase (.rewind .p0) scan =
        (0, .rewind (.p1 false), scan, .right) ∧
      gnTransition phase (.rewind (.p1 b0)) scan =
        (0, .rewind (.p2 false false), scan, .right) ∧
      gnTransition phase (.rewind (.p2 b0 b1)) scan =
        (0, .rewind (.p3 false false false), scan, .right) ∧
      gnTransition phase (.rewind (.p3 b0 b1 b2)) scan =
        (0, .valuesEntry, scan, .right) ∧
      gnTransition phase .valuesEntry scan = (0, .valuesEntry, scan, .stay) :=
  gnTransition_rewind_rows phase b0 b1 b2 b3 scan

theorem check_gnTransition_rewind_decision (phase : Fin 1) :
    (∀ b1 b2 b3 scan : Bool,
        decodeG1Frame? [scan, b1, b2, b3] = some G1Frame.bof →
        gnTransition phase (.rewind (.r0 b1 b2 b3)) scan =
          (0, .rewind .p0, scan, .stay)) ∧
      (∀ (frame : G1Frame) (b1 b2 b3 scan : Bool),
        decodeG1Frame? [scan, b1, b2, b3] = some frame →
        frame ≠ G1Frame.bof →
        gnTransition phase (.rewind (.r0 b1 b2 b3)) scan =
          (0, .rewind .r3, scan, .left)) ∧
      (∀ b1 b2 b3 scan : Bool,
        decodeG1Frame? [scan, b1, b2, b3] = none →
        gnTransition phase (.rewind (.r0 b1 b2 b3)) scan =
          (0, .reject, scan, .stay)) :=
  gnTransition_rewind_decision phase

theorem check_gnTransition_rewind_reserved (phase : Fin 1) :
    gnTransition phase (.rewind (.r0 true false true)) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.rewind (.r0 true true false)) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.rewind (.r0 true true true)) true =
        (0, .reject, true, .stay) :=
  gnTransition_rewind_reserved phase

theorem check_gnRewindAdvance_laws (mode : GNRewindMode) (b : Bool) :
    gnRewindAdvance mode .bof = .anchor ∧
      gnRewindAdvance mode (.data b) = .scan ∧
      gnRewindAdvance mode (.output false) = .scan ∧
      gnRewindAdvance mode .separator = .scan ∧
      gnRewindAdvance mode .cursor = .scan ∧
      gnRewindAdvance mode .tag = .scan ∧
      gnRewindAdvance mode .index = .scan ∧
      gnRewindAdvance mode .argSep = .scan ∧
      gnRewindAdvance mode .finish = .scan :=
  gnRewindAdvance_laws mode b

theorem check_GNRewindMode_Reverse_eq {mode : GNRewindMode}
    (h : mode.Reverse) : mode = .scan :=
  GNRewindMode.Reverse.eq h

theorem check_gnRewind_validPath {frames : List G1Frame}
    (h : ∀ f ∈ frames, f ≠ G1Frame.bof) :
    gnRewindScanner.RevValidPath .scan frames ∧
      gnRewindScanner.revAdvanceList .scan frames = .scan :=
  gnRewind_validPath h

theorem check_gnCS_rewind_reserved1101_reject_four (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
          change base + 3 < GNM.tapeLength n
          omega) tape (.rewind .r3)) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n base (by
        change base < GNM.tapeLength n
        omega) tape .reject :=
  gnCS_rewind_reserved1101_reject_four n base hsafe tape hbits

theorem check_gnCS_rewind_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
          change base + 3 < GNM.tapeLength n
          omega) tape (.rewind .r3)) (4 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n base (by
        change base < GNM.tapeLength n
        omega) tape .reject :=
  gnCS_rewind_reserved1101_reject_stable n base hsafe tape hbits k

theorem check_gnValuesRewindSteps_provenance (scanned : Nat) :
    gnValuesRewindSteps scanned = 1 + (4 * scanned + 4) + 4 ∧
      gnValuesRewindSteps 0 = 9 :=
  gnValuesRewindSteps_provenance scanned

theorem check_gnCS_valuesRewind_exact (n : Nat) (pre post : List G1Frame)
    (hpre : ∀ f ∈ pre, f ≠ G1Frame.bof)
    (hroom : 4 * pre.length + 4 < GNM.tapeLength n) :
    TM.runConfig (M := GNM) (gnValuesRewindConfig n pre post hroom)
        (gnValuesRewindSteps pre.length) =
      gnValuesEntryConfigOf n pre post hroom :=
  gnCS_valuesRewind_exact n pre post hpre hroom

theorem check_gnValuesRewindPre_length (r : GNProgram)
    (g : SLGate r.inputs.length) :
    (gnValuesRewindPre r g).length =
      r.inputs.length + r.program.gates.length + 1 +
        gnRecordSize (gnGateFields g) :=
  gnValuesRewindPre_length r g

theorem check_gnValuesRewindPre_ne_bof (r : GNProgram)
    (g : SLGate r.inputs.length) :
    ∀ f ∈ gnValuesRewindPre r g, f ≠ G1Frame.bof :=
  gnValuesRewindPre_ne_bof r g

theorem check_gnValuesRewind_frames {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    G1Frame.bof :: gnValuesRewindPre r g ++ gnValuesRewindPost r g =
      encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
        [G1Frame.blank] :=
  gnValuesRewind_frames hg

theorem check_gnCS_encodeGN_valuesEntry_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnValuesEntrySteps r g) = gnValuesEntryConfig r g hg :=
  gnCS_encodeGN_valuesEntry_exact hg

theorem check_gnValuesEntryConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnValuesEntryConfig r g hg).state =
        ⟨(0 : Fin 1), GNState.valuesEntry⟩ ∧
      ((gnValuesEntryConfig r g hg).head : Nat) = 4 ∧
      (gnValuesEntryConfig r g hg).tape =
        frameListTape
          ((encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
            [G1Frame.blank]).flatMap G1Frame.bits) ∧
      (gnValuesEntryConfig r g hg).tape = (gnFirstRecordDoneConfig r g hg).tape ∧
      G1Frame.bof :: ((gnCurrentValues r []).map G1Frame.data ++
          gnSlotFrames r.program.gates.length ++ [G1Frame.separator]) =
        gnLocatePrefix r ∧
      (gnRecordFrames .cursor g).map gnInstallImage ++
          (gnCurrentValues r []).map G1Frame.data =
        g1PrefixFrames (gnFirstRequest r g) :=
  gnValuesEntryConfig_structure hg

theorem check_gnValuesEntrySteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnValuesEntrySteps r g ≤ gnClock (encodeGN r).length :=
  gnValuesEntrySteps_le_gnClock hg

theorem check_literal_oneConstFalse_valuesEntry :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 700 =
      GNValuesRewindProbes.oneConstFalseValuesEntryConfig ∧
    (GNValuesRewindProbes.oneConstFalseValuesEntryConfig.head : Nat) = 4 ∧
    GNValuesRewindProbes.oneConstFalseValuesEntryConfig.state =
      ⟨(0 : Fin 1), GNState.valuesEntry⟩ ∧
    GNValuesRewindProbes.oneConstFalseValuesEntryConfig.tape =
      GNBodyDriverProbes.oneConstFalseRecordDoneConfig.tape :=
  GNValuesRewindProbes.literal_oneConstFalse_valuesEntry

end Pnp3.Tests.TMGateNValuesRewindSurface
