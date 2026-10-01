import Complexity.TMVerifier.TuringToolkit.GateNValuesWriter

/-!
# GN-E2-5a values/tail writer surface (2026-09-28)

Definition pins and one direct full-proposition wrapper for every original
GN-E2-5a public theorem of `GateNValuesWriter`, together with pins for the public
control pieces GN-E2-5a adds to `GateNFixedDelegateRelocation`: the finite
values mode type, its frame- and bit-level tables, the one mode/buffer row set,
and the two `GNState` constructors `values` and `requestReady`.  Private kernel
glue — the scanner and writer instances, the aligned-configuration helpers, the
terminal-phase lemmas and the block geometry — is deliberately excluded.  A
bare `#check @name` pins only the name, so every substantive signature is
restated in full here. The classifier `gnCS_values_classify`, promoted to a
public theorem for GN-E2-5b, is pinned and directly audited by the new
`Tests.TMGateNValuesCopySurfaceTests` and `Tests.TMGateNValuesCopyAxioms`.
-/

namespace Pnp3.Tests.TMGateNValuesWriterSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.GNFixedDelegateProbes
open Pnp3.Internal.PsubsetPpoly.TM.GNValuesWriterProbes

/-! ## New public control pieces -/

#check @GNState.values
#check @GNState.requestReady
#check @GNValuesMode
#check @GNValuesMode.reject
#check @gnValuesControl
#check @gnValuesEnter
#check @gnValuesAdvance
#check @gnValuesComplete
#check @gnValuesClassify
#check @gnValuesClassifyBits
#check @gnValuesStep

/-! ## New public definitions of the slice -/

#check @gnValuesTailDistance
#check @gnValuesTailSteps
#check @gnFirstRequestReadySteps
#check @gnFirstRequestReadyConfig
#check @oneConstFalseRequestReadyFrames
#check @oneConstFalseRequestReadyConfig

/-! ## New public theorems of the slice -/

#check @gnTransition_values_rows
#check @gnTransition_values_reserved
#check @gnTransition_dataExit
#check @gnValuesTailSteps_provenance
#check @gnFirstRequestReady_room
#check @gnCS_valuesTail_exact
#check @gnFirstRequestReadyConfig_structure
#check @gnCS_encodeGN_firstRequestReady_exact
#check @gnFirstRequestReadySteps_le_gnClock
#check @gnCS_valuesEntry_reserved1101_reject_four
#check @gnCS_valuesEntry_reserved1101_reject_stable
#check @oneConstFalseGate_mem
#check @oneConstFalseNoInputs
#check @literal_oneConstFalse_requestReady

/-! ## Full-proposition wrappers -/

theorem check_gnTransition_values_rows (phase : Fin 1) (mode : GNValuesMode)
    (buffer : GNInstallBuffer) (scan : Bool) :
    gnTransition phase .valuesEntry scan =
        (0, .values .probe (.p1 scan), scan, .right) ∧
      gnTransition phase (.values mode buffer) scan =
        (0, gnValuesStep mode buffer scan) ∧
      gnTransition phase .requestReady scan = (0, .launch .r3, scan, .left) ∧
      gnValuesStep .back .p0 scan = (.install .probe .p0 .empty, scan, .left) ∧
      gnValuesStep .tailBack .p0 scan =
        (.values .writeOutput .p0, scan, .left) ∧
      gnValuesStep .writeOutput .p0 scan =
        (.values .writeOutput (.p1 false), true, .right) ∧
      gnValuesStep .writeFinish (.p3 false false false) scan =
        (.requestReady, false, .right) :=
  gnTransition_values_rows phase mode buffer scan

theorem check_gnTransition_values_reserved (phase : Fin 1) :
    (∀ b0 b1 b2 b3 : Bool, decodeG1Frame? [b0, b1, b2, b3] = none →
        gnTransition phase (.values .probe (.p3 b0 b1 b2)) b3 =
            (0, .reject, b3, .stay) ∧
          gnTransition phase (.values .seekTail (.p3 b0 b1 b2)) b3 =
            (0, .reject, b3, .stay)) ∧
      gnTransition phase (.values .probe (.p3 true false false)) true =
          (0, .reject, true, .stay) ∧
      gnTransition phase (.values .seekTail (.p3 true false false)) true =
          (0, .reject, true, .stay) ∧
      gnTransition phase (.values .probe (.p3 false false false)) false =
          (0, .reject, false, .stay) ∧
      gnTransition phase (.values .probe (.p3 false false true)) false =
          (0, .reject, false, .stay) :=
  gnTransition_values_reserved phase

theorem check_gnTransition_dataExit (phase : Fin 1) (b scan : Bool) :
    gnTransition phase (gnInstallExitState (.carried (.data b))) scan =
        (0, .valuesEntry, scan, .stay) ∧
      ¬ GNInstallExitContinue (GNInstallAux.carried (.data b)) ∧
      ¬ GNInstallExitInvalid (GNInstallAux.carried (.data b)) :=
  gnTransition_dataExit phase b scan

theorem check_gnValuesTailSteps_provenance (r : GNProgram)
    (g : SLGate r.inputs.length) :
    gnValuesTailDistance r g + 2 =
        (encodeGNFrames r).length + (gnRecordFrames .cursor g).length ∧
      gnValuesTailSteps r g = 4 * gnValuesTailDistance r g + 20 ∧
      gnFirstRequestReadySteps r g =
        gnValuesEntrySteps r g + gnValuesTailSteps r g :=
  gnValuesTailSteps_provenance r g

theorem check_gnFirstRequestReady_room {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
      r.inputs.length + 3) < GNM.tapeLength (encodeGN r).length :=
  gnFirstRequestReady_room hg

theorem check_gnCS_valuesTail_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    (hinputs : r.inputs = []) :
    TM.runConfig (M := GNM) (gnValuesEntryConfig r g hg)
        (gnValuesTailSteps r g) = gnFirstRequestReadyConfig r g hg :=
  gnCS_valuesTail_exact hg hinputs

theorem check_gnCS_encodeGN_firstRequestReady_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    (hinputs : r.inputs = []) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnFirstRequestReadySteps r g) = gnFirstRequestReadyConfig r g hg :=
  gnCS_encodeGN_firstRequestReady_exact hg hinputs

theorem check_gnFirstRequestReadyConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnFirstRequestReadyConfig r g hg).state =
        ⟨(0 : Fin 1), GNState.requestReady⟩ ∧
      ((gnFirstRequestReadyConfig r g hg).head : Nat) =
        4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
          r.inputs.length + 2) ∧
      (gnFirstRequestReadyConfig r g hg).tape =
        frameListTape
          ((encodeGNFrames r ++ encodeG1Frames (gnFirstRequest r g) ++
            [G1Frame.blank]).flatMap G1Frame.bits) ∧
      encodeGNFrames r ++ encodeG1Frames (gnFirstRequest r g) ++
          [G1Frame.blank] =
        encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
          r.inputs.map G1Frame.data ++
            [G1Frame.output false, G1Frame.finish, G1Frame.blank] ∧
      (gnRecordFrames .cursor g).map gnInstallImage ++
          (gnCurrentValues r []).map G1Frame.data =
        g1PrefixFrames (gnFirstRequest r g) ∧
      (gnFirstRequest r g).spec =
        g.compute (fun i => r.inputs[i.val]'(by omega)) [] :=
  gnFirstRequestReadyConfig_structure hg

theorem check_gnFirstRequestReadySteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRequestReadySteps r g ≤ gnClock (encodeGN r).length :=
  gnFirstRequestReadySteps_le_gnClock hg

theorem check_gnCS_valuesEntry_reserved1101_reject_four (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape .valuesEntry) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape .reject :=
  gnCS_valuesEntry_reserved1101_reject_four n base hsafe tape hbits

theorem check_gnCS_valuesEntry_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape .valuesEntry) (4 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape .reject :=
  gnCS_valuesEntry_reserved1101_reject_stable n base hsafe tape hbits k

theorem check_oneConstFalseGate_mem :
    oneConstFalseProgram.program.gates[0]? =
      some (SLGate.const false : SLGate 0) :=
  oneConstFalseGate_mem

theorem check_oneConstFalseNoInputs : oneConstFalseProgram.inputs = [] :=
  oneConstFalseNoInputs

theorem check_literal_oneConstFalse_requestReady :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 784 =
      oneConstFalseRequestReadyConfig ∧
    (oneConstFalseRequestReadyConfig.head : Nat) = 80 ∧
    oneConstFalseRequestReadyConfig.state =
      ⟨(0 : Fin 1), GNState.requestReady⟩ ∧
    oneConstFalseRequestReadyConfig.tape =
      frameListTape (oneConstFalseRequestReadyFrames.flatMap G1Frame.bits) ∧
    oneConstFalseRequestReadyFrames.take 12 =
      encodeGNFrames oneConstFalseProgram ∧
    oneConstFalseRequestReadyFrames.drop 18 =
      [G1Frame.output false, G1Frame.finish, G1Frame.blank] ∧
    G1Frame.output true ∉ oneConstFalseRequestReadyFrames ∧
    oneConstFalseRequestReadyConfig.tape ⟨72, by decide⟩ = true ∧
    oneConstFalseRequestReadyConfig.tape ⟨76, by decide⟩ = true ∧
    (gnValuesEntryConfig oneConstFalseProgram (SLGate.const false)
        oneConstFalseGate_mem).tape ⟨72, by decide⟩ = false ∧
    (gnValuesEntryConfig oneConstFalseProgram (SLGate.const false)
        oneConstFalseGate_mem).tape ⟨76, by decide⟩ = false :=
  literal_oneConstFalse_requestReady

end Pnp3.Tests.TMGateNValuesWriterSurface
