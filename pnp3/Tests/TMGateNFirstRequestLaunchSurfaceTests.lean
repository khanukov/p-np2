import Complexity.TMVerifierExtensions.GateNFirstRequestLaunchExamples

/-! Full proposition pins for GN-E2-5d Infrastructure. -/
namespace Pnp3.Tests.TMGateNFirstRequestLaunchSurface
open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open FrameScan Encoding GNEncodingExamples GNValuesCopyProbes GNValuesInductionProbes
open GNFirstRequestLaunchProbes

#synth Fintype GNState
#synth DecidableEq GNState
#check GNState.launch
#check gnLaunchAdvance
#check gnLaunchComplete
#check gnLaunchControl
#check gnLaunchStopState
#check gnLaunchScanner
#check gnLaunchConfig
#check gnFirstRequestLaunchSteps
#check gnFirstLaunchSteps
#check capGNFrames
#check capLaunched
#check capOutputDone
#check capReturned
#check firstNotProgram

theorem check_gnTransition_launch_rows (phase : Fin 1) (b0 b1 b2 b3 scan : Bool) :
    gnTransition phase .requestReady scan = (0, .launch .r3, scan, .left) ∧
      gnTransition phase (.launch .r3) scan =
        (0, .launch (.r2 scan), scan, .left) ∧
      gnTransition phase (.launch (.r2 b3)) scan =
        (0, .launch (.r1 scan b3), scan, .left) ∧
      gnTransition phase (.launch (.r1 b2 b3)) scan =
        (0, .launch (.r0 scan b2 b3), scan, .left) ∧
      gnTransition phase (.launch .p0) scan = (0, .reject, scan, .stay) ∧
      gnTransition phase (.launch (.p1 b0)) scan = (0, .reject, scan, .stay) ∧
      gnTransition phase (.launch (.p2 b0 b1)) scan = (0, .reject, scan, .stay) ∧
      gnTransition phase (.launch (.p3 b0 b1 b2)) scan = (0, .reject, scan, .stay) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnTransition_launch_rows phase b0 b1 b2 b3 scan

theorem check_gnTransition_launch_decision (phase : Fin 1) :
    (∀ b1 b2 b3 scan : Bool,
      decodeG1Frame? [scan, b1, b2, b3] = some G1Frame.bof →
      gnTransition phase (.launch (.r0 b1 b2 b3)) scan =
        (0, .delegated G1M.start, scan, .stay)) ∧
    (∀ (f : G1Frame) (b1 b2 b3 scan : Bool),
      decodeG1Frame? [scan, b1, b2, b3] = some f → f ≠ G1Frame.bof → f ≠ G1Frame.blank →
      gnTransition phase (.launch (.r0 b1 b2 b3)) scan =
        (0, .launch .r3, scan, .left)) ∧
    (∀ b1 b2 b3 scan : Bool,
      decodeG1Frame? [scan, b1, b2, b3] = some G1Frame.blank →
      gnTransition phase (.launch (.r0 b1 b2 b3)) scan =
        (0, .reject, scan, .stay)) ∧
    (∀ b1 b2 b3 scan : Bool, decodeG1Frame? [scan, b1, b2, b3] = none →
      gnTransition phase (.launch (.r0 b1 b2 b3)) scan =
        (0, .reject, scan, .stay)) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnTransition_launch_decision phase

theorem check_gnCS_launch_onList_exact (n : Nat) (pre body post : List G1Frame)
    (hbody : ∀ f ∈ body, f ≠ G1Frame.bof ∧ f ≠ G1Frame.blank)
    (hroom : 4 * (pre.length + body.length + 1) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig n (4 * (pre.length + body.length + 1)) hroom
        (frameListTape ((pre ++ .bof :: body ++ post).flatMap G1Frame.bits))
        .requestReady) (4 * body.length + 5) =
      gnLaunchConfig n (4 * pre.length) (by omega)
        (frameListTape ((pre ++ .bof :: body ++ post).flatMap G1Frame.bits))
        (.delegated G1M.start) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_launch_onList_exact n pre body post hbody hroom

theorem check_gnCS_requestReady_reserved1101_reject_five (n base : Nat)
    (hroom : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hroom tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig n (base+4) hroom tape .requestReady) 5 =
      gnLaunchConfig n base (by omega) tape .reject := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_requestReady_reserved1101_reject_five n base hroom tape hbits

theorem check_gnCS_requestReady_reserved1101_reject_stable (n base : Nat)
    (hroom : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hroom tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig n (base+4) hroom tape .requestReady) (5+k) =
      gnLaunchConfig n base (by omega) tape .reject := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_requestReady_reserved1101_reject_stable n base hroom tape hbits k

theorem check_gnCS_requestReady_allBlank_reject_exact (n h : Nat)
    (hh : h < GNM.tapeLength n) (k : Nat) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig n h hh (fun _ => false) .requestReady) (5+k) =
      gnLaunchConfig n (h-4) (by omega) (fun _ => false) .reject := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_requestReady_allBlank_reject_exact n h hh k

theorem check_gnFirstRequestReady_geometry {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    (gnFirstRequestReadyConfig r g hg).state = ⟨(0 : Fin 1), .requestReady⟩ ∧
    ((gnFirstRequestReadyConfig r g hg).head : Nat) =
      (encodeGN r).length + (encodeG1 (gnFirstRequest r g)).length ∧
    (gnFirstRequestReadyConfig r g hg).tape =
      frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) ∧
    (encodeGN r).length + (encodeG1 (gnFirstRequest r g)).length <
      GNM.tapeLength (encodeGN r).length := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnFirstRequestReady_geometry hg

theorem check_gnFirstLaunchSteps_provenance (r : GNProgram) (g : SLGate r.inputs.length) :
    gnFirstRequestLaunchSteps r g = (encodeG1 (gnFirstRequest r g)).length + 1 ∧
    gnFirstLaunchSteps r g = gnValuesRequestReadySteps r g +
      ((encodeG1 (gnFirstRequest r g)).length + 1) ∧
    gnFirstLaunchSteps r g = gnValuesEntrySteps r g +
      (r.inputs.length * (8 * gnValuesTailDistance r g + 38) +
        (4 * gnValuesTailDistance r g + 20)) +
      ((encodeG1 (gnFirstRequest r g)).length + 1) ∧
    g1GateDoneSteps (gnFirstRequest r g) = g1GateResultSteps (gnFirstRequest r g) +
      (1 + g1OutputKernelSteps (gnFirstRequest r g)) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnFirstLaunchSteps_provenance r g

theorem check_gnCS_requestReady_launch_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnFirstRequestReadyConfig r g hg)
      (gnFirstRequestLaunchSteps r g) = gnFirstInstalledConfig r g hg := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_requestReady_launch_exact hg

theorem check_gnCS_encodeGN_firstLaunch_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g) = gnFirstInstalledConfig r g hg := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_encodeGN_firstLaunch_exact hg

theorem check_gnCS_encodeGN_firstOutputDone_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + g1GateDoneSteps (gnFirstRequest r g)) =
    gnShiftConfig GNM (encodeGN r).length gnEmbed
      (GNM.initialConfig (gnPoint (encodeGN r))).tape
      (g1OutputDoneConfig (gnFirstRequest r g) res) (gnFirstRequest_room hg)
      (g1OutputDoneConfig_head_lt_gnLocalSpan (gnFirstRequest r g) res) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_encodeGN_firstOutputDone_exact hg res hs

theorem check_gnCS_encodeGN_firstReturned_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g) + 1)) =
    gnReturnConfig res (gnShiftConfig GNM (encodeGN r).length gnEmbed
      (GNM.initialConfig (gnPoint (encodeGN r))).tape
      (g1OutputDoneConfig (gnFirstRequest r g) res) (gnFirstRequest_room hg)
      (g1OutputDoneConfig_head_lt_gnLocalSpan (gnFirstRequest r g) res)) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_encodeGN_firstReturned_exact hg res hs

theorem check_gnFirstReturned_structure {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    let out := TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g) + 1))
    out.state = gnReturnedQ res ∧
      (out.head : Nat) = (encodeGN r).length + g1OutputExitHead (gnFirstRequest r g) ∧
      out.tape = frameListTape ((encodeGNFrames r ++
        g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) ∧
      out.tape = gnOverlayTape GNM (encodeGN r).length (gnFirstRequest_room hg)
        (g1OutputDoneConfig (gnFirstRequest r g) res)
        (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnFirstReturned_structure hg res hs

theorem check_literal_cap_firstLaunch :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1333 = capLaunched ∧
    (encodeGN capProgram).length = 84 ∧
    (encodeG1 (gnFirstRequest capProgram capFirstGate)).length = 32 ∧
    gnValuesRequestReadySteps capProgram capFirstGate = 1300 ∧
    gnFirstRequestLaunchSteps capProgram capFirstGate = 33 ∧
    gnFirstLaunchSteps capProgram capFirstGate = 1333 ∧
    (capLaunched.head : Nat) = 84 ∧ capLaunched.state = gnEmbed G1M.start := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes.literal_cap_firstLaunch

theorem check_literal_cap_firstReturned :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1562 = capOutputDone ∧
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1563 = capReturned ∧
    g1GateDoneSteps (gnFirstRequest capProgram capFirstGate) = 229 ∧
    capReturned.state = gnReturnedQ true ∧ (capReturned.head : Nat) = 107 ∧
    capReturned.tape ⟨111, by decide⟩ = true ∧
    capReturned.tape ⟨11, by decide⟩ = false ∧
    capLaunched.tape ⟨111, by decide⟩ = false ∧
    evalGNProgram capProgram = some false := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes.literal_cap_firstReturned

theorem check_literal_cap_launch_executable :
    (TM.runConfig (M := GNM) capValuesReady 33).state = gnEmbed G1M.start ∧
    ((TM.runConfig (M := GNM) capValuesReady 33).head : Nat) = 84 ∧
    (TM.runConfig (M := GNM) capValuesReady 34).state =
      gnEmbed ⟨(0 : Fin 1), g1State .vBof .p1 false⟩ ∧
    ((TM.runConfig (M := GNM) capValuesReady 34).head : Nat) = 85 ∧
    (TM.runConfig (M := GNM) capValuesReady 34).tape ⟨84, by decide⟩ = false ∧
    (TM.runConfig (M := GNM) capValuesReady 34).tape ⟨111, by decide⟩ = false := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes.literal_cap_launch_executable

theorem check_literal_first_not_is_undefined :
    firstNotProgram.program.gates[0]? = some (.notGate 0) ∧
    (gnFirstRequest firstNotProgram (.notGate 0)).Canonical ∧
    (gnFirstRequest firstNotProgram (.notGate 0)).spec = none ∧
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN firstNotProgram)))
      (gnFirstLaunchSteps firstNotProgram (.notGate 0)) =
      gnFirstInstalledConfig firstNotProgram (.notGate 0) rfl := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes.literal_first_not_is_undefined

theorem check_literal_reserved_launch_reject (k : Nat) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig 0 4 (by decide) (frameListTape [true, true, false, true])
        .requestReady) (5+k) =
      gnLaunchConfig 0 0 (by decide) (frameListTape [true, true, false, true])
        .reject := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes.literal_reserved_launch_reject k

theorem check_literal_noBof_allBlank_launch_reject :
    (TM.runConfig (M := GNM)
      (gnLaunchConfig 0 0 (by decide) (fun _ => false) .requestReady) 5).state =
        ⟨(0 : Fin 1), GNState.reject⟩ ∧
    ((TM.runConfig (M := GNM)
      (gnLaunchConfig 0 0 (by decide) (fun _ => false) .requestReady) 5).head : Nat) = 0 ∧
    (TM.runConfig (M := GNM)
      (gnLaunchConfig 0 4 (by decide) (fun _ => false) .requestReady) 5).state =
        ⟨(0 : Fin 1), GNState.reject⟩ ∧
    ((TM.runConfig (M := GNM)
      (gnLaunchConfig 0 4 (by decide) (fun _ => false) .requestReady) 5).head : Nat) = 0 ∧
    (TM.runConfig (M := GNM)
      (gnLaunchConfig 0 0 (by decide) (fun _ => false) .requestReady) 9).state =
        ⟨(0 : Fin 1), GNState.reject⟩ := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes.literal_noBof_allBlank_launch_reject

end Pnp3.Tests.TMGateNFirstRequestLaunchSurface
