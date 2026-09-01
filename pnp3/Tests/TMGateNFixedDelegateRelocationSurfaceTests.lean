import Complexity.TMVerifier.TuringToolkit.GateNFixedDelegateRelocation

/-!
# GN-E1a live scan and fixed delegate/relocation surface (2026-09-01)

Definitions and constructors receive `#check` pins.  Every public source
theorem has a direct wrapper with an explicit proposition; no inferred alias or
Lean `example` is used.
-/

namespace Pnp3.Tests.TMGateNFixedDelegateRelocationSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.G1AResultProbes

#check @g1DoneQ
#check @g1AcceptQ
#check @GNDiscoveryMode
#check @GNDiscoveryMode.start
#check @GNDiscoveryMode.assignments
#check @GNDiscoveryMode.slots
#check @GNDiscoveryMode.firstRecord
#check @GNDiscoveryMode.laterRecord
#check @GNDiscoveryMode.tag0
#check @GNDiscoveryMode.tag1
#check @GNDiscoveryMode.tag2
#check @GNDiscoveryMode.tag3
#check @GNDiscoveryMode.tag4
#check @GNDiscoveryMode.tag5
#check @GNDiscoveryMode.arg1
#check @GNDiscoveryMode.arg2
#check @GNDiscoveryMode.terminalOutput
#check @GNDiscoveryMode.terminalFinish
#check @GNDiscoveryMode.wordEnd
#check @GNDiscoveryMode.reject
#check @GNDiscoveryMode.Forward
#check @GNScanBuffer
#check @GNScanBuffer.p0
#check @GNScanBuffer.p1
#check @GNScanBuffer.p2
#check @GNScanBuffer.p3
#check @GNScanState
#check @GNScanState.mk
#check @GNState
#check @GNState.delegated
#check @GNState.returnedFalse
#check @GNState.returnedTrue
#check @GNState.scanning
#check @GNState.wordEnd
#check @GNState.idle
#check @GNState.accept
#check @GNState.reject
#synth Fintype GNState
#synth DecidableEq GNState
#synth Fintype GNDiscoveryMode
#synth DecidableEq GNDiscoveryMode
#synth Fintype GNScanState
#synth DecidableEq GNScanState
#check @gnDiscoveryAdvance
#check @gnDiscoveryComplete
#check @gnDiscoveryAdvanceList
#check @GNDiscoveryValidPath
#check @gnScanControl
#check @gnReturnedState
#check @gnTransition
#check @gnClock
#check @gnCS
#check @GNM
#check @gnEmbed
#check @gnReturnedQ
#check @gnPoint
#check @gnFrameScanner
#check @gnWordEndConfig
#check @gnReserved1101Bits
#check @gnReserved1101RejectConfig
#check @gnGateShiftConfig
#check @gnReturnConfig
#check @G1RunDelegates
#check @gnLocalSpan
#check @gnShiftConfig
#check @GNFixedDelegateProbes.emptyProgram
#check @GNFixedDelegateProbes.oneConstFalseProgram

theorem check_gnCS_startState : gnCS.startState = gnScanControl .start .p0 :=
  gnCS_startState

theorem check_gnTransition_idle (phase : Fin 1) (scan : Bool) :
    gnTransition phase .idle scan = (0, .idle, scan, .stay) :=
  gnTransition_idle phase scan

theorem check_gnTransition_returnedFalse (phase : Fin 1) (scan : Bool) :
    gnTransition phase .returnedFalse scan =
      (0, .returnedFalse, scan, .stay) :=
  gnTransition_returnedFalse phase scan

theorem check_gnTransition_returnedTrue (phase : Fin 1) (scan : Bool) :
    gnTransition phase .returnedTrue scan =
      (0, .returnedTrue, scan, .stay) :=
  gnTransition_returnedTrue phase scan

theorem check_gnTransition_wordEnd (phase : Fin 1) (scan : Bool) :
    gnTransition phase .wordEnd scan = (0, .wordEnd, scan, .stay) :=
  gnTransition_wordEnd phase scan

theorem check_gnTransition_accept (phase : Fin 1) (scan : Bool) :
    gnTransition phase .accept scan = (0, .accept, scan, .stay) :=
  gnTransition_accept phase scan

theorem check_gnTransition_reject (phase : Fin 1) (scan : Bool) :
    gnTransition phase .reject scan = (0, .reject, scan, .stay) :=
  gnTransition_reject phase scan

theorem check_gnTransition_delegate_ordinary (phase : Fin 1)
    (q : G1M.state) (scan : Bool) (hf : q ≠ g1DoneQ false)
    (ht : q ≠ g1DoneQ true) :
    gnTransition phase (.delegated q) scan =
      (0, .delegated (G1M.step q scan).fst,
        (G1M.step q scan).snd.fst, (G1M.step q scan).snd.snd) :=
  gnTransition_delegate_ordinary phase q scan hf ht

theorem check_gnTransition_intercept_false (phase : Fin 1) (scan : Bool) :
    gnTransition phase (.delegated (g1DoneQ false)) scan =
      (0, .returnedFalse, scan, .stay) :=
  gnTransition_intercept_false phase scan

theorem check_gnTransition_intercept_true (phase : Fin 1) (scan : Bool) :
    gnTransition phase (.delegated (g1DoneQ true)) scan =
      (0, .returnedTrue, scan, .stay) :=
  gnTransition_intercept_true phase scan

theorem check_g1M_step_done (b scan : Bool) :
    G1M.step (g1DoneQ b) scan = (g1AcceptQ, scan, .stay) :=
  g1M_step_done b scan

theorem check_g1M_step_accept (scan : Bool) :
    G1M.step g1AcceptQ scan = (g1AcceptQ, scan, .stay) :=
  g1M_step_accept scan

theorem check_gnM_step_embed_ordinary (q : G1M.state) (scan : Bool)
    (hf : q ≠ g1DoneQ false) (ht : q ≠ g1DoneQ true) :
    GNM.step (gnEmbed q) scan =
      (gnEmbed (G1M.step q scan).fst,
        (G1M.step q scan).snd.fst, (G1M.step q scan).snd.snd) :=
  gnM_step_embed_ordinary q scan hf ht

theorem check_gnM_step_embed_done (b scan : Bool) :
    GNM.step (gnEmbed (g1DoneQ b)) scan =
      (gnReturnedQ b, scan, .stay) :=
  gnM_step_embed_done b scan

theorem check_gnDiscoveryComplete_decode (m : GNDiscoveryMode)
    (b0 b1 b2 b3 : Bool) :
    gnDiscoveryComplete m b0 b1 b2 b3 =
      match decodeG1Frame? [b0, b1, b2, b3] with
      | some frame => gnDiscoveryAdvance m frame
      | none => .reject :=
  gnDiscoveryComplete_decode m b0 b1 b2 b3

theorem check_gnDiscovery_encodeGNFrames (r : GNProgram) :
    gnDiscoveryAdvanceList .start (encodeGNFrames r) = .wordEnd ∧
      GNDiscoveryValidPath .start (encodeGNFrames r) :=
  gnDiscovery_encodeGNFrames r

theorem check_gnDiscoveryComplete_reserved (m : GNDiscoveryMode) :
    gnDiscoveryComplete m true true false true = .reject ∧
      gnDiscoveryComplete m true true true false = .reject ∧
        gnDiscoveryComplete m true true true true = .reject :=
  gnDiscoveryComplete_reserved m

theorem check_gnDiscoveryAdvance_start_malformed :
    gnDiscoveryAdvance .start .blank = .reject ∧
      gnDiscoveryAdvance .start .spent = .reject ∧
        gnDiscoveryAdvance .start (.output true) = .reject ∧
          gnDiscoveryAdvance .start .separator = .reject ∧
            gnDiscoveryAdvance .start .cursor = .reject ∧
              gnDiscoveryAdvance .assignments .bof = .reject :=
  gnDiscoveryAdvance_start_malformed

theorem check_gnInitialTape_eq_frameListTape (bits : List Bool) :
    (GNM.initialConfig (gnPoint bits)).tape = frameListTape bits :=
  gnInitialTape_eq_frameListTape bits

theorem check_gnCS_encodeGN_wordEnd (r : GNProgram) :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN r)))
      (encodeGN r).length = gnWordEndConfig r :=
  gnCS_encodeGN_wordEnd r

theorem check_gnCS_wordEnd_stable (r : GNProgram) (k : Nat) :
    TM.runConfig (M := GNM) (gnWordEndConfig r) k = gnWordEndConfig r :=
  gnCS_wordEnd_stable r k

theorem check_gnFrameScanner_rejectMacrostep (n h : Nat)
    (hsafe : h + 4 < gnFrameScanner.machine.tapeLength n)
    (tape : Fin (gnFrameScanner.machine.tapeLength n) → Bool)
    (m : GNDiscoveryMode) (hm : m.Forward)
    (hbad : gnDiscoveryComplete m
      (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
      (tape ⟨h + 2, by omega⟩) (tape ⟨h + 3, by omega⟩) = .reject) :
    TM.runConfig (M := gnFrameScanner.machine)
        (gnFrameScanner.alignedFrame n h (by omega) tape m ()) 4 =
      gnFrameScanner.alignedConfigQ n (h + 3) (by omega) tape .reject :=
  gnFrameScanner_rejectMacrostep n h hsafe tape m hm hbad

theorem check_gnCS_reserved1101_reject_four :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint gnReserved1101Bits)) 4 =
        gnReserved1101RejectConfig :=
  gnCS_reserved1101_reject_four

theorem check_gnTransition_reserved_windows (m : GNDiscoveryMode) :
    gnTransition 0 (.scanning ⟨m, .p3 true true false⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition 0 (.scanning ⟨m, .p3 true true true⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨m, .p3 true true true⟩) true =
        (0, .reject, true, .stay) :=
  gnTransition_reserved_windows m

theorem check_gnTransition_start_malformed_windows :
    gnTransition 0 (.scanning ⟨.start, .p3 false false false⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 true true false⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 true false false⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 false true false⟩) false =
        (0, .reject, false, .stay) ∧
      gnTransition 0 (.scanning ⟨.start, .p3 false true true⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition 0 (.scanning ⟨.assignments, .p3 false false false⟩) true =
        (0, .reject, true, .stay) :=
  gnTransition_start_malformed_windows

theorem check_gnCS_reject_stable {n : Nat}
    (c : Configuration (M := GNM) n)
    (hstate : c.state = ⟨(0 : Fin 1), GNState.reject⟩) (k : Nat) :
    TM.runConfig (M := GNM) c k = c :=
  gnCS_reject_stable c hstate k

theorem check_g1CS_gate_done_no_early_outputDone (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    (j : Nat) (hj : j < g1GateDoneSteps r) (b : Bool) :
    (TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) j).state ≠ g1DoneQ b :=
  g1CS_gate_done_no_early_outputDone r hc res hs j hj b

theorem check_gn_g1_gate_done_delegates (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res) :
    G1RunDelegates GNM gnEmbed
      (G1M.initialConfig (g1Point (encodeG1 r))) (g1GateDoneSteps r) :=
  gn_g1_gate_done_delegates r hc res hs

theorem check_gn_g1_outputDone_not_delegates {W : Nat}
    (c : Configuration (M := G1M) W) (b : Bool)
    (hstate : c.state = g1DoneQ b) :
    ¬ G1StepDelegates GNM gnEmbed c :=
  gn_g1_outputDone_not_delegates c b hstate

theorem check_g1InitialConfig_head_lt_gnLocalSpan (r : G1Request) :
    ((G1M.initialConfig (g1Point (encodeG1 r))).head : Nat) <
      gnLocalSpan (encodeG1 r).length :=
  g1InitialConfig_head_lt_gnLocalSpan r

theorem check_g1OutputDoneConfig_head_lt_gnLocalSpan
    (r : G1Request) (res : Bool) :
    ((g1OutputDoneConfig r res).head : Nat) <
      gnLocalSpan (encodeG1 r).length :=
  g1OutputDoneConfig_head_lt_gnLocalSpan r res

theorem check_gnCS_gate_shift_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) {N base : Nat}
    (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
        (g1GateDoneSteps r) =
      gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
        (g1OutputDoneConfig_head_lt_gnLocalSpan r res) :=
  gnCS_gate_shift_exact r hc res hs ambient hroom

theorem check_gnCS_gate_shift_outside_every_prefix (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base j : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N)
    (hj : j ≤ g1GateDoneSteps r) (i : Fin (GNM.tapeLength N))
    (hout : (i : Nat) < base ∨
      base + gnLocalSpan (encodeG1 r).length ≤ (i : Nat)) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom) j).tape i =
      ambient i :=
  gnCS_gate_shift_outside_every_prefix r hc res hs ambient hroom hj i hout

theorem check_gnCS_step_shifted_outputDone (r : G1Request) (res : Bool)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM)
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) 1 =
      gnReturnConfig res
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) :=
  gnCS_step_shifted_outputDone r res ambient hroom

theorem check_gnCS_gate_shift_intercept_exact (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
        (g1GateDoneSteps r + 1) =
      gnReturnConfig res
        (gnShiftConfig GNM base gnEmbed ambient (g1OutputDoneConfig r res) hroom
          (g1OutputDoneConfig_head_lt_gnLocalSpan r res)) :=
  gnCS_gate_shift_intercept_exact r hc res hs ambient hroom

theorem check_gnCS_gate_shift_intercept_state (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)).state = gnReturnedQ res :=
  gnCS_gate_shift_intercept_state r hc res hs ambient hroom

theorem check_gnCS_gate_shift_intercept_mode (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    (TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)).state.snd = gnReturnedState res :=
  gnCS_gate_shift_intercept_mode r hc res hs ambient hroom

theorem check_gnCS_gate_shift_intercept_structure (r : G1Request)
    (hc : r.Canonical) (res : Bool) (hs : r.spec = some res)
    {N base : Nat} (ambient : Fin (GNM.tapeLength N) → Bool)
    (hroom : base + gnLocalSpan (encodeG1 r).length ≤ GNM.tapeLength N) :
    let out := TM.runConfig (M := GNM) (gnGateShiftConfig r ambient hroom)
      (g1GateDoneSteps r + 1)
    let shifted := gnShiftConfig GNM base gnEmbed ambient
      (g1OutputDoneConfig r res) hroom
      (g1OutputDoneConfig_head_lt_gnLocalSpan r res)
    out.state.snd = gnReturnedState res ∧
      out.head = shifted.head ∧ out.tape = shifted.tape :=
  gnCS_gate_shift_intercept_structure r hc res hs ambient hroom

theorem check_literal_input_true_shifted_intercept :
    TM.runConfig (M := GNM)
      (gnGateShiftConfig (N := 64) (base := 7) reqInputT (fun _ => true) (by decide))
      230 =
    gnReturnConfig true
      (gnShiftConfig GNM 7 gnEmbed (fun _ => true)
        (g1OutputDoneConfig reqInputT true) (by decide)
        (g1OutputDoneConfig_head_lt_gnLocalSpan reqInputT true)) :=
  GNFixedDelegateProbes.literal_input_true_shifted_intercept

theorem check_literal_const_false_shifted_intercept :
    TM.runConfig (M := GNM)
      (gnGateShiftConfig (N := 64) (base := 7) reqConstF (fun _ => true) (by decide))
      152 =
    gnReturnConfig false
      (gnShiftConfig GNM 7 gnEmbed (fun _ => true)
        (g1OutputDoneConfig reqConstF false) (by decide)
        (g1OutputDoneConfig_head_lt_gnLocalSpan reqConstF false)) :=
  GNFixedDelegateProbes.literal_const_false_shifted_intercept

theorem check_literal_encodeGN_lengths :
    (encodeGN GNFixedDelegateProbes.emptyProgram).length = 20 ∧
      (encodeGN GNFixedDelegateProbes.oneConstFalseProgram).length = 48 :=
  GNFixedDelegateProbes.literal_encodeGN_lengths

theorem check_literal_empty_wordEnd :
    TM.runConfig (M := GNM)
      (GNM.initialConfig
        (gnPoint (encodeGN GNFixedDelegateProbes.emptyProgram))) 20 =
      gnWordEndConfig GNFixedDelegateProbes.emptyProgram :=
  GNFixedDelegateProbes.literal_empty_wordEnd

theorem check_literal_oneConstFalse_wordEnd :
    TM.runConfig (M := GNM)
      (GNM.initialConfig
        (gnPoint (encodeGN GNFixedDelegateProbes.oneConstFalseProgram))) 48 =
      gnWordEndConfig GNFixedDelegateProbes.oneConstFalseProgram :=
  GNFixedDelegateProbes.literal_oneConstFalse_wordEnd

end Pnp3.Tests.TMGateNFixedDelegateRelocationSurface
