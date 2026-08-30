import Complexity.TMVerifier.TuringToolkit.GateOneOutputAccept

/-! # S10b live G1 output/acceptance surface (2026-08-30)

Definitions receive `#check` only.  Every public S10b theorem has one named,
exactly stated wrapper rooted directly in that theorem.
-/

namespace Pnp3.Tests.TMGateOneOutputAcceptSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

#check @g1AcceptConfig
#check @g1GateAcceptSteps

theorem check_g1Transition_accept_predecessor (phase : Fin 1) (s : G1State)
    (scan : Bool) (h : (g1Transition phase s scan).2.1.mode = .accept) :
    s.mode = .accept ∨ s.mode = .outputDoneFalse ∨ s.mode = .outputDoneTrue :=
  g1Transition_accept_predecessor phase s scan h

theorem check_g1Transition_reject_not_accept (phase : Fin 1) (scan : Bool) :
    (g1Transition phase g1RejectState scan).2.1.mode ≠ .accept :=
  g1Transition_reject_not_accept phase scan

theorem check_g1Transition_oob_not_accept (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    (g1Transition phase (g1State .bOOB position b0 b1 b2 ctx) scan).2.1.mode ≠
      .accept :=
  g1Transition_oob_not_accept phase position b0 b1 b2 scan ctx

theorem check_g1Transition_outSeek_malformed_reject (phase : Fin 1)
    (b0 b1 b2 b3 : Bool) (ctx : G1Ctx)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    g1Transition phase (g1State .outSeek .p3 b0 b1 b2 ctx) b3 =
      (0, g1RejectState, b3, .stay) :=
  g1Transition_outSeek_malformed_reject phase b0 b1 b2 b3 ctx hbad

theorem check_g1AcceptConfig_state (r : G1Request) (res : Bool) :
    (g1AcceptConfig r res).state.snd = g1AcceptState :=
  g1AcceptConfig_state r res

theorem check_g1AcceptConfig_head (r : G1Request) (res : Bool) :
    ((g1AcceptConfig r res).head : Nat) = g1OutputExitHead r :=
  g1AcceptConfig_head r res

theorem check_g1AcceptConfig_tape (r : G1Request) (res : Bool) :
    (g1AcceptConfig r res).tape =
      g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) :=
  g1AcceptConfig_tape r res

theorem check_g1CS_step_combine_output (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1CombineConfig r res) 1 =
      g1OutputStartConfig r res :=
  g1CS_step_combine_output r res

theorem check_g1CS_step_outputDone_accept (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1OutputDoneConfig r res) 1 =
      g1AcceptConfig r res :=
  g1CS_step_outputDone_accept r res

theorem check_g1CS_output_accept_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1CombineConfig r res)
        (1 + g1OutputKernelSteps r + 1) = g1AcceptConfig r res :=
  g1CS_output_accept_exact r res

theorem check_g1CS_runConfig_accept_sink (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (k : Nat) :
    TM.runConfig (M := G1M) (g1AlignedConfigQ n h hh tape g1AcceptState) k =
      g1AlignedConfigQ n h hh tape g1AcceptState :=
  g1CS_runConfig_accept_sink n h hh tape k

theorem check_g1GateAcceptSteps_provenance (r : G1Request) :
    g1GateAcceptSteps r =
      g1GateResultSteps r + 1 + g1OutputKernelSteps r + 1 :=
  g1GateAcceptSteps_provenance r

theorem check_g1GateAcceptSteps_closed (r : G1Request) :
    g1GateAcceptSteps r = g1GateResultSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) :=
  g1GateAcceptSteps_closed r

theorem check_g1GateAcceptSteps_const (r : G1Request) (ht : r.tag = .const) :
    g1GateAcceptSteps r = g1ConstActivatedSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) :=
  g1GateAcceptSteps_const r ht

theorem check_g1GateAcceptSteps_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1GateAcceptSteps r = g1BACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) :=
  g1GateAcceptSteps_binary r ht

theorem check_g1GateAcceptSteps_unary (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1GateAcceptSteps r = g1UACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) :=
  g1GateAcceptSteps_unary r ht

theorem check_g1GateAcceptSteps_le_clock (r : G1Request) :
    g1GateAcceptSteps r ≤ g1Clock (encodeG1 r).length :=
  g1GateAcceptSteps_le_clock r

theorem check_g1GateAccept_clock_unchanged (N : Nat) :
    g1CS.timeBound N = 512 * (N + 1) ^ 2 + 512 :=
  g1GateAccept_clock_unchanged N

theorem check_g1CS_gate_accept_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateAcceptSteps r) = g1AcceptConfig r res :=
  g1CS_gate_accept_exact r hc res hs

theorem check_g1CS_gate_accept_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd = g1AcceptState :=
  g1CS_gate_accept_state r hc res hs

theorem check_g1CS_gate_accept_context (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd.ctx = g1Ctx0 :=
  g1CS_gate_accept_context r hc res hs

theorem check_g1CS_gate_accept_head (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).head : Nat) = g1OutputExitHead r :=
  g1CS_gate_accept_head r hc res hs

theorem check_g1CS_gate_accept_tape (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape =
        writeCell (g1OutputPosition r) res
          (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1CS_gate_accept_tape r hc res hs

theorem check_g1CS_gate_accept_frames (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape =
        g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) :=
  g1CS_gate_accept_frames r hc res hs

theorem check_g1CS_gate_accept_output (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape i = res :=
  g1CS_gate_accept_output r hc res hs i hi

theorem check_g1CS_gate_accept_off (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) ≠ g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape i =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape i :=
  g1CS_gate_accept_off r hc res hs i hi

theorem check_g1CS_gate_accept_true_tape_ne (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = some true)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape i ≠
        (G1M.initialConfig (g1Point (encodeG1 r))).tape i :=
  g1CS_gate_accept_true_tape_ne r hc hs i hi

theorem check_g1CS_gate_accept_false_tape_eq (r : G1Request)
    (hc : r.Canonical) (hs : r.spec = some false) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1CS_gate_accept_false_tape_eq r hc hs

theorem check_g1CS_gate_accept_false_ne_oob (r : G1Request)
    (hc : r.Canonical) (hs : r.spec = some false) (ctx : G1Ctx) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd ≠ g1OOBState ctx :=
  g1CS_gate_accept_false_ne_oob r hc hs ctx

theorem check_g1CS_gate_accept_false_ne_reject (r : G1Request)
    (hc : r.Canonical) (hs : r.spec = some false) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd ≠ g1RejectState :=
  g1CS_gate_accept_false_ne_reject r hc hs

theorem check_g1CS_run_accept_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    G1M.run (n := (encodeG1 r).length) (g1Point (encodeG1 r)) =
      g1AcceptConfig r res :=
  g1CS_run_accept_exact r hc res hs

theorem check_g1CS_accepts_of_spec_some (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true :=
  g1CS_accepts_of_spec_some r hc res hs

theorem check_g1CS_reject_not_accept (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (k : Nat) :
    (TM.runConfig (M := G1M)
      (g1AlignedConfigQ n h hh tape g1RejectState) k).state ≠ G1M.accept :=
  g1CS_reject_not_accept n h hh tape k

theorem check_g1CS_oob_not_accept (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) (k : Nat) :
    (TM.runConfig (M := G1M)
      (g1AlignedConfig n h hh tape .bOOB .p0 false false false ctx) k).state ≠
        G1M.accept :=
  g1CS_oob_not_accept n h hh tape ctx k

theorem check_g1CS_outSeek_malformed_reject_stable (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b0 b1 b2 : Bool) (ctx : G1Ctx)
    (hbad : decodeG1Frame? [b0, b1, b2, tape ⟨h, hh⟩] = none) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .outSeek .p3 b0 b1 b2 ctx) (1 + k) =
      g1AlignedConfigQ n h hh tape g1RejectState :=
  g1CS_outSeek_malformed_reject_stable n h hh tape b0 b1 b2 ctx hbad k

theorem check_g1CS_outSeek_malformed_not_accept (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b0 b1 b2 : Bool) (ctx : G1Ctx)
    (hbad : decodeG1Frame? [b0, b1, b2, tape ⟨h, hh⟩] = none) (k : Nat) :
    (TM.runConfig (M := G1M)
      (g1AlignedConfig n h hh tape .outSeek .p3 b0 b1 b2 ctx) (1 + k)).state ≠
        G1M.accept :=
  g1CS_outSeek_malformed_not_accept n h hh tape b0 b1 b2 ctx hbad k

theorem check_g1CS_accepts_false_of_arg2_oob_positive (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (h2 : 0 < r.arg2) (hm : r.vals.length ≤ r.arg2) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false :=
  g1CS_accepts_false_of_arg2_oob_positive r hc ht h2 hm

theorem check_g1CS_accepts_false_of_arg2_oob_zero (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (h2 : r.arg2 = 0) (hb : r.vals[r.arg2]? = none) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false :=
  g1CS_accepts_false_of_arg2_oob_zero r hc ht h2 hb

open G1AResultProbes

theorem check_literal_steps :
    g1GateAcceptSteps reqInputT = 230 ∧ g1GateAcceptSteps reqNotF = 286 ∧
      g1GateAcceptSteps reqAndF = 485 ∧ g1GateAcceptSteps reqOrT = 513 ∧
      g1GateAcceptSteps reqConstF = 152 ∧ g1GateAcceptSteps reqConstT = 172 :=
  G1OutputAcceptProbes.literal_steps

theorem check_literal_clocks :
    g1Clock (encodeG1 reqInputT).length = 558080 ∧
      g1Clock (encodeG1 reqNotF).length = 861184 ∧
      g1Clock (encodeG1 reqAndF).length = 1438720 ∧
      g1Clock (encodeG1 reqOrT).length = 1664000 ∧
      g1Clock (encodeG1 reqConstF).length = 558080 ∧
      g1Clock (encodeG1 reqConstT).length = 701440 :=
  G1OutputAcceptProbes.literal_clocks

theorem check_literal_accepts :
    TM.accepts (M := G1M) (encodeG1 reqInputT).length
        (g1Point (encodeG1 reqInputT)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqNotF).length
        (g1Point (encodeG1 reqNotF)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqAndF).length
        (g1Point (encodeG1 reqAndF)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqOrT).length
        (g1Point (encodeG1 reqOrT)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqConstF).length
        (g1Point (encodeG1 reqConstF)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqConstT).length
        (g1Point (encodeG1 reqConstT)) = true :=
  G1OutputAcceptProbes.literal_accepts

theorem check_literal_false_output
    (i : Fin (G1M.tapeLength (encodeG1 reqAndF).length))
    (hi : (i : Nat) = g1OutputPosition reqAndF) :
    (TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 485).tape i = false :=
  G1OutputAcceptProbes.literal_false_output i hi

theorem check_literal_true_output
    (i : Fin (G1M.tapeLength (encodeG1 reqOrT).length))
    (hi : (i : Nat) = g1OutputPosition reqOrT) :
    (TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 513).tape i = true :=
  G1OutputAcceptProbes.literal_true_output i hi

end Pnp3.Tests.TMGateOneOutputAcceptSurface
