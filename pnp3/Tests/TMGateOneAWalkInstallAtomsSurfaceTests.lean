import Complexity.TMVerifier.TuringToolkit.GateOneAWalkInstallAtoms

/-!
# S4 live operand-A cursor-installation surface (2026-08-29)

Every public source theorem has one exact named wrapper below; definitions are
checked only.  S4 includes real-initial unary/binary success and unary empty-data
OOB capstones, literal false/true probes, unchanged-clock bounds, and exact
post-writer no-wrong-exit closure.  No normal-walk step executes.
-/

namespace Pnp3.Tests.TMGateOneAWalkInstallAtomsSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

#check @G1Mode.aInsSeek
#check @G1Mode.aProbe
#check @G1Mode.aLatchFalse
#check @G1Mode.aLatchTrue
#check @G1Mode.aIns
#check @g1AInsSeekState
#check @g1AProbeState
#check @g1AInsState
#check @g1ALatchMode
#check @G1AInstallAtomMode
#check @G1AInstallSkip
#check @g1AInstallCursorWriter
#check @g1AInstallSkippedFrames
#check @g1ALiveInstallSteps
#check @g1ALiveInstallOOBSteps
#check @g1AFirstCursorFrames
#check @g1APostWriterConfig
#check @g1AInstallOOBConfig
#check @g1AUnaryCursorSteps
#check @g1ABinaryCursorSteps
#check @g1AUnaryOOBSteps
#check @G1ALiveInstallExamples.reqInputFalse
#check @G1ALiveInstallExamples.reqNotTrue
#check @G1ALiveInstallExamples.reqAndFalse
#check @G1ALiveInstallExamples.reqOrTrue
#check @G1ALiveInstallExamples.reqInputOOB

theorem check_g1Advance_aInstallAtoms_dormant (mode : G1Mode)
    (frame : G1Frame) :
    G1AInstallAtomMode (g1Advance mode frame) → G1AInstallAtomMode mode :=
  g1Advance_aInstallAtoms_dormant mode frame

theorem check_g1Complete_aInstallAtoms_dormant (mode : G1Mode)
    (b0 b1 b2 b3 : Bool) :
    G1AInstallAtomMode (g1Complete mode b0 b1 b2 b3) →
      G1AInstallAtomMode mode :=
  g1Complete_aInstallAtoms_dormant mode b0 b1 b2 b3

theorem check_g1Complete_aInstallAtoms_reserved (mode : G1Mode) :
    g1Complete mode true true false true = .reject ∧
      g1Complete mode true true true false = .reject ∧
      g1Complete mode true true true true = .reject :=
  g1Complete_aInstallAtoms_reserved mode

theorem check_g1Transition_aLatch (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1ALatchMode b) position b0 b1 b2 ctx) scan =
      (0, g1AInsState (ctx.withVB b), scan, .left) :=
  g1Transition_aLatch phase b position b0 b1 b2 scan ctx

theorem check_g1Transition_aIns_p3 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aIns .p3 b0 b1 b2 ctx) scan =
      (0, g1State .aIns .p2 false false false ctx, true, .left) :=
  g1Transition_aIns_p3 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aIns_p2 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aIns .p2 b0 b1 b2 ctx) scan =
      (0, g1State .aIns .p1 false false false ctx, true, .left) :=
  g1Transition_aIns_p2 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aIns_p1 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aIns .p1 b0 b1 b2 ctx) scan =
      (0, g1State .aIns .p0 false false false ctx, true, .left) :=
  g1Transition_aIns_p1 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aIns_p0 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .aIns .p0 b0 b1 b2 ctx) scan =
      (0, g1ASeekOutState ctx, false, .left) :=
  g1Transition_aIns_p0 phase b0 b1 b2 scan ctx

theorem check_g1Transition_aInstallAtoms_entry_closure (phase : Fin 1)
    (s : G1State)
    (scan : Bool)
    (h : G1AInstallAtomMode (g1Transition phase s scan).2.1.mode) :
    G1AWalkMode s.mode ∨ s.mode = .aInstallStart :=
  g1Transition_aInstallAtoms_entry_closure phase s scan h

theorem check_g1Advance_aInsSeek_of_skip {frame : G1Frame}
    (h : G1AInstallSkip frame) :
    g1Advance .aInsSeek frame = .aInsSeek :=
  g1Advance_aInsSeek_of_skip h

theorem check_g1Advance_aProbe_data (v : Bool) :
    g1Advance .aProbe (.data v) = g1ALatchMode v :=
  g1Advance_aProbe_data v

theorem check_g1Advance_aInsSeek_rows :
    g1Advance .aInsSeek .index = .aInsSeek ∧
      g1Advance .aInsSeek .spent = .aInsSeek ∧
      g1Advance .aInsSeek .argSep = .aInsSeek ∧
      g1Advance .aInsSeek .separator = .aProbe :=
  g1Advance_aInsSeek_rows

theorem check_g1Advance_aProbe_rows :
    g1Advance .aProbe (.data false) = .aLatchFalse ∧
      g1Advance .aProbe (.data true) = .aLatchTrue ∧
      g1Advance .aProbe (.output false) = .bOOB :=
  g1Advance_aProbe_rows

theorem check_g1Advance_aInstallAtoms_rejects :
    g1Advance .aInsSeek (.data false) = .reject ∧
      g1Advance .aInsSeek (.output false) = .reject ∧
      g1Advance .aProbe .index = .reject ∧
      g1Advance .aProbe .separator = .reject ∧
      g1Advance .aProbe (.output true) = .reject :=
  g1Advance_aInstallAtoms_rejects

theorem check_g1AInstallCursorWriter_machine :
    g1AInstallCursorWriter.machine = G1M :=
  g1AInstallCursorWriter_machine

theorem check_g1CS_aInstall_scan (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1AInstallSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.separator :: suffix).flatMap G1Frame.bits))
        .aInsSeek .p0 false false false ctx) (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.separator :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx :=
  g1CS_aInstall_scan n pre skipped suffix ctx hskip hsafe

theorem check_g1CS_aProbe_latch (n : Nat) (pre suffix : List G1Frame)
    (v : Bool) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx) 5 =
      g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .aIns .p3 false false false (ctx.withVB v) :=
  g1CS_aProbe_latch n pre suffix v ctx hsafe

theorem check_g1CS_aProbe_oob (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .bOOB .p0 false false false ctx :=
  g1CS_aProbe_oob n pre suffix ctx hsafe

theorem check_g1CS_aInstall_reserved_1101_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : mode = .aInsSeek ∨ mode = .aProbe)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n base (by omega) tape mode .p0
          false false false ctx) 4 =
      g1AlignedConfig n (base + 3) (by omega) tape .reject .p0
        false false false g1Ctx0 :=
  g1CS_aInstall_reserved_1101_reject n base hsafe tape mode ctx hmode hbits

theorem check_g1CS_aInstall_cursor (n : Nat) (pre suffix : List G1Frame)
    (old : G1Frame) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ old :: suffix).flatMap G1Frame.bits))
        .aIns .p3 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aSeekOut .p3 false false false ctx :=
  g1CS_aInstall_cursor n pre suffix old ctx hpre hsafe

/-! ## Exact S4 live-capstone pins -/

theorem check_g1AInstallSkippedFrames_length (r : G1Request) :
    (g1AInstallSkippedFrames r).length = r.arg1 + r.arg2 + 1 :=
  g1AInstallSkippedFrames_length r

theorem check_g1APostWriterConfig_res (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.ctx.res =
      g1Residual r.tag bB :=
  g1APostWriterConfig_res r bA bB

theorem check_g1APostWriterConfig_vB (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.ctx.vB = bA :=
  g1APostWriterConfig_vB r bA bB

theorem check_g1APostWriterConfig_mode (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.mode = .aSeekOut :=
  g1APostWriterConfig_mode r bA bB

theorem check_g1CS_aInstall_success_exact (r : G1Request) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (g1AInstallConfig r bB)
        (g1ALiveInstallSteps r) = g1APostWriterConfig r bA bB :=
  g1CS_aInstall_success_exact r bA bB rest hv

theorem check_g1CS_aInstall_oob_exact (r : G1Request) (bB : Bool)
    (hv : r.vals = []) :
    TM.runConfig (M := G1M) (g1AInstallConfig r bB)
        (g1ALiveInstallOOBSteps r) = g1AInstallOOBConfig r bB :=
  g1CS_aInstall_oob_exact r bB hv

theorem check_g1CS_aCursor_unary_initial_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (bA : Bool) (rest : List Bool) (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r) = g1APostWriterConfig r bA false :=
  g1CS_aCursor_unary_initial_exact r hc ht bA rest hv

theorem check_g1CS_aCursor_binary_initial_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r) = g1APostWriterConfig r bA bB :=
  g1CS_aCursor_binary_initial_exact r hc ht bA bB rest hB hv

theorem check_g1CS_aInstall_unary_oob_initial_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (hv : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryOOBSteps r) = g1AInstallOOBConfig r false :=
  g1CS_aInstall_unary_oob_initial_exact r hc ht hv

theorem check_g1A_binary_success_not_empty (r : G1Request) (b : Bool)
    (hB : r.vals[r.arg2]? = some b) : r.vals ≠ [] :=
  g1A_binary_success_not_empty r b hB

theorem check_g1AFirstCursorFrames_count_cursor (r : G1Request) :
    (g1AFirstCursorFrames r).count .cursor = 1 :=
  g1AFirstCursorFrames_count_cursor r

theorem check_g1APostWriterConfig_head (r : G1Request) (bA bB : Bool) :
    ((g1APostWriterConfig r bA bB).head : Nat) =
      4 * (r.tag.units + r.arg1 + r.arg2 + 4) - 1 :=
  g1APostWriterConfig_head r bA bB

theorem check_g1APostWriterConfig_tape (r : G1Request) (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).tape =
      g1ListTape ((g1AFirstCursorFrames r).flatMap G1Frame.bits) :=
  g1APostWriterConfig_tape r bA bB

theorem check_g1APostWriterConfig_no_wrong_exit (r : G1Request)
    (bA bB : Bool) :
    (g1APostWriterConfig r bA bB).state.snd.mode = .aSeekOut ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .aIns ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .aProbe ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .aRepairStart ∧
      (g1APostWriterConfig r bA bB).state.snd.mode ≠ .combineStart :=
  g1APostWriterConfig_no_wrong_exit r bA bB

theorem check_g1AUnaryCursorSteps_le_clock (r : G1Request) :
    g1AUnaryCursorSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AUnaryCursorSteps_le_clock r

theorem check_g1ABinaryCursorSteps_le_clock (r : G1Request) :
    g1ABinaryCursorSteps r ≤ g1Clock (encodeG1 r).length :=
  g1ABinaryCursorSteps_le_clock r

theorem check_g1AUnaryOOBSteps_le_clock (r : G1Request) :
    g1AUnaryOOBSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AUnaryOOBSteps_le_clock r

theorem check_g1CS_aCursor_unary_no_wrong_exit (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (bA : Bool) (rest : List Bool) (hv : r.vals = bA :: rest) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r)).state.snd.mode = .aSeekOut ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r)).state.snd.mode ≠ .combineStart :=
  g1CS_aCursor_unary_no_wrong_exit r hc ht bA rest hv

theorem check_g1CS_aCursor_binary_no_wrong_exit (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (hv : r.vals = bA :: rest) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r)).state.snd.mode = .aSeekOut ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r)).state.snd.mode ≠ .combineStart :=
  g1CS_aCursor_binary_no_wrong_exit r hc ht bA bB rest hB hv

theorem check_live_requests_canonical :
    G1ALiveInstallExamples.reqInputFalse.Canonical ∧
      G1ALiveInstallExamples.reqNotTrue.Canonical ∧
      G1ALiveInstallExamples.reqAndFalse.Canonical ∧
      G1ALiveInstallExamples.reqOrTrue.Canonical ∧
      G1ALiveInstallExamples.reqInputOOB.Canonical :=
  G1ALiveInstallExamples.requests_canonical

theorem check_input_false_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqInputFalse))) 131 =
      g1APostWriterConfig G1ALiveInstallExamples.reqInputFalse false false :=
  G1ALiveInstallExamples.input_false_cursor_exact

theorem check_not_true_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqNotTrue))) 171 =
      g1APostWriterConfig G1ALiveInstallExamples.reqNotTrue true false :=
  G1ALiveInstallExamples.not_true_cursor_exact

theorem check_and_false_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqAndFalse))) 216 =
      g1APostWriterConfig G1ALiveInstallExamples.reqAndFalse false false :=
  G1ALiveInstallExamples.and_false_cursor_exact

theorem check_or_true_cursor_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqOrTrue))) 236 =
      g1APostWriterConfig G1ALiveInstallExamples.reqOrTrue true true :=
  G1ALiveInstallExamples.or_true_cursor_exact

theorem check_input_empty_oob_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqInputOOB))) 118 =
      g1AInstallOOBConfig G1ALiveInstallExamples.reqInputOOB false :=
  G1ALiveInstallExamples.input_empty_oob_exact

theorem check_literal_clock_bounds :
    131 ≤ g1Clock (encodeG1 G1ALiveInstallExamples.reqInputFalse).length ∧
      171 ≤ g1Clock (encodeG1 G1ALiveInstallExamples.reqNotTrue).length ∧
      216 ≤ g1Clock (encodeG1 G1ALiveInstallExamples.reqAndFalse).length ∧
      236 ≤ g1Clock (encodeG1 G1ALiveInstallExamples.reqOrTrue).length ∧
      118 ≤ g1Clock (encodeG1 G1ALiveInstallExamples.reqInputOOB).length :=
  G1ALiveInstallExamples.literal_clock_bounds

/-! ## Literal caller-supplied nonvacuity probes -/

theorem literal_install_scan (n : Nat) (hsafe : 20 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 4 (by omega)
        (g1ListTape
          ([G1Frame.bof, .index, .argSep, .spent, .separator,
            .data false].flatMap G1Frame.bits))
        .aInsSeek .p0 false false false ⟨false, true, true⟩) 16 =
      g1AlignedConfig n 20 hsafe
        (g1ListTape
          ([G1Frame.bof, .index, .argSep, .spent, .separator,
            .data false].flatMap G1Frame.bits))
        .aProbe .p0 false false false ⟨false, true, true⟩ := by
  simpa using g1CS_aInstall_scan n [G1Frame.bof]
    [G1Frame.index, G1Frame.argSep, G1Frame.spent]
    [.data false] ⟨false, true, true⟩ (by simp [G1AInstallSkip]) hsafe

theorem literal_probe_latch_false (n : Nat) (hsafe : 8 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 4 (by omega)
        (g1ListTape ([G1Frame.bof, .data false, .output false].flatMap
          G1Frame.bits)) .aProbe .p0 false false false g1Ctx0) 5 =
      g1AlignedConfig n 7 (by omega)
        (g1ListTape ([G1Frame.bof, .data false, .output false].flatMap
          G1Frame.bits)) .aIns .p3 false false false (g1Ctx0.withVB false) := by
  simpa using g1CS_aProbe_latch n [.bof] [.output false] false g1Ctx0 hsafe

theorem literal_probe_latch_true (n : Nat) (hsafe : 8 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 4 (by omega)
        (g1ListTape ([G1Frame.bof, .data true, .output false].flatMap
          G1Frame.bits)) .aProbe .p0 false false false g1Ctx0) 5 =
      g1AlignedConfig n 7 (by omega)
        (g1ListTape ([G1Frame.bof, .data true, .output false].flatMap
          G1Frame.bits)) .aIns .p3 false false false (g1Ctx0.withVB true) := by
  simpa using g1CS_aProbe_latch n [.bof] [.output false] true g1Ctx0 hsafe

theorem literal_probe_oob (n : Nat) (hsafe : 8 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 4 (by omega)
        (g1ListTape ([G1Frame.bof, .output false, .finish].flatMap G1Frame.bits))
        .aProbe .p0 false false false g1Ctx0) 4 =
      g1AlignedConfig n 8 hsafe
        (g1ListTape ([G1Frame.bof, .output false, .finish].flatMap G1Frame.bits))
        .bOOB .p0 false false false g1Ctx0 := by
  simpa using g1CS_aProbe_oob n [.bof] [.finish] g1Ctx0 hsafe

theorem literal_reserved_1101_reject (n : Nat)
    (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 0 (by omega)
        (g1ListTape [true, true, false, true]) .aProbe .p0
          false false false g1Ctx0) 4 =
      g1AlignedConfig n 3 (by omega) (g1ListTape [true, true, false, true])
        .reject .p0 false false false g1Ctx0 := by
  apply g1CS_aInstall_reserved_1101_reject n 0 hsafe _ .aProbe g1Ctx0
    (Or.inr rfl)
  rfl

theorem literal_install_cursor (n : Nat) (hsafe : 8 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 7 (by omega)
        (g1ListTape ([G1Frame.bof, .data true, .output false].flatMap
          G1Frame.bits)) .aIns .p3 false false false ⟨false, true, true⟩) 4 =
      g1AlignedConfig n 3 (by omega)
        (g1ListTape ([G1Frame.bof, .cursor, .output false].flatMap G1Frame.bits))
        .aSeekOut .p3 false false false ⟨false, true, true⟩ := by
  simpa using g1CS_aInstall_cursor n [.bof] [.output false] (.data true)
    ⟨false, true, true⟩ (by decide) hsafe

end Pnp3.Tests.TMGateOneAWalkInstallAtomsSurface
