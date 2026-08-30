import Complexity.TMVerifier.TuringToolkit.GateOneOutputKernel

/-!
# S10b live G1 output and acceptance (2026-08-30)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

This module activates S10a without adding runtime data or advice.  One exact
stationary step sends `combineStart` to `outSeek`; the existing strict kernel
scans and writes `output res`; one final stationary step sends either
`outputDoneFalse` or `outputDoneTrue` to the same literal `g1AcceptState`.
Thus `false` accepts exactly when it is a defined computation result.

For canonical `r` with `r.spec = some res`, the exact real-initial total is

`g1GateAcceptSteps r = g1GateResultSteps r + 1 + g1OutputKernelSteps r + 1`.

The public `TM.accepts` theorem pads only in the literal accept sink to the
unchanged `g1Clock`.  Separate exact theorems keep reject, `bOOB`, and malformed
output-scan paths nonaccepting.  No multi-gate claim is made here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Exact transition predecessor boundaries -/

private theorem g1Complete_ne_accept (mode : G1Mode) (b0 b1 b2 b3 : Bool) :
    g1Complete mode b0 b1 b2 b3 ≠ .accept := by
  unfold g1Complete
  cases decodeG1Frame? [b0, b1, b2, b3] with
  | none => exact fun h => G1Mode.noConfusion h
  | some frame => exact (g1Advance_ne_sink mode frame).1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
/-- The only predecessors of an accepting successor are the accept sink and
the two literal output-done handoffs. -/
theorem g1Transition_accept_predecessor (phase : Fin 1) (s : G1State)
    (scan : Bool) (h : (g1Transition phase s scan).2.1.mode = .accept) :
    s.mode = .accept ∨ s.mode = .outputDoneFalse ∨ s.mode = .outputDoneTrue := by
  obtain ⟨mode, position, b0, b1, b2, ctx⟩ := s
  obtain ⟨pass, crossed, vB⟩ := ctx
  cases mode <;> cases position <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
      | exact G1Mode.noConfusion h
      | (cases vB <;> exact G1Mode.noConfusion h)
      | (cases pass <;> exact G1Mode.noConfusion h)
      | (simp only [g1Transition, g1State] at h
         split at h <;>
           first
             | exact G1Mode.noConfusion h
             | exact absurd h (g1Complete_ne_accept _ _ _ _ _))

theorem g1Transition_reject_not_accept (phase : Fin 1) (scan : Bool) :
    (g1Transition phase g1RejectState scan).2.1.mode ≠ .accept := by
  rw [g1Transition_reject_sink]
  intro h
  exact G1Mode.noConfusion h

theorem g1Transition_oob_not_accept (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    (g1Transition phase (g1State .bOOB position b0 b1 b2 ctx) scan).2.1.mode ≠
      .accept := by
  rw [g1Transition_bOOB_stable]
  intro h
  exact G1Mode.noConfusion h

/-- An undecodable output-scan window enters the literal reject sink. -/
theorem g1Transition_outSeek_malformed_reject (phase : Fin 1)
    (b0 b1 b2 b3 : Bool) (ctx : G1Ctx)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    g1Transition phase (g1State .outSeek .p3 b0 b1 b2 ctx) b3 =
      (0, g1RejectState, b3, .stay) := by
  have hcomplete := (g1Complete_outSeek_malformed_reserved hbad).1
  simp only [g1Transition, g1State]
  rw [hcomplete]
  rfl

/-! ## The two live doors and the exact accepting endpoint -/

/-- Exact endpoint: literal accept control, exact output tape and exit head. -/
def g1AcceptConfig (r : G1Request) (res : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfigQ (encodeG1 r).length (g1OutputExitHead r)
    (g1OutputExitHead_safe r)
    (g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits)) g1AcceptState

@[simp] theorem g1AcceptConfig_state (r : G1Request) (res : Bool) :
    (g1AcceptConfig r res).state.snd = g1AcceptState := rfl

@[simp] theorem g1AcceptConfig_head (r : G1Request) (res : Bool) :
    ((g1AcceptConfig r res).head : Nat) = g1OutputExitHead r := rfl

@[simp] theorem g1AcceptConfig_tape (r : G1Request) (res : Bool) :
    (g1AcceptConfig r res).tape =
      g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) := rfl

theorem g1CS_step_combine_output (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1CombineConfig r res) 1 =
      g1OutputStartConfig r res := by
  rw [runConfig_one, g1CombineConfig, g1OutputStartConfig]
  have hstep := g1CS_aligned_step_stay (encodeG1 r).length 0
    (g1_route_lt_tapeLength r 0 (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    (g1CombineState (g1ResultCtx res)) (g1OutSeekState (g1ResultCtx res))
    ((G1M.initialConfig (g1Point (encodeG1 r))).tape
      ⟨0, g1_route_lt_tapeLength r 0 (by omega)⟩)
    (fun phase => g1Transition_combineStart_output phase .p0 false false false _ _)
  rwa [writeCell_self] at hstep

theorem g1CS_step_outputDone_accept (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1OutputDoneConfig r res) 1 =
      g1AcceptConfig r res := by
  rw [runConfig_one, g1OutputDoneConfig, g1AcceptConfig]
  have hstep := g1CS_aligned_step_stay (encodeG1 r).length
    (g1OutputExitHead r) (g1OutputExitHead_safe r)
    (g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits))
    (g1OutputDoneState res) g1AcceptState
    (g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits)
      ⟨g1OutputExitHead r, g1OutputExitHead_safe r⟩)
    (fun phase => g1Transition_outputDone_accept phase res _)
  rwa [writeCell_self] at hstep

/-- Combine door, exact S10a kernel, and accept door; no padding. -/
theorem g1CS_output_accept_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1CombineConfig r res)
        (1 + g1OutputKernelSteps r + 1) = g1AcceptConfig r res := by
  rw [show 1 + g1OutputKernelSteps r + 1 =
      1 + (g1OutputKernelSteps r + 1) by omega,
    runConfig_add, g1CS_step_combine_output, runConfig_add,
    g1CS_output_kernel_exact, g1CS_step_outputDone_accept]

/-- Only the literal accept sink is used for padding. -/
theorem g1CS_runConfig_accept_sink (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (k : Nat) :
    TM.runConfig (M := G1M) (g1AlignedConfigQ n h hh tape g1AcceptState) k =
      g1AlignedConfigQ n h hh tape g1AcceptState :=
  g1CS_runConfig_stable n h hh tape g1AcceptState
    (fun phase scan => g1Transition_accept_sink phase scan) k

/-! ## Concrete five-tag schedule and unchanged clock -/

def g1GateAcceptSteps (r : G1Request) : Nat :=
  g1GateResultSteps r + (1 + g1OutputKernelSteps r + 1)

theorem g1GateAcceptSteps_provenance (r : G1Request) :
    g1GateAcceptSteps r =
      g1GateResultSteps r + 1 + g1OutputKernelSteps r + 1 := by
  rw [g1GateAcceptSteps]
  omega

theorem g1GateAcceptSteps_closed (r : G1Request) :
    g1GateAcceptSteps r = g1GateResultSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) := by
  rw [g1GateAcceptSteps, g1OutputKernelSteps]
  omega

theorem g1GateAcceptSteps_const (r : G1Request) (ht : r.tag = .const) :
    g1GateAcceptSteps r = g1ConstActivatedSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) := by
  rw [g1GateAcceptSteps_closed, g1GateResultSteps_const r ht]

theorem g1GateAcceptSteps_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1GateAcceptSteps r = g1BACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) := by
  rw [g1GateAcceptSteps_closed, g1GateResultSteps_binary r ht]

theorem g1GateAcceptSteps_unary (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1GateAcceptSteps r = g1UACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) := by
  rw [g1GateAcceptSteps_closed, g1GateResultSteps_unary r ht]

private theorem g1AcceptClock_eq (r : G1Request) :
    g1Clock (encodeG1 r).length =
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 +
        (4096 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) + 1024) := by
  rw [encodeG1_length r, g1ResultClock_quad]

private theorem g1BAAcceptSteps_le_clock (r : G1Request) :
    g1BACombineSteps r +
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) ≤
      g1Clock (encodeG1 r).length := by
  have h := g1ABinaryRepairSteps_le_poly r
  rw [g1ARepairLivePoly] at h
  rw [g1AcceptClock_eq, g1BACombineSteps]
  omega

private theorem g1UAAcceptSteps_le_clock (r : G1Request) :
    g1UACombineSteps r +
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) ≤
      g1Clock (encodeG1 r).length := by
  have h := g1AUnaryRepairSteps_le_poly r
  rw [g1ARepairLivePoly] at h
  rw [g1AcceptClock_eq, g1UACombineSteps]
  omega

private theorem g1ConstAcceptSteps_le_clock (r : G1Request) :
    g1ConstActivatedSteps r +
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 11) ≤
      g1Clock (encodeG1 r).length := by
  have hlen := encodeG1_length r
  rw [g1AcceptClock_eq]
  simp only [g1ConstActivatedSteps, g1ConstReadASteps, g1ConstRouteSteps,
    g1FieldRouteSteps, g1ReadBHandoffSteps, g1AConstRewindSteps, hlen]
  omega

theorem g1GateAcceptSteps_le_clock (r : G1Request) :
    g1GateAcceptSteps r ≤ g1Clock (encodeG1 r).length := by
  rw [g1GateAcceptSteps_closed, g1GateResultSteps]
  split_ifs
  · exact g1ConstAcceptSteps_le_clock r
  · exact g1BAAcceptSteps_le_clock r
  · exact g1UAAcceptSteps_le_clock r

theorem g1GateAccept_clock_unchanged (N : Nat) :
    g1CS.timeBound N = 512 * (N + 1) ^ 2 + 512 := rfl

/-! ## Exact real-initial and genuine `TM.accepts` theorems -/

theorem g1CS_gate_accept_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateAcceptSteps r) = g1AcceptConfig r res := by
  rw [g1GateAcceptSteps, runConfig_add, g1CS_gate_result_exact r hc res hs]
  exact g1CS_output_accept_exact r res

theorem g1CS_gate_accept_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd = g1AcceptState := by
  rw [g1CS_gate_accept_exact r hc res hs]
  rfl

theorem g1CS_gate_accept_context (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd.ctx = g1Ctx0 := by
  rw [g1CS_gate_accept_state r hc res hs]
  rfl

theorem g1CS_gate_accept_head (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).head : Nat) = g1OutputExitHead r := by
  rw [g1CS_gate_accept_exact r hc res hs]
  rfl

theorem g1CS_gate_accept_tape (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape =
        writeCell (g1OutputPosition r) res
          (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_gate_accept_exact r hc res hs, g1AcceptConfig_tape,
    g1OutputTape_eq_writeCell]

theorem g1CS_gate_accept_frames (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape =
        g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) := by
  rw [g1CS_gate_accept_exact r hc res hs]
  rfl

theorem g1CS_gate_accept_output (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape i = res := by
  rw [g1CS_gate_accept_tape r hc res hs]
  simp [writeCell, hi]

theorem g1CS_gate_accept_off (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) ≠ g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape i =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape i := by
  rw [g1CS_gate_accept_tape r hc res hs]
  simp [writeCell, hi]

theorem g1CS_gate_accept_true_tape_ne (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = some true)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape i ≠
        (G1M.initialConfig (g1Point (encodeG1 r))).tape i := by
  rw [g1CS_gate_accept_exact r hc true hs, g1AcceptConfig_tape]
  exact g1OutputTape_true_ne_initial r i hi

theorem g1CS_gate_accept_false_tape_eq (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = some false) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_gate_accept_exact r hc false hs, g1AcceptConfig_tape]
  exact g1OutputTape_false_identity r

theorem g1CS_gate_accept_false_ne_oob (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = some false) (ctx : G1Ctx) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd ≠ g1OOBState ctx := by
  rw [g1CS_gate_accept_state r hc false hs]
  intro hstate
  exact G1Mode.noConfusion (congrArg G1State.mode hstate)

theorem g1CS_gate_accept_false_ne_reject (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = some false) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateAcceptSteps r)).state.snd ≠ g1RejectState := by
  rw [g1CS_gate_accept_state r hc false hs]
  intro hstate
  exact G1Mode.noConfusion (congrArg G1State.mode hstate)

theorem g1CS_run_accept_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    G1M.run (n := (encodeG1 r).length) (g1Point (encodeG1 r)) =
      g1AcceptConfig r res := by
  have hle := g1GateAcceptSteps_le_clock r
  obtain ⟨k, hk⟩ : ∃ k, g1Clock (encodeG1 r).length =
      g1GateAcceptSteps r + k :=
    ⟨g1Clock (encodeG1 r).length - g1GateAcceptSteps r, by omega⟩
  rw [show G1M.run (n := (encodeG1 r).length) (g1Point (encodeG1 r)) =
      TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length) from rfl,
    hk, runConfig_add, g1CS_gate_accept_exact r hc res hs,
    g1AcceptConfig]
  exact g1CS_runConfig_accept_sink _ _ _ _ k

/-- Genuine repository `TM.accepts`: defined false and true results both
accept, because the complete dependent state equals `G1M.accept`. -/
theorem g1CS_accepts_of_spec_some (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true := by
  unfold TM.accepts
  rw [g1CS_run_accept_exact r hc res hs]
  exact decide_eq_true rfl

/-! ## Reject, OOB, and malformed nonacceptance -/

theorem g1CS_reject_not_accept (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (k : Nat) :
    (TM.runConfig (M := G1M)
      (g1AlignedConfigQ n h hh tape g1RejectState) k).state ≠ G1M.accept := by
  rw [g1CS_runConfig_reject_sink]
  intro hstate
  exact G1Mode.noConfusion (congrArg (fun q => q.snd.mode) hstate)

theorem g1CS_oob_not_accept (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (k : Nat) :
    (TM.runConfig (M := G1M)
      (g1AlignedConfig n h hh tape .bOOB .p0 false false false ctx) k).state ≠
        G1M.accept := by
  rw [g1CS_runConfig_oob_sink]
  intro hstate
  exact G1Mode.noConfusion (congrArg (fun q => q.snd.mode) hstate)

theorem g1CS_outSeek_malformed_reject_stable (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b0 b1 b2 : Bool) (ctx : G1Ctx)
    (hbad : decodeG1Frame? [b0, b1, b2, tape ⟨h, hh⟩] = none) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .outSeek .p3 b0 b1 b2 ctx) (1 + k) =
      g1AlignedConfigQ n h hh tape g1RejectState := by
  change TM.runConfig (M := G1M)
      (g1AlignedConfigQ n h hh tape
        (g1State .outSeek .p3 b0 b1 b2 ctx)) (1 + k) = _
  rw [runConfig_add, runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape
    (g1State .outSeek .p3 b0 b1 b2 ctx) g1RejectState (tape ⟨h, hh⟩)
    (fun phase => g1Transition_outSeek_malformed_reject phase b0 b1 b2 _ ctx hbad)
  rw [writeCell_self] at hstep
  rw [hstep]
  exact g1CS_runConfig_reject_sink n h hh tape k

theorem g1CS_outSeek_malformed_not_accept (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b0 b1 b2 : Bool) (ctx : G1Ctx)
    (hbad : decodeG1Frame? [b0, b1, b2, tape ⟨h, hh⟩] = none) (k : Nat) :
    (TM.runConfig (M := G1M)
      (g1AlignedConfig n h hh tape .outSeek .p3 b0 b1 b2 ctx) (1 + k)).state ≠
        G1M.accept := by
  rw [g1CS_outSeek_malformed_reject_stable n h hh tape b0 b1 b2 ctx hbad k]
  intro hstate
  exact G1Mode.noConfusion (congrArg (fun q => q.snd.mode) hstate)

private theorem g1OOBFullState_ne_accept (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    (g1AlignedConfig n h hh tape .bOOB .p0 false false false ctx).state ≠
      G1M.accept := by
  intro hstate
  have hmode : G1Mode.bOOB = .accept :=
    congrArg (fun q => q.snd.mode) hstate
  exact G1Mode.noConfusion hmode

theorem g1CS_accepts_false_of_arg2_oob_positive (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (h2 : 0 < r.arg2) (hm : r.vals.length ≤ r.arg2) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false := by
  have hle := g1BOOBSteps_le_clock r
  obtain ⟨k, hk⟩ : ∃ k, g1Clock (encodeG1 r).length = g1BOOBSteps r + k :=
    ⟨g1Clock (encodeG1 r).length - g1BOOBSteps r, by omega⟩
  unfold TM.accepts TM.run
  rw [show G1M.runTime (encodeG1 r).length = g1Clock (encodeG1 r).length from rfl,
    hk, g1CS_readB_positive_oob_stable r hc ht h2 hm k]
  exact decide_eq_false (g1OOBFullState_ne_accept _ _ _ _ _)

theorem g1CS_accepts_false_of_arg2_oob_zero (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (h2 : r.arg2 = 0) (hb : r.vals[r.arg2]? = none) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false := by
  have hle := g1ReadBOOBSteps_le_clock r
  obtain ⟨k, hk⟩ : ∃ k, g1Clock (encodeG1 r).length = g1ReadBOOBSteps r + k :=
    ⟨g1Clock (encodeG1 r).length - g1ReadBOOBSteps r, by omega⟩
  unfold TM.accepts TM.run
  rw [show G1M.runTime (encodeG1 r).length = g1Clock (encodeG1 r).length from rfl,
    hk, g1CS_readB_zero_oob_stable r hc ht h2 hb k]
  exact decide_eq_false (g1OOBFullState_ne_accept _ _ _ _ _)

/-! ## Literal all-five-tag acceptance probes -/

namespace G1OutputAcceptProbes

open G1AResultProbes

theorem literal_steps :
    g1GateAcceptSteps reqInputT = 230 ∧
      g1GateAcceptSteps reqNotF = 286 ∧
      g1GateAcceptSteps reqAndF = 485 ∧
      g1GateAcceptSteps reqOrT = 513 ∧
      g1GateAcceptSteps reqConstF = 152 ∧
      g1GateAcceptSteps reqConstT = 172 := by
  decide

theorem literal_clocks :
    g1Clock (encodeG1 reqInputT).length = 558080 ∧
      g1Clock (encodeG1 reqNotF).length = 861184 ∧
      g1Clock (encodeG1 reqAndF).length = 1438720 ∧
      g1Clock (encodeG1 reqOrT).length = 1664000 ∧
      g1Clock (encodeG1 reqConstF).length = 558080 ∧
      g1Clock (encodeG1 reqConstT).length = 701440 :=
  G1AResultProbes.literal_clocks

theorem literal_accepts :
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
        (g1Point (encodeG1 reqConstT)) = true := by
  exact ⟨g1CS_accepts_of_spec_some reqInputT literal_canonical.1 true literal_specs.1,
    g1CS_accepts_of_spec_some reqNotF literal_canonical.2.1 false literal_specs.2.1,
    g1CS_accepts_of_spec_some reqAndF literal_canonical.2.2.1 false literal_specs.2.2.1,
    g1CS_accepts_of_spec_some reqOrT literal_canonical.2.2.2.1 true literal_specs.2.2.2.1,
    g1CS_accepts_of_spec_some reqConstF literal_canonical.2.2.2.2.1 false
      literal_specs.2.2.2.2.1,
    g1CS_accepts_of_spec_some reqConstT literal_canonical.2.2.2.2.2 true
      literal_specs.2.2.2.2.2⟩

theorem literal_false_output (i : Fin (G1M.tapeLength (encodeG1 reqAndF).length))
    (hi : (i : Nat) = g1OutputPosition reqAndF) :
    (TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 reqAndF))) 485).tape i = false := by
  rw [← literal_steps.2.2.1]
  exact g1CS_gate_accept_output reqAndF literal_canonical.2.2.1 false
    literal_specs.2.2.1 i hi

theorem literal_true_output (i : Fin (G1M.tapeLength (encodeG1 reqOrT).length))
    (hi : (i : Nat) = g1OutputPosition reqOrT) :
    (TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 reqOrT))) 513).tape i = true := by
  rw [← literal_steps.2.2.2.1]
  exact g1CS_gate_accept_output reqOrT literal_canonical.2.2.2.1 true
    literal_specs.2.2.2.1 i hi

end G1OutputAcceptProbes

end Pnp3.Internal.PsubsetPpoly.TM
