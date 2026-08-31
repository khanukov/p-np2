import Complexity.TMVerifier.TuringToolkit.GateNRelocation
import Complexity.TMVerifier.TuringToolkit.GateOneOutputAccept

/-!
# GN-3B1 + GN-3B2a + GN-3B2b: validation/rewind trace safety (2026-08-31)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module stops the canonical one-gate execution at the result-indexed
`g1OutputDoneConfig`, exactly one step before the literal accept handoff.  The
result is an index of the theorem and of the already-existing output-done
control state; it is not stored in a new annotation.

GN-3B2a adds a structural, parametric safety proof for the canonical validation
segment.  Its envelope records the actual frame decomposition, controller fold,
head, initial tape/context, coherent four-bit buffer, and remaining valid path;
it stores no reachability, run index, or safety assertion.  Exact microsteps
preserve that envelope through the trailing blank and stop at `rewindStart`.
The resulting `G1RunSafe` includes that boundary's left turn, but no later
rewind or full-gate trace is claimed by GN-3B2a.  GN-3B2b starts at the
successor of that left turn and follows the exact read-only reverse scan to
the existing `readBStart` handoff.  Its reverse envelope has the same purely
structural character: actual validation frames and tape bits, reverse mode
and position, coherent buffer, context, and remaining reverse path, with no
reachability, run-index, or safety field.

No GN machine, controller, copier, clock, or acceptance construction is added,
and the literal accept state is not mapped into a future GN control.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Exact output-done schedule -/

/-- Exact canonical schedule stopping one transition before literal accept. -/
def g1GateDoneSteps (r : G1Request) : Nat :=
  g1GateResultSteps r + (1 + g1OutputKernelSteps r)

theorem g1GateDoneSteps_provenance (r : G1Request) :
    g1GateDoneSteps r =
      g1GateResultSteps r + 1 + g1OutputKernelSteps r := by
  rw [g1GateDoneSteps]
  omega

theorem g1GateAcceptSteps_eq_done_add_one (r : G1Request) :
    g1GateAcceptSteps r = g1GateDoneSteps r + 1 := by
  rw [g1GateAcceptSteps, g1GateDoneSteps]
  omega

theorem g1GateDoneSteps_closed (r : G1Request) :
    g1GateDoneSteps r = g1GateResultSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps, g1OutputKernelSteps]
  omega

theorem g1GateDoneSteps_const (r : G1Request) (ht : r.tag = .const) :
    g1GateDoneSteps r = g1ConstActivatedSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_const r ht]

theorem g1GateDoneSteps_input (r : G1Request) (ht : r.tag = .input) :
    g1GateDoneSteps r = g1UACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_unary r (Or.inl ht)]

theorem g1GateDoneSteps_not (r : G1Request) (ht : r.tag = .not) :
    g1GateDoneSteps r = g1UACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_unary r (Or.inr ht)]

theorem g1GateDoneSteps_and (r : G1Request) (ht : r.tag = .and) :
    g1GateDoneSteps r = g1BACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_binary r (Or.inl ht)]

theorem g1GateDoneSteps_or (r : G1Request) (ht : r.tag = .or) :
    g1GateDoneSteps r = g1BACombineSteps r +
      (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 10) := by
  rw [g1GateDoneSteps_closed, g1GateResultSteps_binary r (Or.inr ht)]

theorem g1GateDoneSteps_le_clock (r : G1Request) :
    g1GateDoneSteps r ≤ g1Clock (encodeG1 r).length := by
  have haccept := g1GateAcceptSteps_le_clock r
  rw [g1GateAcceptSteps_eq_done_add_one] at haccept
  omega

/-- Combine door plus the exact S10a kernel, stopping at output-done. -/
theorem g1CS_output_done_exact (r : G1Request) (res : Bool) :
    TM.runConfig (M := G1M) (g1CombineConfig r res)
        (1 + g1OutputKernelSteps r) = g1OutputDoneConfig r res := by
  rw [runConfig_add, g1CS_step_combine_output, g1CS_output_kernel_exact]

/-- Exact real-initial canonical endpoint, one step before literal accept. -/
theorem g1CS_gate_done_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateDoneSteps r) = g1OutputDoneConfig r res := by
  rw [g1GateDoneSteps, runConfig_add, g1CS_gate_result_exact r hc res hs]
  exact g1CS_output_done_exact r res

theorem g1CS_gate_done_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).state.snd = g1OutputDoneState res := by
  rw [g1CS_gate_done_exact r hc res hs]
  rfl

theorem g1CS_gate_done_mode (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).state.snd.mode =
        if res then .outputDoneTrue else .outputDoneFalse := by
  rw [g1CS_gate_done_state r hc res hs]
  cases res <;> rfl

theorem g1CS_gate_done_context (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).state.snd.ctx = g1Ctx0 := by
  rw [g1CS_gate_done_state r hc res hs]
  cases res <;> rfl

theorem g1CS_gate_done_head (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).head : Nat) = g1OutputExitHead r := by
  rw [g1CS_gate_done_exact r hc res hs]
  rfl

theorem g1CS_gate_done_tape (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape =
        writeCell (g1OutputPosition r) res
          (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_gate_done_exact r hc res hs, g1OutputDoneConfig_tape,
    g1OutputTape_eq_writeCell]

theorem g1CS_gate_done_frames (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape =
        g1ListTape ((g1OutputFrames r res).flatMap G1Frame.bits) := by
  rw [g1CS_gate_done_exact r hc res hs]
  rfl

theorem g1CS_gate_done_output (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) = g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape i = res := by
  rw [g1CS_gate_done_tape r hc res hs]
  simp [writeCell, hi]

theorem g1CS_gate_done_off (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res)
    (i : Fin (G1M.tapeLength (encodeG1 r).length))
    (hi : (i : Nat) ≠ g1OutputPosition r) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateDoneSteps r)).tape i =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape i := by
  rw [g1CS_gate_done_tape r hc res hs]
  simp [writeCell, hi]

/-! ## Generic proper-prefix head growth and strict right room -/

theorem g1_runConfig_head_le_start_add {W k : Nat}
    (c : Configuration (M := G1M) W) :
    ((TM.runConfig (M := G1M) c k).head : Nat) ≤ (c.head : Nat) + k := by
  exact runConfig_head_val_le c k

theorem g1_initial_prefix_head_le_steps (r : G1Request) (k : Nat) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r))) k).head :
      Nat) ≤ k := by
  simpa using g1_runConfig_head_le_start_add
    (c := G1M.initialConfig (g1Point (encodeG1 r))) (k := k)

/-- A generic strict-right-footprint reduction at the exact `span - 1`
boundary.  It separates the natural head bound from the only boundary control
case that a complete schedule proof must discharge. -/
theorem g1_local_right_safe_of_head_le_span_pred {W : Nat}
    (c : Configuration (M := G1M) W)
    (hhead : (c.head : Nat) + 1 ≤ gnLocalSpan W)
    (hboundary : (c.head : Nat) + 1 = gnLocalSpan W →
      (G1M.step c.state (c.tape c.head)).snd.snd ≠ Move.right) :
    (c.head : Nat) < gnLocalSpan W ∧
      (((G1M.step c.state (c.tape c.head)).snd.snd = Move.right) →
        (c.head : Nat) + 1 < gnLocalSpan W) := by
  constructor
  · omega
  · intro hright
    by_contra hnot
    have heq : (c.head : Nat) + 1 = gnLocalSpan W := by omega
    exact hboundary heq hright

/-- Generic early-prefix right safety.  The schedule-specific extension from
this early prefix to all `k < g1GateDoneSteps r` is deliberately not inferred
from the output-done endpoint. -/
theorem g1_initial_prefix_right_safe_of_steps_lt_span (r : G1Request) (k : Nat)
    (hk : k + 1 < gnLocalSpan (encodeG1 r).length) :
    let c := TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) k
    (c.head : Nat) < gnLocalSpan (encodeG1 r).length ∧
      (((G1M.step c.state (c.tape c.head)).snd.snd = Move.right) →
        (c.head : Nat) + 1 < gnLocalSpan (encodeG1 r).length) := by
  dsimp only
  have hhead := g1_initial_prefix_head_le_steps r k
  constructor <;> omega

/-! ## GN-3B2a structural validation envelope -/

/-- Physical offset represented by a frame-buffer position. -/
def g1FramePositionOffset : G1FramePosition → Nat
  | .p0 => 0
  | .p1 => 1
  | .p2 => 2
  | .p3 => 3

/-- The buffer contains exactly the already-read prefix of the current
canonical four-bit frame, and its unused cells retain the scanner defaults. -/
def G1ForwardBufferCoherent (frame : G1Frame) :
    G1FramePosition → Bool → Bool → Bool → Prop
  | .p0, b0, b1, b2 => b0 = false ∧ b1 = false ∧ b2 = false
  | .p1, b0, b1, b2 =>
      b0 = frame.bits[0]! ∧ b1 = false ∧ b2 = false
  | .p2, b0, b1, b2 =>
      b0 = frame.bits[0]! ∧ b1 = frame.bits[1]! ∧ b2 = false
  | .p3, b0, b1, b2 =>
      b0 = frame.bits[0]! ∧ b1 = frame.bits[1]! ∧
        b2 = frame.bits[2]!

/-- A nonterminal concrete validation-scanner configuration.  Its mode is the
actual `g1AdvanceList` fold over the consumed frames; its head, initial tape,
context, current-frame buffer, and remaining valid path are all exact.  This
record deliberately contains no reachability, run index, or safety field. -/
structure G1ValidationScannerMicrostate (r : G1Request)
    (c : Configuration (M := G1M) (encodeG1 r).length) where
  pre : List G1Frame
  frame : G1Frame
  suffix : List G1Frame
  position : G1FramePosition
  b0 : Bool
  b1 : Bool
  b2 : Bool
  frames_eq : g1ValidationFrames r = pre ++ frame :: suffix
  head_lt : 4 * pre.length + g1FramePositionOffset position <
    G1M.tapeLength (encodeG1 r).length
  config_eq : c =
    g1AlignedConfig (encodeG1 r).length
      (4 * pre.length + g1FramePositionOffset position) head_lt
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      (g1AdvanceList .vBof pre) position b0 b1 b2 g1Ctx0
  buffer : G1ForwardBufferCoherent frame position b0 b1 b2
  remaining : G1ValidPath (g1AdvanceList .vBof pre) (frame :: suffix)
  advance_eq : g1AdvanceList .vBof (g1ValidationFrames r) = .rewindStart

/-- The exact terminal boundary after the trailing blank has completed and
before `rewindStart` takes its left transition. -/
structure G1ValidationRewindBoundary (r : G1Request)
    (c : Configuration (M := G1M) (encodeG1 r).length) where
  terminal_blank : g1ValidationFrames r = encodeG1Frames r ++ [.blank]
  advance_eq : g1AdvanceList .vBof (g1ValidationFrames r) = .rewindStart
  head_lt : 4 * (g1ValidationFrames r).length <
    G1M.tapeLength (encodeG1 r).length
  config_eq : c =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1ValidationFrames r).length) head_lt
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      (g1AdvanceList .vBof (g1ValidationFrames r)) .p0 false false false g1Ctx0

/-- Structural envelope for the forward scan, including its terminal
rewind-start boundary but no successor of that boundary. -/
inductive G1ValidationScannerEnvelope (r : G1Request) :
    Configuration (M := G1M) (encodeG1 r).length → Prop
  | scanning {c} : G1ValidationScannerMicrostate r c →
      G1ValidationScannerEnvelope r c
  | boundary {c} : G1ValidationRewindBoundary r c →
      G1ValidationScannerEnvelope r c

private theorem g1ValidationFrames_bits_length (r : G1Request) :
    4 * (g1ValidationFrames r).length = (encodeG1 r).length + 4 := by
  simp [g1ValidationFrames, encodeG1_length]
  omega

private theorem g1Validation_frame_room (r : G1Request)
    (pre : List G1Frame) (frame : G1Frame) (suffix : List G1Frame)
    (hframes : g1ValidationFrames r = pre ++ frame :: suffix) :
    4 * pre.length + 4 < G1M.tapeLength (encodeG1 r).length := by
  have htotal := g1ValidationFrames_bits_length r
  have hpre : pre.length + 1 ≤ (g1ValidationFrames r).length := by
    rw [hframes]
    simp
  apply g1_lt_tapeLength
  omega

private theorem g1Validation_scan_local_room (r : G1Request)
    (pre : List G1Frame) (frame : G1Frame) (suffix : List G1Frame)
    (position : G1FramePosition)
    (hframes : g1ValidationFrames r = pre ++ frame :: suffix) :
    4 * pre.length + g1FramePositionOffset position + 1 <
      gnLocalSpan (encodeG1 r).length := by
  have htotal := g1ValidationFrames_bits_length r
  have hpre : pre.length + 1 ≤ (g1ValidationFrames r).length := by
    rw [hframes]
    simp
  have hpre4 := Nat.mul_le_mul_left 4 hpre
  rw [htotal] at hpre4
  simp only [gnLocalSpan]
  cases position <;> simp only [g1FramePositionOffset] <;> omega

private theorem g1Validation_initial_tape_bit (r : G1Request)
    (pre : List G1Frame) (frame : G1Frame) (suffix : List G1Frame)
    (hframes : g1ValidationFrames r = pre ++ frame :: suffix)
    (j : Nat) (hj : j < 4)
    (hh : 4 * pre.length + j < G1M.tapeLength (encodeG1 r).length) :
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
        ⟨4 * pre.length + j, hh⟩ = frame.bits[j]! := by
  rw [← g1ListTape_validation_eq_initial]
  change ((g1ValidationFrames r).flatMap G1Frame.bits).getD
      (4 * pre.length + j) false = frame.bits[j]!
  rw [hframes]
  have hget := G1Frame.flatMap_getElem? pre suffix frame j hj
  simp only [List.getD, hget]
  have hjbits : j < frame.bits.length := by simpa using hj
  simp [List.getElem?_eq_getElem hjbits]

private theorem g1Frame_bits_four (frame : G1Frame) :
    [frame.bits[0]!, frame.bits[1]!, frame.bits[2]!, frame.bits[3]!] =
      frame.bits := by
  cases frame with
  | data b | output b => cases b <;> rfl
  | blank | bof | tag | index | separator | cursor | finish | argSep | spent =>
      rfl

/-- The real initial configuration inhabits the structural scanner envelope;
canonicality enters only through the existing validation path and fold. -/
theorem g1Validation_initial_envelope (r : G1Request) (hc : r.Canonical) :
    G1ValidationScannerEnvelope r
      (G1M.initialConfig (g1Point (encodeG1 r))) := by
  apply G1ValidationScannerEnvelope.scanning
  refine {
    pre := []
    frame := .bof
    suffix := (g1ValidationFrames r).tail
    position := .p0
    b0 := false
    b1 := false
    b2 := false
    frames_eq := ?_
    head_lt := by
      change 0 < G1M.tapeLength (encodeG1 r).length
      exact g1_lt_tapeLength (by omega)
    config_eq := ?_
    buffer := ⟨rfl, rfl, rfl⟩
    remaining := ?_
    advance_eq := g1AdvanceList_encode r hc }
  · simp [g1ValidationFrames, encodeG1Frames]
  · apply Configuration.ext_of_components <;> rfl
  · simpa [g1ValidationFrames, encodeG1Frames] using g1ValidationPath r hc

/-- Every structural scanner or terminal-boundary configuration is locally
safe in the exact `W+5` relocation footprint. -/
theorem g1Validation_envelope_local_safe (r : G1Request)
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (h : G1ValidationScannerEnvelope r c) : G1LocalStepSafe c := by
  cases h with
  | scanning hs =>
      rcases hs with ⟨pre, frame, suffix, position, b0, b1, b2, hframes,
        hhead, rfl, hbuffer, hpath, hadvance⟩
      have hroom := g1Validation_frame_room r pre frame suffix hframes
      have hlocal := g1Validation_scan_local_room r pre frame suffix position
        hframes
      have hforward : G1ForwardMode (g1AdvanceList .vBof pre) := hpath.1
      have hmove :
          (G1M.step
            ⟨g1FrameScanner.phase,
              g1State (g1AdvanceList .vBof pre) position b0 b1 b2 g1Ctx0⟩
            ((G1M.initialConfig (g1Point (encodeG1 r))).tape
              ⟨4 * pre.length + g1FramePositionOffset position, hhead⟩)).snd.snd =
              Move.right := by
        cases position with
        | p0 =>
            change (g1Transition 0
              (g1State (g1AdvanceList .vBof pre) .p0 b0 b1 b2 g1Ctx0)
              _).snd.snd.snd = Move.right
            rw [g1Transition_forward_p0 hforward]
        | p1 =>
            change (g1Transition 0
              (g1State (g1AdvanceList .vBof pre) .p1 b0 b1 b2 g1Ctx0)
              _).snd.snd.snd = Move.right
            rw [g1Transition_forward_p1 hforward]
        | p2 =>
            change (g1Transition 0
              (g1State (g1AdvanceList .vBof pre) .p2 b0 b1 b2 g1Ctx0)
              _).snd.snd.snd = Move.right
            rw [g1Transition_forward_p2 hforward]
        | p3 =>
            rcases hbuffer with ⟨rfl, rfl, rfl⟩
            have hscan := g1Validation_initial_tape_bit r pre frame suffix
              hframes 3 (by omega) hhead
            have hcomplete :
                g1Complete (g1AdvanceList .vBof pre) frame.bits[0]!
                  frame.bits[1]! frame.bits[2]! frame.bits[3]! =
                    g1Advance (g1AdvanceList .vBof pre) frame :=
              g1FrameScanner.complete_of_bits _ frame (g1Frame_bits_four frame)
            have hnext := hpath.2.1
            change (g1Transition 0
              (g1State (g1AdvanceList .vBof pre) .p3 frame.bits[0]!
                frame.bits[1]! frame.bits[2]! g1Ctx0)
              ((G1M.initialConfig (g1Point (encodeG1 r))).tape
                ⟨4 * pre.length + 3, by omega⟩)).snd.snd.snd = Move.right
            have hscan' :
                (G1M.initialConfig (g1Point (encodeG1 r))).tape
                  ⟨4 * pre.length + 3, by omega⟩ = frame.bits[3]! := by
              simpa using hscan
            rw [hscan', g1Transition_forward_p3_advance hforward _ _ _ _ _ _
              (by rw [hcomplete]; exact hnext)]
      refine ⟨?_, ?_, ?_⟩
      · simpa only [g1AlignedConfig_head_val] using Nat.lt_of_succ_lt hlocal
      · intro hleft
        change (G1M.step
          ⟨g1FrameScanner.phase,
            g1State (g1AdvanceList .vBof pre) position b0 b1 b2 g1Ctx0⟩
          ((G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length + g1FramePositionOffset position, hhead⟩)).snd.snd =
              Move.left at hleft
        rw [hmove] at hleft
        exact Move.noConfusion hleft
      · intro _
        simpa only [g1AlignedConfig_head_val] using hlocal
  | boundary hb =>
      rcases hb with ⟨hblank, hadvance, hhead, rfl⟩
      have hlen := g1ValidationFrames_bits_length r
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨?_, ?_, ?_⟩
      · simp only [gnLocalSpan]
        omega
      · intro _
        rw [hlen]
        omega
      · intro hright
        rw [hadvance] at hright
        change (g1Transition (0 : Fin 1)
          (g1State .rewindStart .p0 false false false g1Ctx0) _).snd.snd.snd =
            Move.right at hright
        rw [g1Transition_rewindStart] at hright
        exact Move.noConfusion hright

/-- One actual TM step preserves the envelope from every nonterminal scanner
microstate.  The proof follows `p0 → p1 → p2 → p3`; completion either
advances to the next frame or enters the exact trailing-blank boundary. -/
theorem g1Validation_scanner_step_exact (r : G1Request)
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (h : G1ValidationScannerMicrostate r c) :
    G1ValidationScannerEnvelope r (TM.stepConfig (M := G1M) c) := by
  rcases h with ⟨pre, frame, suffix, position, b0, b1, b2, hframes,
    hhead, rfl, hbuffer, hpath, hadvance⟩
  have hroom := g1Validation_frame_room r pre frame suffix hframes
  have hforward : G1ForwardMode (g1AdvanceList .vBof pre) := hpath.1
  have bitAt (j : Nat) (hj : j < 4)
      (hh : 4 * pre.length + j < G1M.tapeLength (encodeG1 r).length) :
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + j, hh⟩ = frame.bits[j]! :=
    g1Validation_initial_tape_bit r pre frame suffix hframes j hj hh
  cases position with
  | p0 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan :
          (G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length, hhead⟩ = frame.bits[0]! := by
        simpa using bitAt 0 (by omega) hhead
      have hnextHead : 4 * pre.length + 1 <
          G1M.tapeLength (encodeG1 r).length := by omega
      have hstep := g1CS_aligned_step_right (encodeG1 r).length
        (4 * pre.length) hhead hnextHead
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1State (g1AdvanceList .vBof pre) .p0 false false false g1Ctx0)
        (g1State (g1AdvanceList .vBof pre) .p1
          ((G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length, hhead⟩) false false g1Ctx0)
        ((G1M.initialConfig (g1Point (encodeG1 r))).tape ⟨4 * pre.length, hhead⟩)
        (fun phase => g1Transition_forward_p0 hforward phase false false false _
          g1Ctx0)
      rw [writeCell_self] at hstep
      apply G1ValidationScannerEnvelope.scanning
      refine ⟨pre, frame, suffix, .p1, frame.bits[0]!, false, false, hframes,
        by simpa [g1FramePositionOffset] using hnextHead,
        ?_, ⟨rfl, rfl, rfl⟩, hpath, hadvance⟩
      simpa only [g1AlignedConfig, g1FramePositionOffset, hscan] using hstep
  | p1 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := bitAt 1 (by omega) hhead
      have hnextHead : 4 * pre.length + 2 <
          G1M.tapeLength (encodeG1 r).length := by omega
      have hstep := g1CS_aligned_step_right (encodeG1 r).length
        (4 * pre.length + 1) hhead (by omega)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1State (g1AdvanceList .vBof pre) .p1 frame.bits[0]! false false g1Ctx0)
        (g1State (g1AdvanceList .vBof pre) .p2 frame.bits[0]!
          ((G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length + 1, hhead⟩) false g1Ctx0)
        ((G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + 1, hhead⟩)
        (fun phase => g1Transition_forward_p1 hforward phase _ false false _ g1Ctx0)
      rw [writeCell_self] at hstep
      apply G1ValidationScannerEnvelope.scanning
      refine ⟨pre, frame, suffix, .p2, frame.bits[0]!, frame.bits[1]!, false,
        hframes, by simpa [g1FramePositionOffset] using hnextHead,
        ?_, ⟨rfl, rfl, rfl⟩,
        hpath, hadvance⟩
      simpa only [g1AlignedConfig, g1FramePositionOffset, hscan,
        Nat.add_assoc] using hstep
  | p2 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := bitAt 2 (by omega) hhead
      have hnextHead : 4 * pre.length + 3 <
          G1M.tapeLength (encodeG1 r).length := by omega
      have hstep := g1CS_aligned_step_right (encodeG1 r).length
        (4 * pre.length + 2) hhead (by omega)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1State (g1AdvanceList .vBof pre) .p2 frame.bits[0]! frame.bits[1]!
          false g1Ctx0)
        (g1State (g1AdvanceList .vBof pre) .p3 frame.bits[0]! frame.bits[1]!
          ((G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length + 2, hhead⟩) g1Ctx0)
        ((G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + 2, hhead⟩)
        (fun phase => g1Transition_forward_p2 hforward phase _ _ false _ g1Ctx0)
      rw [writeCell_self] at hstep
      apply G1ValidationScannerEnvelope.scanning
      refine ⟨pre, frame, suffix, .p3, frame.bits[0]!, frame.bits[1]!,
        frame.bits[2]!, hframes, by simpa [g1FramePositionOffset] using
          hnextHead, ?_, ⟨rfl, rfl, rfl⟩,
        hpath, hadvance⟩
      simpa only [g1AlignedConfig, g1FramePositionOffset, hscan,
        Nat.add_assoc] using hstep
  | p3 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := bitAt 3 (by omega) hhead
      have hcomplete :
          g1Complete (g1AdvanceList .vBof pre) frame.bits[0]! frame.bits[1]!
              frame.bits[2]! frame.bits[3]! =
            g1Advance (g1AdvanceList .vBof pre) frame :=
        g1FrameScanner.complete_of_bits _ frame (g1Frame_bits_four frame)
      have hnext := hpath.2.1
      have hcompleteScan :
          g1Complete (g1AdvanceList .vBof pre) frame.bits[0]! frame.bits[1]!
              frame.bits[2]!
              ((G1M.initialConfig (g1Point (encodeG1 r))).tape
                ⟨4 * pre.length + 3, hhead⟩) =
            g1Advance (g1AdvanceList .vBof pre) frame := by
        rw [hscan, hcomplete]
      have hstep := g1CS_aligned_step_right (encodeG1 r).length
        (4 * pre.length + 3) hhead (by omega)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1State (g1AdvanceList .vBof pre) .p3 frame.bits[0]! frame.bits[1]!
          frame.bits[2]! g1Ctx0)
        (g1State (g1Advance (g1AdvanceList .vBof pre) frame) .p0 false false
          false g1Ctx0)
        ((G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + 3, hhead⟩)
        (fun phase => by
          have ht := g1Transition_forward_p3_advance hforward phase
            frame.bits[0]! frame.bits[1]! frame.bits[2]!
            ((G1M.initialConfig (g1Point (encodeG1 r))).tape
              ⟨4 * pre.length + 3, hhead⟩) g1Ctx0
            (by rw [hcompleteScan]; exact hnext)
          rw [hcompleteScan] at ht
          exact ht)
      rw [writeCell_self] at hstep
      cases suffix with
      | nil =>
          apply G1ValidationScannerEnvelope.boundary
          have hmode : g1Advance (g1AdvanceList .vBof pre) frame =
              .rewindStart := by
            have happ := g1AdvanceList_append .vBof pre [frame]
            rw [← hframes, hadvance] at happ
            simpa using happ.symm
          refine ⟨rfl, hadvance, ?_, ?_⟩
          · rw [g1ValidationFrames_bits_length]
            exact g1_lt_tapeLength (by omega)
          · rw [hmode] at hstep
            have hlen : 4 * pre.length + 3 + 1 =
                4 * (g1ValidationFrames r).length := by
              rw [hframes]
              simp
              omega
            simpa only [g1AlignedConfig, hadvance, hlen] using hstep
      | cons next rest =>
          apply G1ValidationScannerEnvelope.scanning
          have htail : G1ValidPath
              (g1AdvanceList .vBof (pre ++ [frame])) (next :: rest) := by
            rw [g1AdvanceList_append]
            exact hpath.2.2
          refine ⟨pre ++ [frame], next, rest, .p0, false, false, false, ?_,
            ?_, ?_, ⟨rfl, rfl, rfl⟩, htail, hadvance⟩
          · simpa [List.append_assoc] using hframes
          · simpa only [g1FramePositionOffset, List.length_append,
              List.length_cons, List.length_nil, Nat.add_zero, Nat.mul_add,
              Nat.mul_one] using hroom
          · simpa only [g1AlignedConfig, g1FramePositionOffset,
              g1AdvanceList_append, List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Nat.add_assoc] using hstep

/-- Every run prefix through (and including) the exact forward-scan endpoint
inhabits the structural envelope. -/
theorem g1Validation_run_envelope (r : G1Request) (hc : r.Canonical)
    (k : Nat) (hk : k ≤ (encodeG1 r).length + 4) :
    G1ValidationScannerEnvelope r
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r))) k) := by
  induction k with
  | zero => simpa using g1Validation_initial_envelope r hc
  | succ k ih =>
      have hklt : k < (encodeG1 r).length + 4 := by omega
      have hprev := ih (by omega)
      rw [runConfig_succ]
      cases hprev with
      | scanning hs => exact g1Validation_scanner_step_exact r hs
      | boundary hb =>
          have hcap :
              ((TM.runConfig (M := G1M)
                (G1M.initialConfig (g1Point (encodeG1 r))) k).head : Nat) =
                (encodeG1 r).length + 4 := by
            rw [hb.config_eq]
            simp only [g1AlignedConfig_head_val]
            exact g1ValidationFrames_bits_length r
          have hbound := g1_initial_prefix_head_le_steps r k
          omega

/-- The complete forward validation scan is safe at every proper prefix.
Exact `W+4` attainment is combined with this theorem below. -/
theorem g1Validation_run_safe (r : G1Request) (hc : r.Canonical) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4) := by
  intro k hk
  exact g1Validation_envelope_local_safe r
    (g1Validation_run_envelope r hc k (by omega))

/-! ## Exact inspection of the `W + 4` validation boundary -/

theorem g1CS_validation_reaches_span_pred (r : G1Request) (hc : r.Canonical) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4)).head : Nat) + 1 =
        gnLocalSpan (encodeG1 r).length := by
  rw [g1CS_validate_encoded_exact r hc]
  simp [gnLocalSpan]

theorem g1CS_validation_span_pred_moves_left (r : G1Request)
    (hc : r.Canonical) :
    (G1M.step
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).state
      ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).tape
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).head)).snd.snd = Move.left := by
  rw [g1CS_validate_encoded_exact r hc]
  rfl

/-- The maximum-head validation configuration is locally safe: it is inside
`W + 5`, and its actual next row is left, not right. -/
theorem g1CS_validation_span_pred_local_safe (r : G1Request)
    (hc : r.Canonical) :
    G1LocalStepSafe
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)) := by
  have hhead := g1CS_validation_reaches_span_pred r hc
  have hleft := g1CS_validation_span_pred_moves_left r hc
  refine ⟨by omega, ?_, ?_⟩
  · intro _
    rw [g1CS_validate_encoded_exact r hc]
    simp
  · intro hright
    rw [hleft] at hright
    exact Move.noConfusion hright

/-- Include the attained `W+4` rewind-start configuration itself as a safe
transition source.  This is exactly the forward validation segment plus its
single left-turn boundary row, and no rewind successor. -/
theorem g1Validation_run_safe_through_boundary (r : G1Request)
    (hc : r.Canonical) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 5) := by
  simpa [Nat.add_assoc] using
    G1RunSafe.succ (g1Validation_run_safe r hc)
      (g1CS_validation_span_pred_local_safe r hc)

/-- GN-3B2a capstone: every canonical request really attains head `W+4`, and
the validation segment is locally safe through the boundary's left turn. -/
theorem g1CS_validation_trace_safe (r : G1Request) (hc : r.Canonical) :
    ((TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4)).head : Nat) = (encodeG1 r).length + 4 ∧
      G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 5) := by
  constructor
  · have h := g1CS_validation_reaches_span_pred r hc
    simp only [gnLocalSpan] at h
    omega
  · exact g1Validation_run_safe_through_boundary r hc

/-! ## GN-3B2b structural validation rewind -/

/-- Number of physical reverse-read steps from the successor of the
validation boundary to the existing read-B handoff. -/
def g1ValidationRewindSteps (r : G1Request) : Nat :=
  4 * (g1ValidationFrames r).length

/-- Remaining microsteps in the current reverse-read frame position. -/
def g1ReverseFrameSteps : G1FramePosition → Nat
  | .p3 => 4
  | .p2 => 3
  | .p1 => 2
  | .p0 => 1

/-- The already established prefix from the unique left anchor through the
current reverse-read frame.  Each extension is explicitly non-anchor. -/
inductive G1ReversePath : List G1Frame → G1Frame → Prop
  | bof : G1ReversePath [] .bof
  | step {pre frame next} : G1ReversePath pre frame → next ≠ .bof →
      G1ReversePath (pre ++ [frame]) next

/-- The reverse buffer contains exactly the bits already scanned from the
right side of the current canonical frame.  Unused slots retain their reset
value. -/
def G1ReverseBufferCoherent (frame : G1Frame) :
    G1FramePosition → Bool → Bool → Bool → Prop
  | .p3, b0, b1, b2 => b0 = false ∧ b1 = false ∧ b2 = false
  | .p2, b0, b1, b2 =>
      b0 = false ∧ b1 = false ∧ b2 = frame.bits[3]!
  | .p1, b0, b1, b2 =>
      b0 = false ∧ b1 = frame.bits[2]! ∧ b2 = frame.bits[3]!
  | .p0, b0, b1, b2 =>
      b0 = frame.bits[1]! ∧ b1 = frame.bits[2]! ∧
        b2 = frame.bits[3]!

/-- A concrete reverse-scanner configuration over the canonical validation
tape.  `pre ++ frame :: suffix` is the actual frame decomposition, while
`remaining` is the structural path back to the unique leading anchor. -/
structure G1RewindScannerMicrostate (r : G1Request)
    (c : Configuration (M := G1M) (encodeG1 r).length) where
  pre : List G1Frame
  frame : G1Frame
  suffix : List G1Frame
  position : G1FramePosition
  b0 : Bool
  b1 : Bool
  b2 : Bool
  frames_eq : g1ValidationFrames r = pre ++ frame :: suffix
  head_lt : 4 * pre.length + g1FramePositionOffset position <
    G1M.tapeLength (encodeG1 r).length
  config_eq : c =
    g1AlignedConfig (encodeG1 r).length
      (4 * pre.length + g1FramePositionOffset position) head_lt
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .rewind position b0 b1 b2 g1Ctx0
  buffer : G1ReverseBufferCoherent frame position b0 b1 b2
  remaining : G1ReversePath pre frame

/-- The canonical terminal configuration reached by reverse-reading `bof`.
This is the pre-existing read-B/pass-B handoff, not a pass-B walk. -/
structure G1RewindHandoff (r : G1Request)
    (c : Configuration (M := G1M) (encodeG1 r).length) where
  head_lt : 0 < G1M.tapeLength (encodeG1 r).length
  config_eq : c =
    g1AlignedConfig (encodeG1 r).length 0 head_lt
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .readBStart .p0 false false false g1Ctx0

/-- Structural reverse envelope, including only the terminal handoff as its
non-rewinding case. -/
inductive G1RewindEnvelope (r : G1Request) :
    Configuration (M := G1M) (encodeG1 r).length → Prop
  | rewinding {c} : G1RewindScannerMicrostate r c → G1RewindEnvelope r c
  | handoff {c} : G1RewindHandoff r c → G1RewindEnvelope r c

/-- Structural measure used by the safety induction; it is derived from the
frame decomposition and position and is not stored in the microstate. -/
def G1RewindScannerMicrostate.stepsRemaining {r c}
    (h : G1RewindScannerMicrostate r c) : Nat :=
  4 * h.pre.length + g1ReverseFrameSteps h.position

private theorem g1ReversePath_extend_to_blank {pre : List G1Frame}
    {frame : G1Frame} (hpath : G1ReversePath pre frame)
    (tail : List G1Frame) (hne : ∀ f ∈ tail, f ≠ .bof) :
    G1ReversePath ((pre ++ [frame]) ++ tail) .blank := by
  induction tail generalizing pre frame with
  | nil =>
      simpa using G1ReversePath.step hpath (by decide : G1Frame.blank ≠ .bof)
  | cons next rest ih =>
      have hnext : next ≠ G1Frame.bof := hne next (by simp)
      have hrest : ∀ f ∈ rest, f ≠ G1Frame.bof := by
        intro f hf
        exact hne f (by simp [hf])
      simpa [List.append_assoc] using
        ih (G1ReversePath.step hpath hnext) hrest

private theorem g1Validation_reverse_path (r : G1Request) :
    G1ReversePath (encodeG1Frames r) .blank := by
  have hne : ∀ f ∈ (encodeG1Frames r).tail, f ≠ G1Frame.bof := by
    intro f hf heq
    subst f
    rcases r with ⟨tag, arg1, arg2, vals⟩
    simp [encodeG1Frames] at hf
  have h := g1ReversePath_extend_to_blank G1ReversePath.bof
    (encodeG1Frames r).tail hne
  rcases r with ⟨tag, arg1, arg2, vals⟩
  simpa [encodeG1Frames] using h

/-- Exact successor of the merged GN-3B2a `W+4` validation boundary. -/
theorem g1Validation_rewind_entry_exact (r : G1Request) (hc : r.Canonical) :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 5) =
      g1AlignedConfig (encodeG1 r).length ((encodeG1 r).length + 3)
        (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .rewind .p3 false false false g1Ctx0 := by
  rw [show (encodeG1 r).length + 5 =
      ((encodeG1 r).length + 4) + 1 by omega, runConfig_add,
    g1CS_validate_encoded_exact r hc, runConfig_one]
  have hstep := g1CS_aligned_step_left (encodeG1 r).length
    ((encodeG1 r).length + 4) (g1_lt_tapeLength (by omega)) (by omega)
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    (g1State .rewindStart .p0 false false false g1Ctx0)
    (g1State .rewind .p3 false false false g1Ctx0)
    ((G1M.initialConfig (g1Point (encodeG1 r))).tape
      ⟨(encodeG1 r).length + 4, g1_lt_tapeLength (by omega)⟩)
    (fun phase => g1Transition_rewindStart phase .p0 false false false _ g1Ctx0)
  rwa [writeCell_self] at hstep

/-- The boundary successor inhabits the reverse envelope with the terminal
blank as current frame and the whole canonical word as its remaining path. -/
theorem g1Validation_rewind_entry_envelope (r : G1Request)
    (hc : r.Canonical) :
    G1RewindEnvelope r
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 5)) := by
  apply G1RewindEnvelope.rewinding
  refine {
    pre := encodeG1Frames r
    frame := .blank
    suffix := []
    position := .p3
    b0 := false
    b1 := false
    b2 := false
    frames_eq := by simp [g1ValidationFrames]
    head_lt := by
      simp only [g1FramePositionOffset, encodeG1Frames_length,
        encodeG1_length]
      exact g1_lt_tapeLength (by omega)
    config_eq := ?_
    buffer := ⟨rfl, rfl, rfl⟩
    remaining := g1Validation_reverse_path r }
  rw [g1Validation_rewind_entry_exact r hc]
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    simp [g1FramePositionOffset, encodeG1Frames_length, encodeG1_length]
  · rfl

private theorem g1Rewind_initial_tape_bit (r : G1Request)
    (pre : List G1Frame) (frame : G1Frame) (suffix : List G1Frame)
    (hframes : g1ValidationFrames r = pre ++ frame :: suffix)
    (j : Nat) (hj : j < 4)
    (hh : 4 * pre.length + j < G1M.tapeLength (encodeG1 r).length) :
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
        ⟨4 * pre.length + j, hh⟩ = frame.bits[j]! :=
  g1Validation_initial_tape_bit r pre frame suffix hframes j hj hh

/-- Every genuine rewind microstate is locally safe in the exact `W+5`
footprint.  In the anchor `p0` case the concrete transition is `stay`, so the
head-zero proof does not use the source machine's left clamp. -/
theorem g1Rewind_microstate_local_safe (r : G1Request)
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (h : G1RewindScannerMicrostate r c) : G1LocalStepSafe c := by
  rcases h with ⟨pre, frame, suffix, position, b0, b1, b2, hframes,
    hhead, rfl, hbuffer, hpath⟩
  have hlocal := g1Validation_scan_local_room r pre frame suffix position
    hframes
  cases position with
  | p3 =>
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨Nat.lt_of_succ_lt hlocal, ?_, ?_⟩
      · intro _
        simp only [g1FramePositionOffset]
        omega
      · intro hright
        change (g1Transition (0 : Fin 1)
          (g1State .rewind .p3 false false false g1Ctx0) _).snd.snd.snd =
            Move.right at hright
        rw [g1Transition_rewind_p3] at hright
        exact Move.noConfusion hright
  | p2 =>
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨Nat.lt_of_succ_lt hlocal, ?_, ?_⟩
      · intro _
        simp only [g1FramePositionOffset]
        omega
      · intro hright
        change (g1Transition (0 : Fin 1)
          (g1State .rewind .p2 false false frame.bits[3]! g1Ctx0) _).snd.snd.snd =
            Move.right at hright
        rw [g1Transition_rewind_p2] at hright
        exact Move.noConfusion hright
  | p1 =>
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨Nat.lt_of_succ_lt hlocal, ?_, ?_⟩
      · intro _
        simp only [g1FramePositionOffset]
        omega
      · intro hright
        change (g1Transition (0 : Fin 1)
          (g1State .rewind .p1 false frame.bits[2]! frame.bits[3]! g1Ctx0)
            _).snd.snd.snd = Move.right at hright
        rw [g1Transition_rewind_p1] at hright
        exact Move.noConfusion hright
  | p0 =>
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan : (G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length, hhead⟩ = frame.bits[0]! := by
        simpa using g1Rewind_initial_tape_bit r pre frame suffix hframes 0
          (by omega) hhead
      have hdecode : decodeG1Frame?
          [(G1M.initialConfig (g1Point (encodeG1 r))).tape
              ⟨4 * pre.length, hhead⟩,
            frame.bits[1]!, frame.bits[2]!, frame.bits[3]!] = some frame := by
        rw [hscan]
        simpa only [g1Frame_bits_four] using decodeG1Frame_bits frame
      cases hpath with
      | bof =>
          have hdecode0 : decodeG1Frame?
              [(G1M.initialConfig (g1Point (encodeG1 r))).tape
                  ⟨0, hhead⟩,
                G1Frame.bof.bits[1]!, G1Frame.bof.bits[2]!,
                G1Frame.bof.bits[3]!] = some G1Frame.bof := by
            simpa using hdecode
          simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
            g1AlignedConfig_state, g1AlignedConfig_tape,
            g1FramePositionOffset]
          refine ⟨by simpa using Nat.lt_of_succ_lt hlocal, ?_, ?_⟩
          · intro hleft
            simp only [g1AlignedConfig, g1AlignedConfigQ] at hleft
            simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hleft
            change (g1Transition (0 : Fin 1)
              (g1State .rewind .p0 G1Frame.bof.bits[1]!
                G1Frame.bof.bits[2]! G1Frame.bof.bits[3]! g1Ctx0)
              ((G1M.initialConfig (g1Point (encodeG1 r))).tape
                ⟨0, hhead⟩)).snd.snd.snd = Move.left at hleft
            rw [g1Transition_rewind_p0_bof (heq := hdecode0)] at hleft
            exact Move.noConfusion hleft
          · intro hright
            simp only [g1AlignedConfig, g1AlignedConfigQ] at hright
            simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hright
            change (g1Transition (0 : Fin 1)
              (g1State .rewind .p0 G1Frame.bof.bits[1]!
                G1Frame.bof.bits[2]! G1Frame.bof.bits[3]! g1Ctx0)
              ((G1M.initialConfig (g1Point (encodeG1 r))).tape
                ⟨0, hhead⟩)).snd.snd.snd = Move.right at hright
            rw [g1Transition_rewind_p0_bof (heq := hdecode0)] at hright
            exact Move.noConfusion hright
      | @step left previous _ hprevious hne =>
          simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
            g1AlignedConfig_state, g1AlignedConfig_tape,
            g1FramePositionOffset]
          refine ⟨by simpa using Nat.lt_of_succ_lt hlocal, ?_, ?_⟩
          · intro _
            simp only [List.length_append, List.length_cons, List.length_nil,
              Nat.add_zero]
            omega
          · intro hright
            simp only [g1AlignedConfig, g1AlignedConfigQ] at hright
            change (g1Transition (0 : Fin 1)
              (g1State .rewind .p0 frame.bits[1]! frame.bits[2]!
                frame.bits[3]! g1Ctx0)
              ((G1M.initialConfig (g1Point (encodeG1 r))).tape
                ⟨4 * (left ++ [previous]).length, hhead⟩)).snd.snd.snd =
                  Move.right at hright
            rw [g1Transition_rewind_p0_other
              (hne := by rw [hdecode]; simpa using hne)] at hright
            exact Move.noConfusion hright

/-- Ranked structural result of one reverse microstep.  The rank is external
to both structural records and decreases exactly once on a rewinding result. -/
inductive G1RewindStepResult (r : G1Request) (remaining : Nat) :
    Configuration (M := G1M) (encodeG1 r).length → Prop
  | rewinding {c} (h : G1RewindScannerMicrostate r c)
      (remaining_eq : h.stepsRemaining + 1 = remaining) :
      G1RewindStepResult r remaining c
  | handoff {c} (h : G1RewindHandoff r c) (remaining_eq : remaining = 1) :
      G1RewindStepResult r remaining c

set_option maxHeartbeats 1000000 in
/-- One genuine TM step has a rank-decreasing structural result at all four
positions.  A non-anchor `p0` crosses a frame boundary; the anchor `p0` takes
the actual stationary row into the canonical read-B handoff. -/
theorem g1Rewind_microstate_step_ranked (r : G1Request)
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (h : G1RewindScannerMicrostate r c) :
    G1RewindStepResult r h.stepsRemaining
      (TM.stepConfig (M := G1M) c) := by
  rcases h with ⟨pre, frame, suffix, position, b0, b1, b2, hframes,
    hhead, rfl, hbuffer, hpath⟩
  have bitAt (j : Nat) (hj : j < 4)
      (hh : 4 * pre.length + j < G1M.tapeLength (encodeG1 r).length) :
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + j, hh⟩ = frame.bits[j]! :=
    g1Rewind_initial_tape_bit r pre frame suffix hframes j hj hh
  cases position with
  | p3 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := bitAt 3 (by omega) hhead
      have hstep := g1CS_aligned_step_left (encodeG1 r).length
        (4 * pre.length + 3) hhead (by omega)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1State .rewind .p3 false false false g1Ctx0)
        (g1State .rewind .p2 false false
          ((G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length + 3, hhead⟩) g1Ctx0)
        ((G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + 3, hhead⟩)
        (fun phase => g1Transition_rewind_p3 phase false false false _ g1Ctx0)
      rw [writeCell_self] at hstep
      refine G1RewindStepResult.rewinding ?_ ?_
      refine ⟨pre, frame, suffix, .p2, false, false, frame.bits[3]!, hframes,
        ?_, ?_, ⟨rfl, rfl, rfl⟩, hpath⟩
      · simp only [g1FramePositionOffset]
        omega
      · simpa only [g1AlignedConfig, g1FramePositionOffset, hscan,
          Nat.add_assoc] using hstep
      · simp [G1RewindScannerMicrostate.stepsRemaining, g1ReverseFrameSteps]
  | p2 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := bitAt 2 (by omega) hhead
      have hstep := g1CS_aligned_step_left (encodeG1 r).length
        (4 * pre.length + 2) hhead (by omega)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1State .rewind .p2 false false frame.bits[3]! g1Ctx0)
        (g1State .rewind .p1 false
          ((G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length + 2, hhead⟩) frame.bits[3]! g1Ctx0)
        ((G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + 2, hhead⟩)
        (fun phase => g1Transition_rewind_p2 phase false false
          frame.bits[3]! _ g1Ctx0)
      rw [writeCell_self] at hstep
      refine G1RewindStepResult.rewinding ?_ ?_
      refine ⟨pre, frame, suffix, .p1, false, frame.bits[2]!, frame.bits[3]!,
        hframes, ?_, ?_, ⟨rfl, rfl, rfl⟩, hpath⟩
      · simp only [g1FramePositionOffset]
        omega
      · simpa only [g1AlignedConfig, g1FramePositionOffset, hscan,
          Nat.add_assoc] using hstep
      · simp [G1RewindScannerMicrostate.stepsRemaining, g1ReverseFrameSteps]
  | p1 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := bitAt 1 (by omega) hhead
      have hstep := g1CS_aligned_step_left (encodeG1 r).length
        (4 * pre.length + 1) hhead (by omega)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1State .rewind .p1 false frame.bits[2]! frame.bits[3]! g1Ctx0)
        (g1State .rewind .p0
          ((G1M.initialConfig (g1Point (encodeG1 r))).tape
            ⟨4 * pre.length + 1, hhead⟩)
          frame.bits[2]! frame.bits[3]! g1Ctx0)
        ((G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length + 1, hhead⟩)
        (fun phase => g1Transition_rewind_p1 phase false frame.bits[2]!
          frame.bits[3]! _ g1Ctx0)
      rw [writeCell_self] at hstep
      refine G1RewindStepResult.rewinding ?_ ?_
      refine ⟨pre, frame, suffix, .p0, frame.bits[1]!, frame.bits[2]!,
        frame.bits[3]!, hframes, ?_, ?_, ⟨rfl, rfl, rfl⟩, hpath⟩
      · simp only [g1FramePositionOffset]
        omega
      · simpa only [g1AlignedConfig, g1FramePositionOffset, hscan,
          Nat.add_assoc] using hstep
      · simp [G1RewindScannerMicrostate.stepsRemaining, g1ReverseFrameSteps]
  | p0 =>
      simp only [g1FramePositionOffset] at hhead
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan : (G1M.initialConfig (g1Point (encodeG1 r))).tape
          ⟨4 * pre.length, hhead⟩ = frame.bits[0]! := by
        simpa using bitAt 0 (by omega) hhead
      have hdecode : decodeG1Frame?
          [(G1M.initialConfig (g1Point (encodeG1 r))).tape
              ⟨4 * pre.length, hhead⟩,
            frame.bits[1]!, frame.bits[2]!, frame.bits[3]!] = some frame := by
        rw [hscan]
        simpa only [g1Frame_bits_four] using decodeG1Frame_bits frame
      cases hpath with
      | bof =>
          have hstep := g1CS_aligned_step_stay (encodeG1 r).length 0 hhead
            (G1M.initialConfig (g1Point (encodeG1 r))).tape
            (g1State .rewind .p0 G1Frame.bof.bits[1]!
              G1Frame.bof.bits[2]! G1Frame.bof.bits[3]! g1Ctx0)
            (g1ReadBState g1Ctx0)
            ((G1M.initialConfig (g1Point (encodeG1 r))).tape ⟨0, hhead⟩)
            (fun phase => g1Transition_rewind_p0_bof phase _ _ _ _ g1Ctx0
              hdecode)
          rw [writeCell_self] at hstep
          refine G1RewindStepResult.handoff ?_ ?_
          · exact ⟨hhead, by simpa only [g1AlignedConfig] using hstep⟩
          · rfl
      | @step left previous _ hprevious hne =>
          have hpos : 0 < 4 * (left ++ [previous]).length := by simp
          have hstep := g1CS_aligned_step_left (encodeG1 r).length
            (4 * (left ++ [previous]).length) hhead hpos
            (G1M.initialConfig (g1Point (encodeG1 r))).tape
            (g1State .rewind .p0 frame.bits[1]! frame.bits[2]!
              frame.bits[3]! g1Ctx0)
            (g1State .rewind .p3 false false false g1Ctx0)
            ((G1M.initialConfig (g1Point (encodeG1 r))).tape
              ⟨4 * (left ++ [previous]).length, hhead⟩)
            (fun phase => g1Transition_rewind_p0_other phase _ _ _ _ g1Ctx0
              (by rw [hdecode]; simpa using hne))
          rw [writeCell_self] at hstep
          refine G1RewindStepResult.rewinding ?_ ?_
          refine ⟨left, previous, frame :: suffix, .p3, false, false, false,
            ?_, ?_, ?_, ⟨rfl, rfl, rfl⟩, hprevious⟩
          · simpa [List.append_assoc] using hframes
          · simp only [g1FramePositionOffset, List.length_append,
              List.length_cons, List.length_nil, Nat.add_zero] at hhead ⊢
            omega
          · simpa only [g1AlignedConfig, g1FramePositionOffset,
              List.length_append, List.length_cons, List.length_nil,
              Nat.add_zero, Nat.mul_add, Nat.mul_one] using hstep
          · simp [G1RewindScannerMicrostate.stepsRemaining,
              g1ReverseFrameSteps]
            omega

/-- One genuine TM step preserves the unranked structural reverse envelope. -/
theorem g1Rewind_microstate_step_exact (r : G1Request)
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (h : G1RewindScannerMicrostate r c) :
    G1RewindEnvelope r (TM.stepConfig (M := G1M) c) := by
  cases g1Rewind_microstate_step_ranked r h with
  | rewinding hnext _ => exact G1RewindEnvelope.rewinding hnext
  | handoff hdone _ => exact G1RewindEnvelope.handoff hdone

/-- The complete structural envelope is locally safe.  The handoff case only
inspects its first forward row; no pass-B execution is appended. -/
theorem g1Rewind_envelope_local_safe (r : G1Request)
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (h : G1RewindEnvelope r c) : G1LocalStepSafe c := by
  cases h with
  | rewinding hs => exact g1Rewind_microstate_local_safe r hs
  | handoff hd =>
      rcases hd with ⟨hhead, rfl⟩
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨by simp [gnLocalSpan], ?_, ?_⟩
      · intro hleft
        change (g1Transition (0 : Fin 1)
          (g1State .readBStart .p0 false false false g1Ctx0) _).snd.snd.snd =
            Move.left at hleft
        rw [g1Transition_forward_p0 G1ForwardMode.readBStart] at hleft
        exact Move.noConfusion hleft
      · intro _
        simp [gnLocalSpan]

/-- The boundary successor carries the exact structural rank
`g1ValidationRewindSteps`; the rank is a theorem, not a record field. -/
theorem g1Validation_rewind_entry_ranked (r : G1Request)
    (hc : r.Canonical) :
    ∃ h : G1RewindScannerMicrostate r
        (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          ((encodeG1 r).length + 5)),
      h.stepsRemaining = g1ValidationRewindSteps r := by
  let hhead : 4 * (encodeG1Frames r).length +
      g1FramePositionOffset .p3 < G1M.tapeLength (encodeG1 r).length := by
    simp only [g1FramePositionOffset, encodeG1Frames_length, encodeG1_length]
    exact g1_lt_tapeLength (by omega)
  let h : G1RewindScannerMicrostate r
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 5)) := {
    pre := encodeG1Frames r
    frame := .blank
    suffix := []
    position := .p3
    b0 := false
    b1 := false
    b2 := false
    frames_eq := by simp [g1ValidationFrames]
    head_lt := hhead
    config_eq := by
      rw [g1Validation_rewind_entry_exact r hc]
      apply Configuration.ext_of_components
      · rfl
      · apply Fin.ext
        simp [g1FramePositionOffset, encodeG1Frames_length, encodeG1_length]
      · rfl
    buffer := ⟨rfl, rfl, rfl⟩
    remaining := g1Validation_reverse_path r }
  refine ⟨h, ?_⟩
  simp [h, G1RewindScannerMicrostate.stepsRemaining, g1ReverseFrameSteps,
    g1ValidationRewindSteps, g1ValidationFrames]
  omega

set_option maxHeartbeats 1000000 in
/-- Safety for the exact derived rank of any structural rewind microstate. -/
theorem g1Rewind_microstate_run_safe (r : G1Request)
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (h : G1RewindScannerMicrostate r c) :
    G1RunSafe c h.stepsRemaining := by
  have hlocal := g1Rewind_microstate_local_safe r h
  cases hstep : g1Rewind_microstate_step_ranked r h with
  | handoff hdone hrank =>
      rw [hrank]
      simpa using G1RunSafe.succ (G1RunSafe.empty c) hlocal
  | rewinding hnext hrank =>
      have htail := g1Rewind_microstate_run_safe r hnext
      have hone : G1RunSafe c 1 := by
        simpa using G1RunSafe.succ (G1RunSafe.empty c) hlocal
      have htail' : G1RunSafe (TM.runConfig (M := G1M) c 1)
          hnext.stepsRemaining := by
        simpa only [runConfig_one] using htail
      have hadd := G1RunSafe.add hone htail'
      rw [← hrank]
      simpa [Nat.add_comm] using hadd
termination_by h.stepsRemaining
decreasing_by omega

/-- Closed form of the exact rewind suffix schedule. -/
theorem g1ValidationRewindSteps_closed (r : G1Request) :
    g1ValidationRewindSteps r = (encodeG1 r).length + 4 := by
  simp [g1ValidationRewindSteps, g1ValidationFrames, encodeG1_length]
  omega

/-- The merged boundary prefix plus the rewind suffix is exactly the existing
read-B handoff schedule. -/
theorem g1ValidationRewindSteps_add_boundary (r : G1Request) :
    (encodeG1 r).length + 5 + g1ValidationRewindSteps r =
      g1ReadBHandoffSteps r := by
  rw [g1ValidationRewindSteps_closed]
  simp only [g1ReadBHandoffSteps]
  omega

/-- Parametric local safety for exactly the reverse scan after the safe
validation-boundary left turn and before the read-B handoff. -/
theorem g1Validation_rewind_run_safe (r : G1Request) (hc : r.Canonical) :
    G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 5))
      (g1ValidationRewindSteps r) := by
  rcases g1Validation_rewind_entry_ranked r hc with ⟨h, hrank⟩
  rw [← hrank]
  exact g1Rewind_microstate_run_safe r h

/-- GN-3B2b composition: canonical validation plus the complete rewind is
safe for the exact pre-existing read-B handoff schedule. -/
theorem g1ValidationRewind_run_safe_to_readB (r : G1Request)
    (hc : r.Canonical) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBHandoffSteps r) := by
  have h := G1RunSafe.add (g1Validation_run_safe_through_boundary r hc)
    (g1Validation_rewind_run_safe r hc)
  rw [g1ValidationRewindSteps_add_boundary] at h
  exact h

/-- Every configuration in the composed validation/rewind prefix, including
the read-B endpoint, keeps its head inside the exact `W+5` footprint. -/
theorem g1ValidationRewind_prefix_head_lt (r : G1Request)
    (hc : r.Canonical) (j : Nat) (hj : j ≤ g1ReadBHandoffSteps r) :
    ((TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) j).head : Nat) <
        gnLocalSpan (encodeG1 r).length := by
  apply gn_run_safe_endpoint_head
  · simp [gnLocalSpan]
  · exact G1RunSafe.mono (g1ValidationRewind_run_safe_to_readB r hc) hj

/-- No proper source configuration of the composed prefix moves left from
local head zero. -/
theorem g1ValidationRewind_no_left_at_zero (r : G1Request)
    (hc : r.Canonical) (j : Nat) (hj : j < g1ReadBHandoffSteps r)
    (hzero : ((TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r))) j).head : Nat) = 0) :
    (G1M.step
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r))) j).state
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r))) j).tape
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r))) j).head)).snd.snd ≠
        Move.left := by
  intro hleft
  have hsafe := g1ValidationRewind_run_safe_to_readB r hc j hj
  exact (Nat.not_lt_zero 0) (by simpa [hzero] using hsafe.2.1 hleft)

/-- Nonvacuous arbitrary-canonical capstone: the composed safety theorem and
the existing exact configuration equality meet at the same real handoff. -/
theorem g1CS_validation_rewind_trace_safe (r : G1Request)
    (hc : r.Canonical) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ReadBHandoffSteps r) =
        g1AlignedConfig (encodeG1 r).length 0
          (g1_lt_tapeLength (by omega))
          (G1M.initialConfig (g1Point (encodeG1 r))).tape
          .readBStart .p0 false false false g1Ctx0 := by
  exact ⟨g1ValidationRewind_run_safe_to_readB r hc,
    g1CS_validate_rewind_readB_exact r hc⟩

/-! ## Nonvacuous literal false/true probes -/

namespace G1TraceSafetyProbes

open G1AResultProbes

theorem literal_done_steps :
    g1GateDoneSteps reqConstF = 151 ∧ g1GateDoneSteps reqConstT = 171 := by
  decide

theorem literal_false_done :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 151 =
      g1OutputDoneConfig reqConstF false := by
  rw [← literal_done_steps.1]
  exact g1CS_gate_done_exact reqConstF literal_canonical.2.2.2.2.1 false
    literal_specs.2.2.2.2.1

theorem literal_true_done :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 171 =
      g1OutputDoneConfig reqConstT true := by
  rw [← literal_done_steps.2]
  exact g1CS_gate_done_exact reqConstT literal_canonical.2.2.2.2.2 true
    literal_specs.2.2.2.2.2

/-- False literal at the actually attained maximum validation head `W+4`. -/
theorem literal_false_span_pred_safe :
    G1LocalStepSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstF)))
        ((encodeG1 reqConstF).length + 4)) :=
  g1CS_validation_span_pred_local_safe reqConstF
    literal_canonical.2.2.2.2.1

/-- True literal at the actually attained maximum validation head `W+4`. -/
theorem literal_true_span_pred_safe :
    G1LocalStepSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstT)))
        ((encodeG1 reqConstT).length + 4)) :=
  g1CS_validation_span_pred_local_safe reqConstT
    literal_canonical.2.2.2.2.2

end G1TraceSafetyProbes

end Pnp3.Internal.PsubsetPpoly.TM
