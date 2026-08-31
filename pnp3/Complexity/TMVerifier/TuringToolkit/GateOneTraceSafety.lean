import Complexity.TMVerifier.TuringToolkit.GateNRelocation
import Complexity.TMVerifier.TuringToolkit.GateOneOutputAccept

/-!
# GN-3B1 + GN-3B2a: structural validation trace safety (2026-08-31)

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
rewind or full-gate trace is claimed.

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

/-- The complete forward validation scan is safe at every proper prefix and
attains its exact `W+4` endpoint. -/
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
