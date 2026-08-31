import Complexity.TMVerifier.TuringToolkit.GateOneTraceSafety

/-!
# GN-3B2c1: parametric G1 pass-B trace safety (2026-08-31)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module begins at the exact merged `readBStart`/`p0`/head-zero handoff of
`g1CS_validation_rewind_trace_safe`.  It proves local-footprint safety for the
existing positive-operand-B route, strict installation scan, data probe/latch,
cursor installation, and exactly one successful cursor-walk round.  The final
capstone starts at the real `G1M.initialConfig`, uses the existing exact
schedule `g1CS_walk_iteration_exact`, and stops at `Σ(1)`.

The structural records below contain only frame decomposition, scanner buffer,
head, tape, context, and path facts.  They contain no reachability, run index,
safety, or target-machine field.  No induction over `arg2`, terminal B
exhaustion, repair sweep, pass A, full gate, `ShiftRunSafe`, GN controller,
clock, or acceptance statement is made here.  Terminal cleanup and one
reject-aware repair cycle are the separate GN-3B2c2 boundary.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private theorem g1PassB_getn {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) (hj : j < l.length) : l[j] = v := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

private theorem g1PassB_length_pos_of_get {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) : j < l.length := by
  by_contra hn
  rw [List.getElem?_eq_none (by omega)] at h
  contradiction

private theorem g1PassB_drop_cons (l : List Bool) (j : Nat)
    (hj : j < l.length) : l.drop j = l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => exact ih j (by simpa using hj)

private theorem g1PassB_replicate_split (m : Nat) (hm : 0 < m)
    (f : G1Frame) :
    List.replicate m f = List.replicate (m - 1) f ++ [f] := by
  obtain ⟨m, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  simp [List.replicate_succ']

/-! ## Small local-safety adapters -/

/-- A configuration strictly inside both local-footprint edges is safe for
one step, independently of which of the three moves its control selects. -/
theorem g1LocalStepSafe_of_interior {W : Nat}
    (c : Configuration (M := G1M) W) (hleft : 0 < (c.head : Nat))
    (hright : (c.head : Nat) + 1 < gnLocalSpan W) : G1LocalStepSafe c := by
  exact ⟨by omega, fun _ => hleft, fun _ => hright⟩

/-- A stationary or right-moving structural state at local head zero is safe. -/
theorem g1LocalStepSafe_at_zero_of_not_left {W : Nat}
    (c : Configuration (M := G1M) W) (hzero : (c.head : Nat) = 0)
    (hmove : (G1M.step c.state (c.tape c.head)).snd.snd ≠ Move.left) :
    G1LocalStepSafe c := by
  refine ⟨by simp [hzero, gnLocalSpan], ?_, ?_⟩
  · intro h; exact (hmove h).elim
  · intro _; simp [hzero, gnLocalSpan]

/-! ## A structural forward-scanner envelope -/

/-- A forward scanner configuration on an arbitrary concrete G1 frame word.
The current mode is the actual fold over `pre`; `remaining` is the strict
non-rejecting path still on tape. -/
structure G1ForwardScannerMicrostate (W : Nat) (frames : List G1Frame)
    (tape : Fin (G1M.tapeLength W) -> Bool) (start : G1Mode) (ctx : G1Ctx)
    (c : Configuration (M := G1M) W) where
  pre : List G1Frame
  frame : G1Frame
  suffix : List G1Frame
  position : G1FramePosition
  b0 : Bool
  b1 : Bool
  b2 : Bool
  frames_eq : frames = pre ++ frame :: suffix
  bits_eq : tape = g1ListTape (frames.flatMap G1Frame.bits)
  word_lt : 4 * frames.length < gnLocalSpan W
  head_lt : 4 * pre.length + g1FramePositionOffset position < G1M.tapeLength W
  config_eq : c =
    g1AlignedConfig W
      (4 * pre.length + g1FramePositionOffset position) head_lt tape
      (g1AdvanceList start pre) position b0 b1 b2 ctx
  buffer : G1ForwardBufferCoherent frame position b0 b1 b2
  remaining : G1ValidPath (g1AdvanceList start pre) (frame :: suffix)

/-- The aligned endpoint after a structural forward path is exhausted. -/
structure G1ForwardScannerHandoff (W : Nat) (frames : List G1Frame)
    (tape : Fin (G1M.tapeLength W) -> Bool) (start : G1Mode) (ctx : G1Ctx)
    (c : Configuration (M := G1M) W) where
  bits_eq : tape = g1ListTape (frames.flatMap G1Frame.bits)
  word_lt : 4 * frames.length < gnLocalSpan W
  head_lt : 4 * frames.length < G1M.tapeLength W
  config_eq : c = g1AlignedConfig W (4 * frames.length) head_lt tape
    (g1AdvanceList start frames) .p0 false false false ctx

/-- The phase-specific forward path, including its exact aligned handoff. -/
inductive G1ForwardScannerEnvelope (W : Nat) (frames : List G1Frame)
    (tape : Fin (G1M.tapeLength W) -> Bool) (start : G1Mode) (ctx : G1Ctx) :
    Configuration (M := G1M) W -> Prop
  | scanning {c} : G1ForwardScannerMicrostate W frames tape start ctx c ->
      G1ForwardScannerEnvelope W frames tape start ctx c
  | handoff {c} : G1ForwardScannerHandoff W frames tape start ctx c ->
      G1ForwardScannerEnvelope W frames tape start ctx c

private theorem g1Forward_word_bit (W : Nat) (frames pre : List G1Frame)
    (frame : G1Frame) (suffix : List G1Frame)
    (hframes : frames = pre ++ frame :: suffix)
    (j : Nat) (hj : j < 4)
    (hh : 4 * pre.length + j < G1M.tapeLength W) :
    (g1ListTape (n := W) (frames.flatMap G1Frame.bits))
        ⟨4 * pre.length + j, hh⟩ = frame.bits[j]! := by
  change (frames.flatMap G1Frame.bits).getD (4 * pre.length + j) false = _
  rw [hframes]
  have hget := G1Frame.flatMap_getElem? pre suffix frame j hj
  simp only [List.getD, hget]
  have hjbits : j < frame.bits.length := by simpa using hj
  simp [List.getElem?_eq_getElem hjbits]

private theorem g1Forward_local_room {W : Nat} {frames pre : List G1Frame}
    {frame : G1Frame} {suffix : List G1Frame} {position : G1FramePosition}
    (hframes : frames = pre ++ frame :: suffix)
    (hword : 4 * frames.length < gnLocalSpan W) :
    4 * pre.length + g1FramePositionOffset position + 1 < gnLocalSpan W := by
  have hpre : pre.length + 1 <= frames.length := by rw [hframes]; simp
  cases position <;> simp only [g1FramePositionOffset] <;> omega

/-- Every structural forward-scanner microstate is locally safe.  At `p3`,
buffer coherence plus the physical tape word turns strict `G1ValidPath` into
the exact non-rejecting right-moving completion row. -/
theorem g1Forward_microstate_localSafe {W : Nat} {frames : List G1Frame}
    {tape : Fin (G1M.tapeLength W) -> Bool} {start : G1Mode} {ctx : G1Ctx}
    {c : Configuration (M := G1M) W}
    (h : G1ForwardScannerMicrostate W frames tape start ctx c) :
    G1LocalStepSafe c := by
  rcases h with ⟨pre, frame, suffix, position, b0, b1, b2, hframes, htape,
    hword, hhead, rfl, hbuffer, hpath⟩
  have hroom := g1Forward_local_room (position := position) hframes hword
  have hfwd : G1ForwardMode (g1AdvanceList start pre) := hpath.1
  have htapeBit (j : Nat) (hj : j < 4)
      (hh : 4 * pre.length + j < G1M.tapeLength W) :
      tape ⟨4 * pre.length + j, hh⟩ = frame.bits[j]! := by
    rw [htape]
    exact g1Forward_word_bit W frames pre frame suffix hframes j hj hh
  cases position with
  | p0 =>
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨by omega, ?_, fun _ => by simpa using hroom⟩
      intro hleft
      change (g1Transition (0 : Fin 1)
        (g1State (g1AdvanceList start pre) .p0 b0 b1 b2 ctx) _).snd.snd.snd =
          Move.left at hleft
      rw [g1Transition_forward_p0 hfwd] at hleft
      exact Move.noConfusion hleft
  | p1 =>
      simp only [G1ForwardBufferCoherent] at hbuffer
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨by omega, ?_, fun _ => by simpa using hroom⟩
      intro hleft
      change (g1Transition (0 : Fin 1)
        (g1State (g1AdvanceList start pre) .p1 frame.bits[0]! false false ctx)
          _).snd.snd.snd = Move.left at hleft
      rw [g1Transition_forward_p1 hfwd] at hleft
      exact Move.noConfusion hleft
  | p2 =>
      simp only [G1ForwardBufferCoherent] at hbuffer
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨by omega, ?_, fun _ => by simpa using hroom⟩
      intro hleft
      change (g1Transition (0 : Fin 1)
        (g1State (g1AdvanceList start pre) .p2 frame.bits[0]!
          frame.bits[1]! false ctx) _).snd.snd.snd = Move.left at hleft
      rw [g1Transition_forward_p2 hfwd] at hleft
      exact Move.noConfusion hleft
  | p3 =>
      simp only [G1ForwardBufferCoherent] at hbuffer
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := htapeBit 3 (by omega) hhead
      have hcomplete : g1Complete (g1AdvanceList start pre) frame.bits[0]!
          frame.bits[1]! frame.bits[2]! frame.bits[3]! =
          g1Advance (g1AdvanceList start pre) frame :=
        g1FrameScanner.complete_of_bits _ frame (by
          cases frame with
          | data b | output b => cases b <;> rfl
          | blank | bof | tag | index | separator | cursor | finish | argSep |
              spent => rfl)
      have hnext := hpath.2.1
      simp only [G1LocalStepSafe, g1AlignedConfig_head_val,
        g1AlignedConfig_state, g1AlignedConfig_tape]
      refine ⟨by omega, ?_, fun _ => by simpa using hroom⟩
      intro hleft
      change (g1Transition (0 : Fin 1)
        (g1State (g1AdvanceList start pre) .p3 frame.bits[0]!
          frame.bits[1]! frame.bits[2]! ctx) (tape ⟨4 * pre.length + 3,
            hhead⟩)).snd.snd.snd = Move.left at hleft
      rw [hscan, g1Transition_forward_p3_advance hfwd _ _ _ _ _ _
        (by rw [hcomplete]; exact hnext)] at hleft
      exact Move.noConfusion hleft

private def G1ForwardScannerMicrostate.stepsRemaining {W : Nat}
    {frames : List G1Frame} {tape : Fin (G1M.tapeLength W) -> Bool}
    {start : G1Mode} {ctx : G1Ctx} {c : Configuration (M := G1M) W}
    (h : G1ForwardScannerMicrostate W frames tape start ctx c) : Nat :=
  4 * h.suffix.length + match h.position with
    | .p0 => 4
    | .p1 => 3
    | .p2 => 2
    | .p3 => 1

inductive G1ForwardStepResult (W : Nat) (frames : List G1Frame)
    (tape : Fin (G1M.tapeLength W) -> Bool) (start : G1Mode) (ctx : G1Ctx)
    (remaining : Nat) : Configuration (M := G1M) W -> Prop
  | scanning {c} (h : G1ForwardScannerMicrostate W frames tape start ctx c)
      (rank_eq : h.stepsRemaining + 1 = remaining) :
      G1ForwardStepResult W frames tape start ctx remaining c
  | handoff {c} (h : G1ForwardScannerHandoff W frames tape start ctx c)
      (rank_eq : remaining = 1) :
      G1ForwardStepResult W frames tape start ctx remaining c

set_option maxHeartbeats 1000000 in
/-- One actual forward-scanner step preserves the structural path and lowers
its external rank, or produces the exact aligned handoff. -/
theorem g1Forward_microstate_step {W : Nat} {frames : List G1Frame}
    {tape : Fin (G1M.tapeLength W) -> Bool} {start : G1Mode} {ctx : G1Ctx}
    {c : Configuration (M := G1M) W}
    (h : G1ForwardScannerMicrostate W frames tape start ctx c) :
    G1ForwardStepResult W frames tape start ctx h.stepsRemaining
      (TM.stepConfig (M := G1M) c) := by
  rcases h with ⟨pre, frame, suffix, position, b0, b1, b2, hframes, htape,
    hword, hhead, rfl, hbuffer, hpath⟩
  have hroomTape : 4 * pre.length + 4 < G1M.tapeLength W := by
    have hlocal := g1Forward_local_room (position := .p3) hframes hword
    exact lt_of_lt_of_le hlocal (gnLocalSpan_le_g1_tapeLength W)
  have htapeBit (j : Nat) (hj : j < 4)
      (hh : 4 * pre.length + j < G1M.tapeLength W) :
      tape ⟨4 * pre.length + j, hh⟩ = frame.bits[j]! := by
    rw [htape]
    exact g1Forward_word_bit W frames pre frame suffix hframes j hj hh
  have hfwd : G1ForwardMode (g1AdvanceList start pre) := hpath.1
  cases position with
  | p0 =>
      simp only [g1FramePositionOffset] at hhead
      simp only [G1ForwardBufferCoherent] at hbuffer
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hs := g1CS_aligned_step_right W (4 * pre.length) hhead (by omega)
        tape (g1State (g1AdvanceList start pre) .p0 false false false ctx)
        (g1State (g1AdvanceList start pre) .p1 (tape ⟨4 * pre.length,
          hhead⟩) false false ctx) _
        (fun phase => g1Transition_forward_p0 hfwd phase false false false _ ctx)
      rw [writeCell_self] at hs
      refine G1ForwardStepResult.scanning ?_ ?_
      · refine ⟨pre, frame, suffix, .p1, frame.bits[0]!, false, false,
          hframes, htape, hword, ?_, ?_, ?_, hpath⟩
        · simpa only [g1FramePositionOffset] using
            (show 4 * pre.length + 1 < G1M.tapeLength W by omega)
        · have hbit : tape ⟨4 * pre.length, hhead⟩ = frame.bits[0]! := by
            simpa using htapeBit 0 (by omega) hhead
          rw [hbit] at hs
          simpa only [g1FramePositionOffset] using hs
        · exact ⟨rfl, rfl, rfl⟩
      · simp [G1ForwardScannerMicrostate.stepsRemaining]
  | p1 =>
      simp only [g1FramePositionOffset] at hhead
      simp only [G1ForwardBufferCoherent] at hbuffer
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hs := g1CS_aligned_step_right W (4 * pre.length + 1) hhead
        (by omega) tape
        (g1State (g1AdvanceList start pre) .p1 frame.bits[0]! false false ctx)
        (g1State (g1AdvanceList start pre) .p2 frame.bits[0]!
          (tape ⟨4 * pre.length + 1, hhead⟩) false ctx) _
        (fun phase => g1Transition_forward_p1 hfwd phase frame.bits[0]! false
          false _ ctx)
      rw [writeCell_self] at hs
      refine G1ForwardStepResult.scanning ?_ ?_
      · refine ⟨pre, frame, suffix, .p2, frame.bits[0]!, frame.bits[1]!, false,
          hframes, htape, hword, ?_, ?_, ?_, hpath⟩
        · simpa only [g1FramePositionOffset] using
            (show 4 * pre.length + 2 < G1M.tapeLength W by omega)
        · have hbit : tape ⟨4 * pre.length + 1, hhead⟩ = frame.bits[1]! := by
            simpa using htapeBit 1 (by omega) hhead
          rw [hbit] at hs
          simpa only [g1FramePositionOffset] using hs
        · exact ⟨rfl, rfl, rfl⟩
      · simp [G1ForwardScannerMicrostate.stepsRemaining]
  | p2 =>
      simp only [g1FramePositionOffset] at hhead
      simp only [G1ForwardBufferCoherent] at hbuffer
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hs := g1CS_aligned_step_right W (4 * pre.length + 2) hhead
        (by omega) tape
        (g1State (g1AdvanceList start pre) .p2 frame.bits[0]!
          frame.bits[1]! false ctx)
        (g1State (g1AdvanceList start pre) .p3 frame.bits[0]!
          frame.bits[1]! (tape ⟨4 * pre.length + 2, hhead⟩) ctx) _
        (fun phase => g1Transition_forward_p2 hfwd phase frame.bits[0]!
          frame.bits[1]! false _ ctx)
      rw [writeCell_self] at hs
      refine G1ForwardStepResult.scanning ?_ ?_
      · refine ⟨pre, frame, suffix, .p3, frame.bits[0]!, frame.bits[1]!,
          frame.bits[2]!, hframes, htape, hword, ?_, ?_, ?_, hpath⟩
        · simpa only [g1FramePositionOffset] using
            (show 4 * pre.length + 3 < G1M.tapeLength W by omega)
        · have hbit : tape ⟨4 * pre.length + 2, hhead⟩ = frame.bits[2]! := by
            simpa using htapeBit 2 (by omega) hhead
          rw [hbit] at hs
          simpa only [g1FramePositionOffset] using hs
        · exact ⟨rfl, rfl, rfl⟩
      · simp [G1ForwardScannerMicrostate.stepsRemaining]
  | p3 =>
      simp only [g1FramePositionOffset] at hhead
      simp only [G1ForwardBufferCoherent] at hbuffer
      rcases hbuffer with ⟨rfl, rfl, rfl⟩
      have hscan := htapeBit 3 (by omega) hhead
      have hcomplete : g1Complete (g1AdvanceList start pre) frame.bits[0]!
          frame.bits[1]! frame.bits[2]! frame.bits[3]! =
          g1Advance (g1AdvanceList start pre) frame :=
        g1FrameScanner.complete_of_bits _ frame (by
          cases frame with
          | data b | output b => cases b <;> rfl
          | blank | bof | tag | index | separator | cursor | finish | argSep |
              spent => rfl)
      have hs := g1CS_aligned_step_right W (4 * pre.length + 3) hhead
        hroomTape tape
        (g1State (g1AdvanceList start pre) .p3 frame.bits[0]!
          frame.bits[1]! frame.bits[2]! ctx)
        (g1State (g1Complete (g1AdvanceList start pre) frame.bits[0]!
          frame.bits[1]! frame.bits[2]!
          (tape ⟨4 * pre.length + 3, hhead⟩)) .p0 false false false ctx)
        (tape ⟨4 * pre.length + 3, hhead⟩)
        (fun phase => g1Transition_forward_p3_advance hfwd phase _ _ _ _ ctx
          (by rw [hscan, hcomplete]; exact hpath.2.1))
      rw [writeCell_self, hscan, hcomplete] at hs
      cases suffix with
      | nil =>
          refine G1ForwardStepResult.handoff ?_ ?_
          · refine ⟨htape, hword, ?_, ?_⟩
            · rw [hframes]; simp at hroomTape ⊢; exact hroomTape
            · have hfold : g1AdvanceList start frames =
                  g1Advance (g1AdvanceList start pre) frame := by
                rw [hframes, g1AdvanceList_append]
                simp
              rw [hfold]
              simpa [hframes] using hs
          · simp [G1ForwardScannerMicrostate.stepsRemaining]
      | cons next rest =>
          refine G1ForwardStepResult.scanning ?_ ?_
          · refine ⟨pre ++ [frame], next, rest, .p0, false, false, false,
              ?_, htape, hword, ?_, ?_, ?_, ?_⟩
            · simpa [List.append_assoc] using hframes
            · simpa only [g1FramePositionOffset, List.length_append,
                List.length_cons, List.length_nil, Nat.add_zero] using hroomTape
            · have hfold : g1AdvanceList start (pre ++ [frame]) =
                  g1Advance (g1AdvanceList start pre) frame := by
                rw [g1AdvanceList_append]
                rfl
              rw [hfold]
              simpa only [g1FramePositionOffset, List.length_append,
                List.length_cons, List.length_nil, Nat.add_zero, Nat.mul_add,
                Nat.mul_one] using hs
            · exact ⟨rfl, rfl, rfl⟩
            · simpa [g1AdvanceList_append] using hpath.2.2
          · simp [G1ForwardScannerMicrostate.stepsRemaining]
            omega

/-- The exact external rank of a forward microstate is safe. -/
theorem g1Forward_microstate_runSafe {W : Nat} {frames : List G1Frame}
    {tape : Fin (G1M.tapeLength W) -> Bool} {start : G1Mode} {ctx : G1Ctx}
    {c : Configuration (M := G1M) W}
    (h : G1ForwardScannerMicrostate W frames tape start ctx c) :
    G1RunSafe c h.stepsRemaining := by
  have hlocal := g1Forward_microstate_localSafe h
  cases hs : g1Forward_microstate_step h with
  | handoff hd hrank =>
      rw [hrank]
      simpa using G1RunSafe.succ (G1RunSafe.empty c) hlocal
  | scanning hn hrank =>
      have htail := g1Forward_microstate_runSafe hn
      have hone : G1RunSafe c 1 := by
        simpa using G1RunSafe.succ (G1RunSafe.empty c) hlocal
      have htail' : G1RunSafe (TM.runConfig (M := G1M) c 1)
          hn.stepsRemaining := by simpa only [runConfig_one] using htail
      have hadd := G1RunSafe.add hone htail'
      rw [<- hrank]
      simpa [Nat.add_comm] using hadd
termination_by h.stepsRemaining
decreasing_by omega

/-- Entry constructor for a nonempty strict forward path. -/
def g1Forward_scan_entry {W : Nat} (frames : List G1Frame)
    (tape : Fin (G1M.tapeLength W) -> Bool) (start : G1Mode) (ctx : G1Ctx)
    (frame : G1Frame) (suffix : List G1Frame)
    (hframes : frames = frame :: suffix) (htape : tape =
      g1ListTape (frames.flatMap G1Frame.bits))
    (hword : 4 * frames.length < gnLocalSpan W)
    (hpath : G1ValidPath start frames) :
    G1ForwardScannerMicrostate W frames tape start ctx
      (g1AlignedConfig W 0 (by
        have := gnLocalSpan_le_g1_tapeLength W
        simp [gnLocalSpan] at this ⊢)
        tape start .p0 false false false ctx) := by
  refine ⟨[], frame, suffix, .p0, false, false, false, hframes, htape,
    hword, ?_, rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
  · simp [g1FramePositionOffset]
  · simpa [hframes] using hpath

/-- Exact structural forward-scan safety from an aligned head-zero entry. -/
theorem g1Forward_scan_runSafe {W : Nat} (frames : List G1Frame)
    (tape : Fin (G1M.tapeLength W) -> Bool) (start : G1Mode) (ctx : G1Ctx)
    (frame : G1Frame) (suffix : List G1Frame)
    (hframes : frames = frame :: suffix)
    (htape : tape = g1ListTape (frames.flatMap G1Frame.bits))
    (hword : 4 * frames.length < gnLocalSpan W)
    (hpath : G1ValidPath start frames) :
    G1RunSafe
      (g1AlignedConfig W 0 (by
        have := gnLocalSpan_le_g1_tapeLength W
        simp [gnLocalSpan] at this ⊢)
        tape start .p0 false false false ctx)
      (4 * frames.length) := by
  let h := g1Forward_scan_entry frames tape start ctx frame suffix hframes
    htape hword hpath
  have hs := g1Forward_microstate_runSafe h
  have hrank : h.stepsRemaining = 4 * frames.length := by
    dsimp [h, g1Forward_scan_entry,
      G1ForwardScannerMicrostate.stepsRemaining]
    simp [hframes, Nat.mul_add]
  rw [hrank] at hs
  exact hs

/-! ## Reverse seek safety -/

private theorem g1RunSafe_one {W : Nat} (c : Configuration (M := G1M) W)
    (h : G1LocalStepSafe c) : G1RunSafe c 1 := by
  simpa using G1RunSafe.succ (G1RunSafe.empty c) h

/-- Four reverse-buffer steps are safe on one physical frame.  The fourth row
may either continue left (then `base > 0`) or stop in place.  The explicit
buffer values are the exact right-to-left scanner relation. -/
theorem g1Walk_reverseFrame_runSafe {W base : Nat}
    (tape : Fin (G1M.tapeLength W) -> Bool) (ctx : G1Ctx)
    (hroom : base + 4 < gnLocalSpan W)
    (hfinal : 0 < base ∨
      G1WalkStop (g1WalkRevComplete .bSeek (tape ⟨base, by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 1, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 2, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 3, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩))) :
    G1RunSafe
      (g1AlignedConfig W (base + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .bSeek .p3 false false false ctx) 4 := by
  let hb0 : base < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb1 : base + 1 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb2 : base + 2 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb3 : base + 3 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let b3 := tape ⟨base + 3, hb3⟩
  let b2 := tape ⟨base + 2, hb2⟩
  let b1 := tape ⟨base + 1, hb1⟩
  let b0 := tape ⟨base, hb0⟩
  let c3 := g1AlignedConfig W (base + 3) hb3 tape .bSeek .p3 false false false ctx
  let c2 := g1AlignedConfig W (base + 2) hb2 tape .bSeek .p2 false false b3 ctx
  let c1 := g1AlignedConfig W (base + 1) hb1 tape .bSeek .p1 false b2 b3 ctx
  let c0 := g1AlignedConfig W base hb0 tape .bSeek .p0 b1 b2 b3 ctx
  have hs3 : TM.stepConfig (M := G1M) c3 = c2 := by
    have h := g1CS_aligned_step_left W (base + 3) hb3 (by omega) tape
      (g1State .bSeek .p3 false false false ctx)
      (g1State .bSeek .p2 false false b3 ctx) _
      (fun phase => g1Transition_bSeek_p3 phase false false false _ ctx)
    rw [writeCell_self] at h
    simpa [c3, c2, b3] using h
  have hs2 : TM.stepConfig (M := G1M) c2 = c1 := by
    have h := g1CS_aligned_step_left W (base + 2) hb2 (by omega) tape
      (g1State .bSeek .p2 false false b3 ctx)
      (g1State .bSeek .p1 false b2 b3 ctx) _
      (fun phase => g1Transition_bSeek_p2 phase false false b3 _ ctx)
    rw [writeCell_self] at h
    simpa [c2, c1, b2] using h
  have hs1 : TM.stepConfig (M := G1M) c1 = c0 := by
    have h := g1CS_aligned_step_left W (base + 1) hb1 (by omega) tape
      (g1State .bSeek .p1 false b2 b3 ctx)
      (g1State .bSeek .p0 b1 b2 b3 ctx) _
      (fun phase => g1Transition_bSeek_p1 phase false b2 b3 _ ctx)
    rw [writeCell_self] at h
    simpa [c1, c0, b1] using h
  have hlocal3 : G1LocalStepSafe c3 := by
    apply g1LocalStepSafe_of_interior <;> simp [c3, gnLocalSpan] at hroom ⊢ <;>
      omega
  have hlocal2 : G1LocalStepSafe c2 := by
    apply g1LocalStepSafe_of_interior <;> simp [c2, gnLocalSpan] at hroom ⊢ <;>
      omega
  have hlocal1 : G1LocalStepSafe c1 := by
    apply g1LocalStepSafe_of_interior <;> simp [c1, gnLocalSpan] at hroom ⊢ <;>
      omega
  have hlocal0 : G1LocalStepSafe c0 := by
    simp only [G1LocalStepSafe, c0, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by simpa [gnLocalSpan] using (show base < gnLocalSpan W by omega),
      ?_, ?_⟩
    · intro hleft
      by_cases hstop : G1WalkStop (g1WalkRevComplete .bSeek b0 b1 b2 b3)
      · change (g1Transition (0 : Fin 1)
          (g1State .bSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd = Move.left at hleft
        have htr := g1WalkScanner.rstep_p0_stop (m := .bSeek) trivial ctx b1 b2
          b3 b0 hstop
        change g1Transition 0 (g1State .bSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1State (g1WalkRevComplete .bSeek b0 b1 b2 b3) .p0 false false
            false ctx, b0, Move.stay) at htr
        rw [htr] at hleft
        exact Move.noConfusion hleft
      · rcases hfinal with hpos | hstop'
        · simpa [c0] using hpos
        · exact (hstop hstop').elim
    · intro hright
      by_cases hstop : G1WalkStop (g1WalkRevComplete .bSeek b0 b1 b2 b3)
      · change (g1Transition (0 : Fin 1)
          (g1State .bSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd = Move.right at hright
        have htr := g1WalkScanner.rstep_p0_stop (m := .bSeek) trivial ctx b1 b2
          b3 b0 hstop
        change g1Transition 0 (g1State .bSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1State (g1WalkRevComplete .bSeek b0 b1 b2 b3) .p0 false false
            false ctx, b0, Move.stay) at htr
        rw [htr] at hright
        exact Move.noConfusion hright
      · change (g1Transition (0 : Fin 1)
          (g1State .bSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd = Move.right at hright
        have htr := g1WalkScanner.rstep_p0 (m := .bSeek) trivial ctx b1 b2 b3 b0
          hstop
        change g1Transition 0 (g1State .bSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1State (g1WalkRevComplete .bSeek b0 b1 b2 b3) .p3 false false
            false ctx, b0, Move.left) at htr
        rw [htr] at hright
        exact Move.noConfusion hright
  have hr1 : TM.runConfig (M := G1M) c3 1 = c2 := by
    simpa only [runConfig_one] using hs3
  have hr2 : TM.runConfig (M := G1M) c3 2 = c1 := by
    rw [show (2 : Nat) = 1 + 1 by omega, runConfig_add, hr1, runConfig_one,
      hs2]
  have hr3 : TM.runConfig (M := G1M) c3 3 = c0 := by
    rw [show (3 : Nat) = 2 + 1 by omega, runConfig_add, hr2, runConfig_one,
      hs1]
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with
    rfl | rfl | rfl | rfl
  · change G1LocalStepSafe c3
    exact hlocal3
  · change G1LocalStepSafe (TM.runConfig (M := G1M) c3 1)
    rw [hr1]
    exact hlocal2
  · change G1LocalStepSafe (TM.runConfig (M := G1M) c3 2)
    rw [hr2]
    exact hlocal1
  · change G1LocalStepSafe (TM.runConfig (M := G1M) c3 3)
    rw [hr3]
    exact hlocal0

/-- A homogeneous right-to-left `bSeek` scan is safe for exactly four steps
per skipped frame. -/
theorem g1Walk_revSkip_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f, f ∈ skipped -> g1WalkRevAdvance .bSeek f = .bSeek)
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) .bSeek .p3 false false false ctx)
      (4 * skipped.length) := by
  induction skipped using List.reverseRecOn generalizing suffix with
  | nil => exact G1RunSafe.empty _
  | append_singleton rest frame ih =>
      have hframe : g1WalkRevAdvance .bSeek frame = .bSeek :=
        hskip frame (by simp)
      have hrest : ∀ f, f ∈ rest -> g1WalkRevAdvance .bSeek f = .bSeek := by
        intro f hf; exact hskip f (by simp [hf])
      have hword' : 4 * (pre.length + rest.length + 1) + 8 <
          gnLocalSpan W := by
        simpa using hword
      let tape := g1ListTape (n := W)
        ((pre ++ marker :: (rest ++ [frame]) ++ suffix).flatMap G1Frame.bits)
      have hframeSafe : G1RunSafe
          (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3) (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
            tape .bSeek .p3 false false false ctx) 4 :=
        g1Walk_reverseFrame_runSafe tape ctx (by omega) (Or.inl (by omega))
      have hframe' : g1WalkScanner.revAdvance .bSeek frame = .bSeek := hframe
      have hphysical : 4 * (pre ++ marker :: rest).length + 4 <
          G1M.tapeLength W := by
        apply lt_of_lt_of_le (b := gnLocalSpan W)
        · simp only [List.length_append, List.length_cons]
          omega
        · exact gnLocalSpan_le_g1_tapeLength W
      have hmacro := g1WalkScanner.revFrameMacrostepAt W
        (4 * (pre.length + rest.length + 1))
        (4 * (pre.length + rest.length) + 3) (by omega)
        (lt_of_lt_of_le (by
          omega) (gnLocalSpan_le_g1_tapeLength W)) tape .bSeek frame ctx trivial
        (by
          rw [hframe']
          change ¬ G1WalkStop .bSeek
          intro hs
          rcases hs with hs | hs <;> contradiction)
        (by
          have hbits := physicalBitsAt_flatMap (L := G1M.tapeLength W)
            g1FrameCodec (pre ++ marker :: rest) suffix frame hphysical
          simpa [tape, List.append_assoc] using hbits)
      have htail := ih (suffix := frame :: suffix) hrest (by omega)
      have hstartTape : 4 * (pre.length + rest.length + 1) + 3 <
          G1M.tapeLength W :=
        lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
      have hmacro' : TM.runConfig (M := G1M)
          (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3)
            hstartTape tape .bSeek .p3 false false false ctx) 4 =
        g1AlignedConfig W (4 * (pre.length + rest.length) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .bSeek .p3 false false false ctx := by
        change TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3) _
              tape .bSeek .p3 false false false ctx) 4 =
          g1AlignedConfig W (4 * (pre.length + rest.length) + 3) _ tape
            (g1WalkRevAdvance .bSeek frame) .p3 false false false ctx at hmacro
        rw [hframe] at hmacro
        exact hmacro
      have htail' : G1RunSafe
          (TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3)
              hstartTape tape .bSeek .p3 false false false ctx) 4)
          (4 * rest.length) := by
        rw [hmacro']
        simpa [tape, List.append_assoc] using htail
      have hadd := G1RunSafe.add hframeSafe htail'
      simpa [tape, Nat.mul_add, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hadd

/-- The complete reverse seek through `skipped` and its stopping marker is
safe for the exact schedule used by `g1CS_walk_seek_to_index`. -/
theorem g1Walk_seekToMarker_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f, f ∈ skipped -> g1WalkRevAdvance .bSeek f = .bSeek)
    (hstop : G1WalkStop (g1WalkRevAdvance .bSeek marker))
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) .bSeek .p3 false false false ctx)
      (4 * skipped.length + 4) := by
  let tape := g1ListTape (n := W)
    ((pre ++ marker :: skipped ++ suffix).flatMap G1Frame.bits)
  have hscan := g1Walk_revSkip_runSafe pre marker skipped suffix ctx hskip hword
  have hscanExact := g1WalkScanner.revSkipRun W pre marker skipped suffix .bSeek
    ctx trivial (by
      change ¬ G1WalkStop .bSeek
      intro hs
      rcases hs with hs | hs <;> contradiction) hskip (by
      exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
  have hmarker : G1RunSafe
      (g1AlignedConfig W (4 * pre.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .bSeek .p3 false false false ctx) 4 := by
    have hmarkerRoom : 4 * pre.length + 4 < gnLocalSpan W := by
      have hpre : pre.length <= pre.length + skipped.length := by omega
      omega
    apply g1Walk_reverseFrame_runSafe tape ctx hmarkerRoom
    · right
      have hbits := physicalBitsAt_flatMap (L := G1M.tapeLength W)
        g1FrameCodec pre (skipped ++ suffix) marker (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
      have hc := g1WalkScanner.revComplete_of_bits .bSeek marker
        (by simpa [physicalBitsAt] using hbits)
      have hc' : g1WalkRevComplete .bSeek
          (tape ⟨4 * pre.length, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
          (tape ⟨4 * pre.length + 1, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
          (tape ⟨4 * pre.length + 2, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
          (tape ⟨4 * pre.length + 3, by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩) =
          g1WalkRevAdvance .bSeek marker := by
        simpa [tape, List.append_assoc] using hc
      exact hc'.symm ▸ hstop
  have hmarker' : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .bSeek .p3 false false false ctx) (4 * skipped.length)) 4 := by
    have hscanExact' : TM.runConfig (M := G1M)
        (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .bSeek .p3 false false false ctx) (4 * skipped.length) =
        g1AlignedConfig W (4 * pre.length + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .bSeek .p3 false false false ctx := by
      simpa [tape, g1WalkScanner, ReverseFrameScanner.revAligned] using
        hscanExact
    rw [hscanExact']
    exact hmarker
  exact G1RunSafe.add hscan hmarker'

/-! ## Macro-segment adapters -/

private theorem g1Step_head_le_next_add_one {W : Nat}
    (c : Configuration (M := G1M) W) :
    (c.head : Nat) <= ((TM.stepConfig (M := G1M) c).head : Nat) + 1 := by
  rw [stepConfig_head]
  generalize hm : (G1M.step c.state (c.tape c.head)).snd.snd = move
  cases move with
  | stay => simp
  | left =>
      by_cases hzero : (c.head : Nat) = 0
      · simp [hzero]
      · rw [Configuration.moveHead_left_val_of_pos c (by omega)]
        omega
  | right =>
      by_cases hright : (c.head : Nat) + 1 < G1M.tapeLength W
      · rw [Configuration.moveHead_right_lt c hright]
        simp only [Fin.val_mk]
        omega
      · rw [Configuration.moveHead_right_clamp c hright]
        exact Nat.le_succ _

private theorem g1Run_head_start_le_add {W k : Nat}
    (c : Configuration (M := G1M) W) :
    (c.head : Nat) <= ((TM.runConfig (M := G1M) c k).head : Nat) + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [runConfig_succ]
      have hs := g1Step_head_le_next_add_one
        (TM.runConfig (M := G1M) c k)
      omega

/-- A short segment with enough margin on both sides is locally safe without
inspecting its phase-specific control. -/
theorem g1RunSafe_of_margins {W k : Nat}
    (c : Configuration (M := G1M) W) (hleft : k < (c.head : Nat))
    (hright : (c.head : Nat) + k < gnLocalSpan W) : G1RunSafe c k := by
  intro j hj
  apply g1LocalStepSafe_of_interior
  · have hlo := g1Run_head_start_le_add (k := j) c
    omega
  · have hhi := g1_runConfig_head_le_start_add (k := j) c
    omega

/-- Four exact right-moving scanner cells are safe on an arbitrary physical
frame whose decoded completion is non-rejecting. -/
theorem g1Forward_frame_runSafe {W base : Nat}
    (tape : Fin (G1M.tapeLength W) -> Bool) (mode : G1Mode) (frame : G1Frame)
    (ctx : G1Ctx) (hmode : G1ForwardMode mode)
    (hnext : g1Advance mode frame ≠ .reject)
    (hroom : base + 4 < gnLocalSpan W)
    (hbits : physicalBitsAt (by
      exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape =
        frame.bits) :
    G1RunSafe (g1AlignedConfig W base (by
      exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
      mode .p0 false false false ctx) 4 := by
  have hspan := gnLocalSpan_le_g1_tapeLength W
  have hb0 : base < G1M.tapeLength W := by omega
  have hb1 : base + 1 < G1M.tapeLength W := by omega
  have hb2 : base + 2 < G1M.tapeLength W := by omega
  have htape (i : Nat) (hi : i < 4) :
      tape ⟨base + i, by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩ =
        frame.bits[i]! := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with
      rfl | rfl | rfl | rfl
    · simpa [physicalBitsAt] using congrArg (fun xs => xs[0]!) hbits
    · simpa [physicalBitsAt] using congrArg (fun xs => xs[1]!) hbits
    · simpa [physicalBitsAt] using congrArg (fun xs => xs[2]!) hbits
    · simpa [physicalBitsAt] using congrArg (fun xs => xs[3]!) hbits
  let b0 := frame.bits[0]!
  let b1 := frame.bits[1]!
  let b2 := frame.bits[2]!
  let c0 := g1AlignedConfig W base (by
    exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape mode
    .p0 false false false ctx
  let c1 := g1AlignedConfig W (base + 1) (by
    exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape mode
    .p1 b0 false false ctx
  let c2 := g1AlignedConfig W (base + 2) (by
    exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape mode
    .p2 b0 b1 false ctx
  let c3 := g1AlignedConfig W (base + 3) (by
    exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape mode
    .p3 b0 b1 b2 ctx
  have hs0 : TM.stepConfig (M := G1M) c0 = c1 := by
    have hbit : tape ⟨base, hb0⟩ = frame.bits[0]! := by
      simpa using htape 0 (by omega)
    have h := g1CS_aligned_step_right W base
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
      (g1State mode .p0 false false false ctx)
      (g1State mode .p1 (tape ⟨base, hb0⟩) false false ctx)
      (tape ⟨base, hb0⟩)
      (fun phase => g1Transition_forward_p0 hmode phase false false false _ ctx)
    rw [writeCell_self] at h
    simpa [c0, c1, b0, hbit] using h
  have hs1 : TM.stepConfig (M := G1M) c1 = c2 := by
    have hbit : tape ⟨base + 1, hb1⟩ = frame.bits[1]! := by
      simpa using htape 1 (by omega)
    have h := g1CS_aligned_step_right W (base + 1)
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
      (g1State mode .p1 b0 false false ctx)
      (g1State mode .p2 b0 (tape ⟨base + 1, hb1⟩) false ctx)
      (tape ⟨base + 1, hb1⟩)
      (fun phase => g1Transition_forward_p1 hmode phase b0 false false _ ctx)
    rw [writeCell_self] at h
    simpa [c1, c2, b1, hbit] using h
  have hs2 : TM.stepConfig (M := G1M) c2 = c3 := by
    have hbit : tape ⟨base + 2, hb2⟩ = frame.bits[2]! := by
      simpa using htape 2 (by omega)
    have h := g1CS_aligned_step_right W (base + 2)
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
      (g1State mode .p2 b0 b1 false ctx)
      (g1State mode .p3 b0 b1 (tape ⟨base + 2, hb2⟩) ctx)
      (tape ⟨base + 2, hb2⟩)
      (fun phase => g1Transition_forward_p2 hmode phase b0 b1 false _ ctx)
    rw [writeCell_self] at h
    simpa [c2, c3, b2, hbit] using h
  have hl0 : G1LocalStepSafe c0 := by
    simp only [G1LocalStepSafe, c0, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by omega, ?_, by omega⟩
    intro hl
    change (g1Transition 0 (g1State mode .p0 false false false ctx) _).snd.snd.snd =
      Move.left at hl
    rw [g1Transition_forward_p0 hmode] at hl
    contradiction
  have hl1 : G1LocalStepSafe c1 := by
    simp only [G1LocalStepSafe, c1, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by omega, ?_, by omega⟩
    intro hl
    change (g1Transition 0 (g1State mode .p1 b0 false false ctx) _).snd.snd.snd =
      Move.left at hl
    rw [g1Transition_forward_p1 hmode] at hl
    contradiction
  have hl2 : G1LocalStepSafe c2 := by
    simp only [G1LocalStepSafe, c2, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by omega, ?_, by omega⟩
    intro hl
    change (g1Transition 0 (g1State mode .p2 b0 b1 false ctx) _).snd.snd.snd =
      Move.left at hl
    rw [g1Transition_forward_p2 hmode] at hl
    contradiction
  have hl3 : G1LocalStepSafe c3 := by
    simp only [G1LocalStepSafe, c3, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by omega, ?_, by omega⟩
    intro hl
    have hc : g1Complete mode frame.bits[0]! frame.bits[1]! frame.bits[2]!
        frame.bits[3]! = g1Advance mode frame :=
      g1FrameScanner.complete_of_bits mode frame (by
        cases frame with
        | data b | output b => cases b <;> rfl
        | blank | bof | tag | index | separator | cursor | finish | argSep |
            spent => rfl)
    change (g1Transition 0 (g1State mode .p3 b0 b1 b2 ctx)
      (tape ⟨base + 3, by
        exact lt_of_lt_of_le (by omega)
          (gnLocalSpan_le_g1_tapeLength W)⟩)).snd.snd.snd = Move.left at hl
    rw [g1Transition_forward_p3_advance hmode _ _ _ _ _ ctx (by
      rw [show tape ⟨base + 3, by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩ =
          frame.bits[3]! from htape 3 (by omega), hc]
      exact hnext)] at hl
    contradiction
  have hr1 : TM.runConfig (M := G1M) c0 1 = c1 := by
    simpa only [runConfig_one] using hs0
  have hr2 : TM.runConfig (M := G1M) c0 2 = c2 := by
    rw [show (2 : Nat) = 1 + 1 by omega, runConfig_add, hr1, runConfig_one, hs1]
  have hr3 : TM.runConfig (M := G1M) c0 3 = c3 := by
    rw [show (3 : Nat) = 2 + 1 by omega, runConfig_add, hr2, runConfig_one, hs2]
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with
    rfl | rfl | rfl | rfl
  · exact hl0
  · rw [hr1]; exact hl1
  · rw [hr2]; exact hl2
  · rw [hr3]; exact hl3

/-- A strict valid forward path on an arbitrary surrounding frame list is
safe for its exact four-steps-per-frame schedule. -/
theorem g1Forward_scanFrom_runSafe {W : Nat} (pre frames suffix : List G1Frame)
    (mode : G1Mode) (ctx : G1Ctx) (hpath : G1ValidPath mode frames)
    (hroom : 4 * (pre.length + frames.length) < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * pre.length) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ frames ++ suffix).flatMap G1Frame.bits)) mode
        .p0 false false false ctx) (4 * frames.length) := by
  induction frames generalizing pre mode with
  | nil => exact G1RunSafe.empty _
  | cons frame rest ih =>
      obtain ⟨hfwd, hnext, hrest⟩ := hpath
      let tape := g1ListTape (n := W)
        ((pre ++ frame :: rest ++ suffix).flatMap G1Frame.bits)
      have hframeRoom : 4 * pre.length + 4 < gnLocalSpan W := by
        simp only [List.length_cons] at hroom
        omega
      have hbits := physicalBitsAt_flatMap (L := G1M.tapeLength W) g1FrameCodec
        pre (rest ++ suffix) frame (lt_of_lt_of_le hframeRoom
          (gnLocalSpan_le_g1_tapeLength W))
      have hfirst := g1Forward_frame_runSafe tape mode frame ctx hfwd hnext
        hframeRoom (by simpa [tape, List.append_assoc] using hbits)
      have hmacro := g1FrameScanner.frameMacrostep W (4 * pre.length)
        (lt_of_lt_of_le hframeRoom (gnLocalSpan_le_g1_tapeLength W)) tape mode
        frame ctx hfwd hnext (by simpa [tape, List.append_assoc] using hbits)
      have htail := ih (pre := pre ++ [frame]) (mode := g1Advance mode frame)
        hrest (by simp only [List.length_append, List.length_cons,
          List.length_nil] at hroom ⊢; omega)
      have hbaseTape : 4 * pre.length < G1M.tapeLength W :=
        lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
      have hnextTape : 4 * pre.length + 4 < G1M.tapeLength W :=
        lt_of_lt_of_le hframeRoom (gnLocalSpan_le_g1_tapeLength W)
      have htail' : G1RunSafe
          (TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * pre.length) (by
              exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
              tape mode .p0 false false false ctx) 4) (4 * rest.length) := by
        have hmacro' : TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * pre.length) hbaseTape tape mode .p0 false false
              false ctx) 4 =
          g1AlignedConfig W (4 * pre.length + 4) hnextTape tape
            (g1Advance mode frame) .p0 false false false ctx := by
          change TM.runConfig (M := G1M)
              (g1AlignedConfig W (4 * pre.length) hbaseTape tape mode .p0 false false
                false ctx) 4 =
            g1AlignedConfig W (4 * pre.length + 4) hnextTape tape
              (g1Advance mode frame) .p0 false false false ctx at hmacro
          exact hmacro
        rw [hmacro']
        simpa [tape, List.append_assoc] using htail
      have hadd := G1RunSafe.add hfirst htail'
      simpa [tape, Nat.mul_add, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hadd

/-! ## Existing pass-B macro schedules, made safe -/

/-- The existing reverse-seek-plus-mark schedule is safe.  The marker prefix has
at least two frames in every pass-B use; the footprint bound is the local-copy
bound. -/
theorem g1CS_walk_seek_mark_runSafe {W : Nat} (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 1 < pre.length)
    (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hroom : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape
          ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
        .bSeek .p3 false false false ctx) (4 * skipped.length + 8) := by
  let start := g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
    exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
    (g1ListTape
      ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
    .bSeek .p3 false false false ctx
  have hseek := g1Walk_seekToMarker_runSafe pre .index skipped suffix ctx
    (fun f hf => g1WalkRevAdvance_of_skip (hskip f hf)) (Or.inl rfl) hroom
  have hexact := g1CS_walk_seek_to_index W pre skipped suffix ctx hskip
    (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
  have hmark : G1RunSafe
      (TM.runConfig (M := G1M) start (4 * skipped.length + 4)) 4 := by
    rw [show start = g1AlignedConfig W
      (4 * (pre.length + skipped.length) + 3) _
      (g1ListTape
        ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
      .bSeek .p3 false false false ctx from rfl, hexact]
    apply g1RunSafe_of_margins
    · simp only [g1AlignedConfig_head_val]; omega
    · simp only [g1AlignedConfig_head_val]; omega
  have hadd := G1RunSafe.add hseek hmark
  simpa [start] using hadd

/-- The existing forward scan across the skip run and cursor is safe for its
exact `4 * (skipped.length + 1)` schedule. -/
theorem g1CS_walk_fwd_to_cursor_runSafe {W : Nat}
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hroom : 4 * (pre.length + skipped.length + 1) < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * pre.length) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx) (4 * (skipped.length + 1)) := by
  have hfix : ∀ f ∈ skipped, g1Advance .bFwd f = .bFwd :=
    fun f hf => g1Advance_bFwd_of_skip (hskip f hf)
  have hpath : G1ValidPath .bFwd (skipped ++ [.cursor]) :=
    g1ValidPath_fix (mode := .bFwd) trivial [.cursor]
      ⟨trivial, by decide, trivial⟩ skipped hfix
  have hlist : pre ++ (skipped ++ [.cursor]) ++ suffix =
      pre ++ skipped ++ .cursor :: suffix := by simp [List.append_assoc]
  have hs := g1Forward_scanFrom_runSafe pre (skipped ++ [.cursor]) suffix
    .bFwd ctx hpath (by simpa using hroom)
  rw [hlist] at hs
  simpa using hs

/-- Safety of the exact merged read-B route, from the real initial
configuration through the strict positive-operand-B installation scan. -/
theorem g1CS_readB_install_scan_runSafe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1InstallScanSteps r) := by
  let route := g1InstallRouteFrames r
  let rest := g1InstallRouteRest r
  have hroom : 4 * route.length < gnLocalSpan (encodeG1 r).length := by
    simp [route, gnLocalSpan, encodeG1_length]
    omega
  have htape : g1ListTape (n := (encodeG1 r).length)
      (([] ++ route ++ rest).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [List.nil_append, show route ++ rest = encodeG1Frames r ++ [.blank] by
      exact g1InstallRoute_split r]
    exact g1ListTape_validation_eq_initial r
  have htape' : g1ListTape (n := (encodeG1 r).length)
      ((route ++ rest).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    simpa using htape
  have hscan0 := g1Forward_scanFrom_runSafe (W := (encodeG1 r).length)
    ([] : List G1Frame) route rest .readBStart g1Ctx0
    (g1InstallRoute_validPath r ht k h2) (by simpa using hroom)
  have hscan : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r))) (g1ReadBHandoffSteps r))
      (4 * route.length) := by
    apply G1RunSafe.transport _ hscan0
    rw [g1CS_validate_rewind_readB_exact r hc]
    simp only [List.length_nil, Nat.mul_zero]
    rw [show ([] : List G1Frame) ++ route ++ rest = route ++ rest by simp,
      htape']
  have hadd := G1RunSafe.add (g1ValidationRewind_run_safe_to_readB r hc) hscan
  simpa [g1InstallScanSteps, route, g1InstallRouteFrames_length] using hadd

/-- Route, probe/latch, and cursor installation are safe from the real initial
configuration.  The existing exact endpoint theorem is paired with this safety
result by the one-round capstone below. -/
theorem g1CS_walk_install_runSafe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1WalkInstallSteps r) := by
  have hm : 0 < r.vals.length := by
    by_contra hn
    have he : r.vals = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [he] at hv
    contradiction
  have hunit : 2 ≤ r.tag.units := by
    rcases ht with ht | ht <;> rw [ht] <;> decide
  have htail : G1RunSafe
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r)) 9 := by
    rw [g1CS_readB_install_scan_exact r hc ht k h2]
    apply g1RunSafe_of_margins
    · simp only [g1AlignedConfig_head_val]
      omega
    · simp only [g1AlignedConfig_head_val]
      simp [gnLocalSpan, encodeG1_length]
      omega
  have hadd := G1RunSafe.add
    (g1CS_readB_install_scan_runSafe r hc ht k h2) htail
  simpa [g1WalkInstallSteps] using hadd

/-! ## Exactly one successful cursor-walk round -/

set_option maxHeartbeats 1000000

/-- One successful round is safe on every canonical walk configuration in the
domain of `g1CS_walk_iteration_exact`.  This is one round, not a driver. -/
theorem g1CS_walk_iteration_runSafe (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj1 : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    G1RunSafe (g1WalkConfig r j (by omega) (by omega) v hv)
      (16 * j + 37) := by
  let preA := g1FieldRouteFrames r ++
    List.replicate (r.arg2 - j - 1) G1Frame.index
  let skip := List.replicate j G1Frame.spent ++ [.separator] ++
    (r.vals.take j).map G1Frame.data
  let tail := (r.vals.drop (j + 1)).map G1Frame.data ++
    [.output false, .finish, .blank]
  have hj : j < r.vals.length := by omega
  have hpreA : preA.length =
      r.tag.units + r.arg1 + 3 + (r.arg2 - j - 1) := by simp [preA]
  have hskipLen : skip.length = 2 * j + 1 := by
    simp [skip, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    omega
  have hcursor : preA.length + skip.length + 1 = g1WalkCursor r j := by
    rw [hpreA, hskipLen]
    simp only [g1WalkCursor]
    omega
  have hsplit0 : preA ++ .index :: skip ++ .cursor :: tail =
      g1WalkFrames r j := by
    dsimp [preA, skip, tail]
    rw [g1WalkFrames,
      g1PassB_replicate_split (r.arg2 - j) (by omega) .index]
    simp [List.append_assoc]
  have hskip : ∀ f ∈ skip, G1WalkSkip f := by
    simpa [skip] using g1WalkSkipRun_mem j r.vals
  have hroomA : 4 * (preA.length + skip.length) + 8 <
      gnLocalSpan (encodeG1 r).length := by
    simp [gnLocalSpan, encodeG1_length]
    have := hcursor
    omega
  have hA0 := g1CS_walk_seek_mark_runSafe
    (W := (encodeG1 r).length) preA skip (.cursor :: tail) (g1Ctx0.withVB v)
    (by rw [hpreA]; omega) hskip hroomA
  have hheadA : 4 * (preA.length + skip.length) + 3 =
      4 * g1WalkCursor r j - 1 := by
    have := hcursor
    omega
  have hcostA : 4 * skip.length + 8 = 8 * j + 12 := by
    rw [hskipLen]
    omega
  have hA : G1RunSafe (g1WalkConfig r j (by omega) (by omega) v hv)
      (8 * j + 12) := by
    rw [hsplit0] at hA0
    simpa only [g1WalkConfig, hheadA, hcostA] using hA0
  let marked := preA ++ .spent :: skip ++ .cursor :: tail
  have hAeq : TM.runConfig (M := G1M)
      (g1WalkConfig r j (by omega) (by omega) v hv) (8 * j + 12) =
      g1AlignedConfig (encodeG1 r).length (4 * preA.length + 4) (by
        exact lt_of_lt_of_le (by omega)
          (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
        (g1ListTape (marked.flatMap G1Frame.bits)) .bFwd .p0 false false false
        (g1Ctx0.withVB v) := by
    have h := g1CS_walk_seek_mark (encodeG1 r).length preA skip
      (.cursor :: tail) (g1Ctx0.withVB v) hskip
      (lt_of_lt_of_le (by omega)
        (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
    rw [hsplit0] at h
    simpa only [g1WalkConfig, hheadA, hcostA] using h
  let preB := preA ++ [.spent]
  have hpreB : preB.length = preA.length + 1 := by simp [preB]
  have hheadB : 4 * preB.length = 4 * preA.length + 4 := by
    rw [hpreB]
    omega
  have hcostB : 4 * (skip.length + 1) = 8 * j + 8 := by
    rw [hskipLen]
    omega
  have hmarked : preB ++ skip ++ .cursor :: tail = marked := by
    simp [preB, marked, List.append_assoc]
  have hroomB : 4 * (preB.length + skip.length + 1) <
      gnLocalSpan (encodeG1 r).length := by
    simp [preA, preB, skip, gnLocalSpan, encodeG1_length]
    omega
  have hB0 := g1CS_walk_fwd_to_cursor_runSafe
    (W := (encodeG1 r).length) preB skip tail (g1Ctx0.withVB v) hskip hroomB
  rw [hmarked] at hB0
  have hB : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1WalkConfig r j (by omega) (by omega) v hv) (8 * j + 12))
      (8 * j + 8) := by
    apply G1RunSafe.transport hAeq.symm
    simpa only [hheadB, hcostB] using hB0
  have hAB := G1RunSafe.add hA hB
  have hABeq : TM.runConfig (M := G1M)
      (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 20) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1WalkCursor r j + 1)) (by
          exact lt_of_lt_of_le (by omega)
            (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
        (g1ListTape (marked.flatMap G1Frame.bits)) .bTurn .p0 false false false
        (g1Ctx0.withVB v) := by
    rw [show 16 * j + 20 = (8 * j + 12) + (8 * j + 8) by omega,
      runConfig_add, hAeq]
    have h := g1CS_walk_fwd_to_cursor (encodeG1 r).length preB skip tail
      (g1Ctx0.withVB v) hskip
      (lt_of_lt_of_le (by omega)
        (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
    rw [hmarked] at h
    have hendB : 4 * (preB.length + (skip.length + 1)) =
        4 * (g1WalkCursor r j + 1) := by
      rw [hpreB]
      have := hcursor
      omega
    simpa only [hheadB, hcostB, hendB] using h
  have hspaceCD : 4 * (g1WalkCursor r j + 1) + 8 <
      gnLocalSpan (encodeG1 r).length := by
    simp [g1WalkCursor, gnLocalSpan, encodeG1_length]
    omega
  have hCD : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 20)) 8 := by
    rw [hABeq]
    apply g1RunSafe_of_margins
    · simp [g1WalkCursor]; omega
    · simpa only [g1AlignedConfig_head_val] using hspaceCD
  have hABC := G1RunSafe.add hAB (by
    simpa only [show 8 * j + 12 + (8 * j + 8) = 16 * j + 20 by omega] using hCD)
  have hprefix : G1RunSafe (g1WalkConfig r j (by omega) (by omega) v hv)
      (16 * j + 28) := by
    simpa only [show (8 * j + 12 + (8 * j + 8)) + 8 = 16 * j + 28 by omega]
      using hABC
  let preC := preA ++ .spent :: skip
  have hpreC : preC.length = g1WalkCursor r j := by
    simp [preC]
    omega
  have hroomC : 4 * preC.length + 4 <
      gnLocalSpan (encodeG1 r).length := by
    rw [hpreC]
    omega
  let restored := preC ++ .data v :: tail
  have hmarkedC : preC ++ .cursor :: tail = marked := by
    simp [preC, marked, List.append_assoc]
  have hP28eq : TM.runConfig (M := G1M)
      (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 28) =
      g1AlignedConfig (encodeG1 r).length (4 * preC.length + 4) (by
        exact lt_of_lt_of_le hroomC
          (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
        (g1ListTape (restored.flatMap G1Frame.bits)) .bProbe2 .p0 false false
        false (g1Ctx0.withVB v) := by
    have hturn := g1CS_walk_turn (encodeG1 r).length (4 * preC.length)
      (lt_of_lt_of_le hroomC
        (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
      (g1ListTape (n := (encodeG1 r).length)
        (marked.flatMap G1Frame.bits)) (g1Ctx0.withVB v)
    have hrestore := g1CS_walk_restore (encodeG1 r).length preC tail v
      (g1Ctx0.withVB v) (lt_of_lt_of_le hroomC
        (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
    rw [show 16 * j + 28 = (16 * j + 20) + (4 + 4) by omega,
      runConfig_add, hABeq, runConfig_add]
    rw [hmarkedC] at hrestore
    simpa [hpreC, marked, restored] using Eq.trans
        (congrArg (fun c => TM.runConfig (M := G1M) c 4) hturn) hrestore
  have hspaceE : 4 * preC.length + 4 + 5 <
      gnLocalSpan (encodeG1 r).length := by rw [hpreC]; omega
  have hEF : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 28)) 9 := by
    have hE : G1RunSafe
        (TM.runConfig (M := G1M)
          (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 28)) 5 := by
      rw [hP28eq]
      apply g1RunSafe_of_margins
      · simp [preA, preC, skip]; omega
      · simpa only [g1AlignedConfig_head_val] using hspaceE
    have hdv' : r.vals[j + 1] = v' := g1PassB_getn hv' hj1
    let preE := preC ++ [.data v]
    have hpreE : preE.length = g1WalkCursor r j + 1 := by
      simp [preE, hpreC]
    have hroomE : 4 * preE.length + 4 <
        gnLocalSpan (encodeG1 r).length := by rw [hpreE]; omega
    have hspaceF : 4 * preE.length + 3 + 4 <
        gnLocalSpan (encodeG1 r).length := by rw [hpreE]; omega
    let tailE := (r.vals.drop (j + 2)).map G1Frame.data ++
      [.output false, .finish, .blank]
    have hrestE : preE ++ .data v' :: tailE = restored := by
      have hd := g1PassB_drop_cons r.vals (j + 1) hj1
      rw [hdv'] at hd
      simp [preE, preC, restored, tail, tailE, hd, List.append_assoc]
    have hEeq : TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (g1WalkConfig r j (by omega) (by omega) v hv) (16 * j + 28)) 5 =
        g1AlignedConfig (encodeG1 r).length (4 * preE.length + 3) (by
          exact lt_of_lt_of_le (by omega : 4 * preE.length + 3 <
            gnLocalSpan (encodeG1 r).length)
            (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
          (g1ListTape (restored.flatMap G1Frame.bits)) .bIns .p3 false false
          false (g1Ctx0.withVB v') := by
      rw [hP28eq]
      have h := g1CS_walk_probe_latch (encodeG1 r).length preE tailE v'
        (g1Ctx0.withVB v) (lt_of_lt_of_le hroomE
          (gnLocalSpan_le_g1_tapeLength (encodeG1 r).length))
      rw [hrestE] at h
      have hctx : (g1Ctx0.withVB v).withVB v' = g1Ctx0.withVB v' := rfl
      simpa [hpreC, hpreE, hctx] using h
    have hF : G1RunSafe
        (TM.runConfig (M := G1M)
          (TM.runConfig (M := G1M)
            (g1WalkConfig r j (by omega) (by omega) v hv)
            (16 * j + 28)) 5) 4 := by
      rw [hEeq]
      apply g1RunSafe_of_margins
      · simp [preE, preA, preC, skip]; omega
      · simpa only [g1AlignedConfig_head_val] using hspaceF
    exact G1RunSafe.add hE hF
  have hall := G1RunSafe.add hprefix hEF
  simpa using hall

set_option maxHeartbeats 200000

/-- Real-initial capstone: install and one successful round are safe and reach
the same `Σ(1)` as the existing exact schedules. -/
theorem g1CS_walk_one_round_trace_safe (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v v' : Bool) (hv : r.vals[0]? = some v) (hv' : r.vals[1]? = some v') :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r + 37) ∧
      TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1WalkInstallSteps r + 37) =
        g1WalkConfig r 1 (by omega) (g1PassB_length_pos_of_get hv') v' hv' := by
  have hinstall := g1CS_walk_install_runSafe r hc ht k h2 v hv
  have hexact := g1CS_walk_install_exact r hc ht k h2 v hv
  have hround0 := g1CS_walk_iteration_runSafe r 0 (by omega)
    (g1PassB_length_pos_of_get hv') v v' hv hv'
  have hround : G1RunSafe
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)) 37 := by
    apply G1RunSafe.transport hexact.symm
    simpa using hround0
  exact ⟨G1RunSafe.add hinstall hround, by
    rw [runConfig_add, hexact]
    exact g1CS_walk_iteration_exact r 0 (by omega)
      (g1PassB_length_pos_of_get hv') v v' hv hv'⟩

namespace G1PassBTraceProbes

/-- Concrete positive-B request witnessing that the real-initial capstone is
inhabited. -/
def reqAnd : G1Request := ⟨.and, 0, 1, [true, false]⟩

/-- A literal `and` request executes installation plus one safe B round and
reaches the exact `Σ(1)` endpoint. -/
theorem literal_one_round_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqAnd)))
        (g1WalkInstallSteps reqAnd + 37) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqAnd)))
          (g1WalkInstallSteps reqAnd + 37) =
        g1WalkConfig reqAnd 1 (by decide) (by decide) false (by decide) := by
  simpa [reqAnd] using
    g1CS_walk_one_round_trace_safe reqAnd (by decide) (Or.inl rfl)
      0 rfl true false rfl rfl

end G1PassBTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
