import Complexity.TMVerifier.TuringToolkit.GateOneScanner

/-!
# G1 exact execution: canonical validation and rewind to the pass-B handoff

**Progress classification: Infrastructure.**

The executable capstone of the T2a slice.  From the *real* initial
configuration `G1M.initialConfig (g1Point (encodeG1 r))` of the one fixed
machine, for a **canonical** request `r`, exactly
`2 * (encodeG1 r).length + 9` genuine `TM.runConfig` steps leave the machine at
head `0`, in the local `readBStart` handoff with frame position `p0`, all three
frame-buffer cells `false` and the context at `g1Ctx0`, with the tape
**exactly** the initial tape, cell for cell.  Nothing is packaged: the request
is otherwise arbitrary, the initial configuration is the compiled machine's
own, and the step count is a literal.

The `r.Canonical` hypothesis is not decoration.  `GateOneControl` proves the
forward table decides exactly the pure parser's language
(`g1Automaton_accepts_iff_decode`,
`g1CanonicalEncoderAutomatonTrace_iff`), so a *noncanonical* encoded request
ends the fixed `(encodeG1 r).length + 4`-step validation prefix in the literal
`reject` sink rather than the handoff, with the
tape unchanged (`g1CS_validate_noncanonical_reject_exact`,
`g1CS_noncanonical_ne_readB`).

The forward part is not a re-proof of the T1 scanner: it is the generic
`FrameScanner.scanFrames` instantiated at `g1FrameScanner`.  Only the
right-to-left rewind and the rejecting frame, which the kernel does not cover,
have their own step lemmas, each one a generic bridge corollary applied to one
standalone tuple lemma of `GateOneControl`.

**Scope.**  All execution statements are scoped to `encodeG1 r`; as in T1,
nothing is claimed about physically padded tapes — in particular the rejection
theorem is about the encoded word of a noncanonical request, not about an
arbitrary padded physical tape.  No acceptance, output-write, operand read or
`spec`-correctness claim is made, and `g1ReadBHandoffSteps_le_clock` records
only that the *proved prefix* fits the public clock — deliberately no
full-clock theorem, since `readBStart` is activated by the T2b layers.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private def g1Phase : Fin g1CS.toPhased.numPhases := g1CS.toPhased.startPhase

/-- Tape length of the compiled G1 machine. -/
theorem g1M_tapeLength (n : Nat) : G1M.tapeLength n = n + g1Clock n + 1 := rfl

private theorem g1_le_sq (m : Nat) : m + 1 ≤ (m + 1) ^ 2 := by
  have h2 : (m + 1) ^ 2 = (m + 1) * (m + 1) := by
    simp [Nat.pow_succ]
  rw [h2]
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos m)

/-- Every position the T2a trace visits is far inside the tape. -/
theorem g1_lt_tapeLength {n k : Nat} (h : k ≤ 2 * n + 12) :
    k < G1M.tapeLength n := by
  have hmul : 512 * (n + 1) ≤ 512 * (n + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (g1_le_sq n)
  rw [g1M_tapeLength, g1Clock]
  omega

/-! ## Aligned configurations -/

/-- A configuration in the G1 phase, at an explicit head position, with an
arbitrary tape and an arbitrary local state.  Only `Fin` bookkeeping. -/
def g1AlignedConfigQ (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (q : G1State) :
    Configuration (M := G1M) n where
  state := ⟨g1Phase, q⟩
  head := ⟨h, hh⟩
  tape := tape

/-- `g1AlignedConfigQ` with the control state spelled out componentwise. -/
def g1AlignedConfig (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode)
    (position := G1FramePosition.p0) (b0 := false) (b1 := false)
    (b2 := false) (ctx : G1Ctx := g1Ctx0) : Configuration (M := G1M) n :=
  g1AlignedConfigQ n h hh tape (g1State mode position b0 b1 b2 ctx)

@[simp] theorem g1AlignedConfig_state (n h hh tape mode position b0 b1 b2 ctx) :
    (g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx).state =
      ⟨g1Phase, g1State mode position b0 b1 b2 ctx⟩ := rfl

@[simp] theorem g1AlignedConfig_head_val
    (n h hh tape mode position b0 b1 b2 ctx) :
    ((g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx).head : Nat) = h :=
  rfl

@[simp] theorem g1AlignedConfig_tape (n h hh tape mode position b0 b1 b2 ctx) :
    (g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx).tape = tape := rfl

/-- The kernel's frame-aligned configuration *is* the componentwise one. -/
theorem g1AlignedFrame_eq (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (ctx : G1Ctx) :
    g1FrameScanner.alignedFrame n h hh tape mode ctx =
      g1AlignedConfig n h hh tape mode .p0 false false false ctx := rfl

/-! ## The two step adapters the rewind needs

Each is the matching generic kernel adapter, which is itself the matching
generic bridge corollary.  `g1Transition` is never unfolded. -/

theorem g1CS_aligned_step_left (n h : Nat) (hh : h < G1M.tapeLength n)
    (hpos : 0 < h) (tape : Fin (G1M.tapeLength n) → Bool) (q q' : G1State)
    (w : Bool)
    (htr : ∀ phase : Fin 1,
      g1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, Move.left)) :
    TM.stepConfig (M := G1M) (g1AlignedConfigQ n h hh tape q) =
      g1AlignedConfigQ n (h - 1) (by omega) (writeCell h w tape) q' :=
  g1FrameScanner.alignedStepLeft n h hh hpos tape q q' w (htr 0)

theorem g1CS_aligned_step_stay (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (q q' : G1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      g1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, Move.stay)) :
    TM.stepConfig (M := G1M) (g1AlignedConfigQ n h hh tape q) =
      g1AlignedConfigQ n h hh (writeCell h w tape) q' :=
  g1FrameScanner.alignedStepStay n h hh tape q q' w (htr 0)

/-! ## The canonical validation scan -/

/-- The list-backed tape of the G1 machine. -/
abbrev g1ListTape {n : Nat} (bits : List Bool) :
    Fin (G1M.tapeLength n) → Bool := frameListTape bits

/-- The canonical word plus the explicit blank frame that marks end of input.
This is exactly the frame list the read-only pass consumes. -/
def g1ValidationFrames (r : G1Request) : List G1Frame :=
  encodeG1Frames r ++ [.blank]

@[simp] theorem g1ValidationFrames_length (r : G1Request) :
    (g1ValidationFrames r).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp [g1ValidationFrames]

/-- **The canonical validation scan is a complete valid path.**  Immediate from
the frame-level grammar correspondence of `GateOneControl`: a canonical request
is accepted, and every accepted word is a valid path. -/
theorem g1ValidationPath (r : G1Request) (hc : r.Canonical) :
    g1FrameScanner.ValidPath .vBof (g1ValidationFrames r) :=
  (g1FrameScanner_validPath .vBof (g1ValidationFrames r)).mpr
    (g1ValidPath_of_accepts (mode := .vBof) trivial (g1AdvanceList_encode r hc))

/-- **The canonical validation scan ends at `rewindStart`.** -/
theorem g1ValidationAdvance (r : G1Request) (hc : r.Canonical) :
    g1FrameScanner.advanceList .vBof (g1ValidationFrames r) = .rewindStart := by
  rw [g1FrameScanner_advanceList]
  exact g1AdvanceList_encode r hc

/-- **A noncanonical request's validation scan ends in the `reject` sink.**  The
frame-level converse of `g1ValidationAdvance`. -/
theorem g1ValidationAdvance_reject_of_not_canonical (r : G1Request)
    (hc : ¬ r.Canonical) :
    g1FrameScanner.advanceList .vBof (g1ValidationFrames r) = .reject := by
  rw [g1FrameScanner_advanceList]
  exact g1AdvanceList_encode_reject r hc

/-- **Encoder/automaton trace.**  The canonical frames plus the explicit blank
frame form a complete valid path of the forward control, ending at
`rewindStart`.  By `g1CanonicalEncoderAutomatonTrace_iff` the `Canonical`
hypothesis is also necessary, so this really is the machine deciding the pure
canonical grammar. -/
theorem g1CanonicalEncoderAutomatonTrace (r : G1Request) (hc : r.Canonical) :
    g1FrameScanner.ValidPath .vBof (encodeG1Frames r ++ [.blank]) ∧
      g1FrameScanner.advanceList .vBof (encodeG1Frames r ++ [.blank]) =
        .rewindStart :=
  ⟨g1ValidationPath r hc, g1ValidationAdvance r hc⟩

/-- **Encoder equivalence at the scanner.**  The kernel-level forward run of a
request's canonical frame word plus the end-of-input frame reaches
`rewindStart` exactly when the request is canonical. -/
theorem g1FrameScanner_encode_iff_canonical (r : G1Request) :
    g1FrameScanner.advanceList .vBof (encodeG1Frames r ++ [.blank]) =
        .rewindStart ↔ r.Canonical := by
  rw [g1FrameScanner_advanceList]
  exact g1CanonicalEncoderAutomatonTrace_iff r

private theorem g1_getD_blank_bits (k : Nat) :
    (G1Frame.blank.bits[k]?).getD false = false := by
  match k with
  | 0 | 1 | 2 | 3 => rfl
  | (k + 4) => rfl

private theorem g1_getD_append_blank (bits : List Bool) (i : Nat) :
    (bits ++ G1Frame.blank.bits).getD i false =
      if h : i < bits.length then bits.get ⟨i, h⟩ else false := by
  by_cases h : i < bits.length
  · rw [dif_pos h]
    simp only [List.getD, List.getElem?_append_left h]
    simp [List.get_eq_getElem, List.getElem?_eq_getElem h]
  · rw [dif_neg h]
    simp only [List.getD, List.getElem?_append_right (by omega : bits.length ≤ i)]
    exact g1_getD_blank_bits _

/-- The validation tape (canonical word plus one blank frame) is literally the
machine's initial tape.  This is where the binary-tape end-of-input ambiguity
is discharged. -/
theorem g1ListTape_validation_eq_initial (r : G1Request) :
    g1ListTape (n := (encodeG1 r).length)
        ((g1ValidationFrames r).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  funext i
  have hflat : (g1ValidationFrames r).flatMap G1Frame.bits =
      encodeG1 r ++ G1Frame.blank.bits := by
    simp [g1ValidationFrames, encodeG1, List.flatMap_append]
  show ((g1ValidationFrames r).flatMap G1Frame.bits).getD i.val false = _
  rw [hflat, g1_getD_append_blank]
  rfl

/-- **Exact validation.**  Every canonical request passes the complete
grammar plus one blank frame in exactly `(encodeG1 r).length + 4` genuine TM
steps, read-only: the machine ends at `rewindStart` with the whole tape still
the initial tape.  The scan itself is the generic kernel's. -/
theorem g1CS_validate_encoded_exact (r : G1Request) (hc : r.Canonical) :
    let n := (encodeG1 r).length
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r))) (n + 4) =
      g1AlignedConfig n (n + 4) (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape .rewindStart := by
  dsimp
  have hframes : 4 * (g1ValidationFrames r).length =
      (encodeG1 r).length + 4 := by
    simp [g1ValidationFrames, encodeG1_length]; omega
  have hsafe : 4 * (0 + (g1ValidationFrames r).length) <
      G1M.tapeLength (encodeG1 r).length := by
    rw [Nat.zero_add, hframes]; exact g1_lt_tapeLength (by omega)
  have hscan := g1FrameScanner_scanFrames (encodeG1 r).length []
    (g1ValidationFrames r) [] .vBof g1Ctx0 (g1ValidationPath r hc) (by
      simpa using hsafe)
  simp only [List.nil_append, List.append_nil, List.length_nil, zero_add,
    Nat.mul_zero, g1ValidationAdvance r hc, g1AlignedFrame_eq, hframes,
    g1ListTape_validation_eq_initial] at hscan
  exact hscan

/-! ## Exact rewind to head zero -/

private theorem g1CS_step_rewind_p3 (n h : Nat) (hpos : 0 < h)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    TM.stepConfig (M := G1M)
        (g1AlignedConfig n h hh tape .rewind .p3 false false false ctx) =
      g1AlignedConfig n (h - 1) (by omega) tape .rewind .p2 false false
        (tape ⟨h, hh⟩) ctx := by
  have hstep := g1CS_aligned_step_left n h hh hpos tape
    (g1State .rewind .p3 false false false ctx)
    (g1State .rewind .p2 false false (tape ⟨h, hh⟩) ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_rewind_p3 phase false false false _ ctx)
  rwa [writeCell_self] at hstep

private theorem g1CS_step_rewind_p2 (n h : Nat) (hpos : 0 < h)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b2 : Bool) (ctx : G1Ctx) :
    TM.stepConfig (M := G1M)
        (g1AlignedConfig n h hh tape .rewind .p2 false false b2 ctx) =
      g1AlignedConfig n (h - 1) (by omega) tape .rewind .p1 false
        (tape ⟨h, hh⟩) b2 ctx := by
  have hstep := g1CS_aligned_step_left n h hh hpos tape
    (g1State .rewind .p2 false false b2 ctx)
    (g1State .rewind .p1 false (tape ⟨h, hh⟩) b2 ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_rewind_p2 phase false false b2 _ ctx)
  rwa [writeCell_self] at hstep

private theorem g1CS_step_rewind_p1 (n h : Nat) (hpos : 0 < h)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b1 b2 : Bool) (ctx : G1Ctx) :
    TM.stepConfig (M := G1M)
        (g1AlignedConfig n h hh tape .rewind .p1 false b1 b2 ctx) =
      g1AlignedConfig n (h - 1) (by omega) tape .rewind .p0
        (tape ⟨h, hh⟩) b1 b2 ctx := by
  have hstep := g1CS_aligned_step_left n h hh hpos tape
    (g1State .rewind .p1 false b1 b2 ctx)
    (g1State .rewind .p0 (tape ⟨h, hh⟩) b1 b2 ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_rewind_p1 phase false b1 b2 _ ctx)
  rwa [writeCell_self] at hstep

private theorem g1CS_step_rewind_p0_other (n h : Nat) (hpos : 0 < h)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b0 b1 b2 : Bool) (ctx : G1Ctx)
    (hne : decodeG1Frame? [tape ⟨h, hh⟩, b0, b1, b2] ≠ some .bof) :
    TM.stepConfig (M := G1M)
        (g1AlignedConfig n h hh tape .rewind .p0 b0 b1 b2 ctx) =
      g1AlignedConfig n (h - 1) (by omega) tape .rewind .p3 false false false
        ctx := by
  have hstep := g1CS_aligned_step_left n h hh hpos tape
    (g1State .rewind .p0 b0 b1 b2 ctx)
    (g1State .rewind .p3 false false false ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_rewind_p0_other phase b0 b1 b2 _ ctx hne)
  rwa [writeCell_self] at hstep

private theorem g1CS_step_rewind_p0_bof (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b0 b1 b2 : Bool) (ctx : G1Ctx)
    (heq : decodeG1Frame? [tape ⟨h, hh⟩, b0, b1, b2] = some .bof) :
    TM.stepConfig (M := G1M)
        (g1AlignedConfig n h hh tape .rewind .p0 b0 b1 b2 ctx) =
      g1AlignedConfig n h hh tape .readBStart .p0 false false false ctx := by
  have hstep := g1CS_aligned_step_stay n h hh tape
    (g1State .rewind .p0 b0 b1 b2 ctx) (g1ReadBState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_rewind_p0_bof phase b0 b1 b2 _ ctx heq)
  rwa [writeCell_self] at hstep

/-- Reverse-decode one non-anchor frame in exactly four physical steps. -/
private theorem g1CS_rewind_frame_other (n base : Nat) (hbase : 0 < base)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (frame : G1Frame)
    (hne : frame ≠ .bof) (ctx : G1Ctx)
    (hbits : physicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .rewind .p3 false false
          false ctx) 4 =
      g1AlignedConfig n (base - 1) (by omega) tape .rewind .p3 false false
        false ctx := by
  change TM.runConfig (M := G1M)
      (g1AlignedConfig n (base + 3) (by omega) tape .rewind .p3 false false
        false ctx) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have hs1 : TM.stepConfig (M := G1M)
      (g1AlignedConfig n (base + 3) (by omega) tape .rewind .p3 false false
        false ctx) =
      g1AlignedConfig n (base + 2) (by omega) tape .rewind .p2 false false
        (tape ⟨base + 3, by omega⟩) ctx :=
    g1CS_step_rewind_p3 n (base + 3) (by omega) (by omega) tape ctx
  have hs2 : TM.stepConfig (M := G1M)
      (g1AlignedConfig n (base + 2) (by omega) tape .rewind .p2 false false
        (tape ⟨base + 3, by omega⟩) ctx) =
      g1AlignedConfig n (base + 1) (by omega) tape .rewind .p1 false
        (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩) ctx :=
    g1CS_step_rewind_p2 n (base + 2) (by omega) (by omega) tape
      (tape ⟨base + 3, by omega⟩) ctx
  have hs3 : TM.stepConfig (M := G1M)
      (g1AlignedConfig n (base + 1) (by omega) tape .rewind .p1 false
        (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩) ctx) =
      g1AlignedConfig n base (by omega) tape .rewind .p0
        (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
        (tape ⟨base + 3, by omega⟩) ctx :=
    g1CS_step_rewind_p1 n (base + 1) (by omega) (by omega) tape
      (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩) ctx
  rw [hs1, hs2, hs3]
  apply g1CS_step_rewind_p0_other
  · omega
  · simp only [physicalBitsAt] at hbits
    have hdecode : decodeG1Frame? [tape ⟨base, by omega⟩,
        tape ⟨base + 1, by omega⟩, tape ⟨base + 2, by omega⟩,
        tape ⟨base + 3, by omega⟩] = some frame := by
      rw [hbits]; exact decodeG1Frame_bits frame
    simpa [hdecode] using hne

/-- Reverse-decode the left anchor and enter the pass-B handoff at head 0. -/
private theorem g1CS_rewind_bof (n : Nat) (hsafe : 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx)
    (hbits : physicalBitsAt (h := 0) hsafe tape = G1Frame.bof.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 3 (by omega) tape .rewind .p3 false false false ctx)
        4 =
      g1AlignedConfig n 0 (by omega) tape .readBStart .p0 false false false
        ctx := by
  change TM.runConfig (M := G1M)
      (g1AlignedConfig n 3 (by omega) tape .rewind .p3 false false false ctx)
      (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [g1CS_step_rewind_p3 n 3 (by omega) (by omega) tape ctx]
  rw [g1CS_step_rewind_p2 n 2 (by omega) (by omega) tape
    (tape ⟨3, by omega⟩) ctx]
  rw [g1CS_step_rewind_p1 n 1 (by omega) (by omega) tape
    (tape ⟨2, by omega⟩) (tape ⟨3, by omega⟩) ctx]
  apply g1CS_step_rewind_p0_bof
  simp only [physicalBitsAt] at hbits
  rw [hbits]
  rfl

private theorem g1CS_step_rewindStart (n h : Nat) (hpos : 0 < h)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .rewindStart .p0 false false false ctx)
        1 =
      g1AlignedConfig n (h - 1) (by omega) tape .rewind .p3 false false false
        ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_left n h hh hpos tape
    (g1State .rewindStart .p0 false false false ctx)
    (g1State .rewind .p3 false false false ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_rewindStart phase .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-- **Exact reverse scan.**  Rewind right-to-left across a list of non-anchor
frames in exactly four TM steps per frame, preserving the complete
list-backed tape, and finishing on the last cell of the leading anchor. -/
theorem g1CS_rewind_tail (n : Nat) (tail suffix : List G1Frame) (ctx : G1Ctx)
    (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
          .rewind .p3 false false false ctx) (4 * tail.length) =
      g1AlignedConfig n 3 (by omega)
        (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
        .rewind .p3 false false false ctx := by
  induction tail using List.reverseRecOn generalizing suffix with
  | nil => simp
  | append_singleton rest frame ih =>
      have hframeNe : frame ≠ .bof := hne frame (by simp)
      have hrestNe : ∀ f ∈ rest, f ≠ .bof := fun f hf => hne f (by simp [hf])
      have hframeSafe : 4 * (1 + rest.length) + 4 < G1M.tapeLength n := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hsafe
        omega
      have hframeBits : physicalBitsAt hframeSafe
          (g1ListTape (n := n)
            ((.bof :: (rest ++ [frame]) ++ suffix).flatMap G1Frame.bits)) =
          frame.bits := by
        have raw := physicalBitsAt_flatMap (L := G1M.tapeLength n) g1FrameCodec
          (.bof :: rest) suffix frame (by simpa [Nat.add_comm] using hframeSafe)
        convert raw using 1
        all_goals simp [List.append_assoc, Nat.add_comm]
      have hframe := g1CS_rewind_frame_other n (4 * (1 + rest.length))
        (by omega) hframeSafe
        (g1ListTape ((.bof :: (rest ++ [frame]) ++ suffix).flatMap G1Frame.bits))
        frame hframeNe ctx hframeBits
      have hframe' : TM.runConfig (M := G1M)
          (g1AlignedConfig n (4 * (1 + (rest ++ [frame]).length) - 1)
            (by omega)
            (g1ListTape
              ((.bof :: (rest ++ [frame]) ++ suffix).flatMap G1Frame.bits))
            .rewind .p3 false false false ctx) 4 =
          g1AlignedConfig n (4 * (1 + rest.length) - 1) (by omega)
            (g1ListTape
              ((.bof :: (rest ++ [frame]) ++ suffix).flatMap G1Frame.bits))
            .rewind .p3 false false false ctx := by
        simpa [List.length_append, Nat.mul_add] using hframe
      rw [show 4 * (rest ++ [frame]).length = 4 + 4 * rest.length by
        simp; omega, runConfig_add, hframe']
      have hrestSafe : 4 * (1 + rest.length) < G1M.tapeLength n := by omega
      have htail := ih (frame :: suffix) hrestNe hrestSafe
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htail

/-! ## The capstone -/

/-- The exact number of genuine TM steps of the T2a prefix. -/
def g1ReadBHandoffSteps (r : G1Request) : Nat := 2 * (encodeG1 r).length + 9

/-- The proved prefix fits inside the public clock.  This is a budget fact
about the *proved* prefix only; no full-clock theorem is claimed, because
`readBStart` is activated by the T2b layers. -/
theorem g1ReadBHandoffSteps_le_clock (r : G1Request) :
    g1ReadBHandoffSteps r ≤ g1Clock (encodeG1 r).length := by
  have hmul : 512 * ((encodeG1 r).length + 1) ≤
      512 * ((encodeG1 r).length + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (g1_le_sq (encodeG1 r).length)
  simp only [g1ReadBHandoffSteps, g1Clock]
  omega

set_option maxHeartbeats 1000000 in
/-- **T2a executable capstone.**  From the real initial configuration of the
one fixed zero-parameter machine, exactly `2 * (encodeG1 r).length + 9`
genuine `TM.runConfig` steps validate the canonical grammar and rewind, ending
at head `0` in the local `readBStart` handoff with frame position `p0`, all
three frame-buffer cells `false`, the context at `g1Ctx0`, and the tape
exactly the initial tape. -/
theorem g1CS_validate_rewind_readB_exact (r : G1Request) (hc : r.Canonical) :
    let n := (encodeG1 r).length
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r) =
      g1AlignedConfig n 0 (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readBStart .p0 false false false g1Ctx0 := by
  dsimp
  have hlen : 4 * (1 + (g1ValidationFrames r).tail.length) =
      (encodeG1 r).length + 4 := by
    rcases r with ⟨tag, arg1, arg2, vals⟩
    simp [g1ValidationFrames, encodeG1Frames, encodeG1_length]
    omega
  rw [show g1ReadBHandoffSteps r =
      ((encodeG1 r).length + 4) + 1 + 4 * (g1ValidationFrames r).length by
        simp [g1ReadBHandoffSteps, g1ValidationFrames, encodeG1_length]; omega,
    runConfig_add, runConfig_add, g1CS_validate_encoded_exact r hc]
  rw [g1CS_step_rewindStart (encodeG1 r).length ((encodeG1 r).length + 4)
    (by omega) (g1_lt_tapeLength (by omega))]
  have hne : ∀ f ∈ (g1ValidationFrames r).tail, f ≠ G1Frame.bof := by
    intro f hf heq
    subst f
    rcases r with ⟨tag, arg1, arg2, vals⟩
    simp [g1ValidationFrames, encodeG1Frames] at hf
  have hsafe : 4 * (1 + (g1ValidationFrames r).tail.length) <
      G1M.tapeLength (encodeG1 r).length := by
    rw [hlen]; exact g1_lt_tapeLength (by omega)
  have htail := g1CS_rewind_tail (encodeG1 r).length
    (g1ValidationFrames r).tail [] g1Ctx0 hne hsafe
  have htape : g1ListTape (n := (encodeG1 r).length)
      ((G1Frame.bof :: (g1ValidationFrames r).tail ++ []).flatMap
        G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [← g1ListTape_validation_eq_initial r]
    rcases r with ⟨tag, arg1, arg2, vals⟩
    simp [g1ValidationFrames, encodeG1Frames]
  rw [htape] at htail
  rw [show 4 * (g1ValidationFrames r).length =
      4 * (g1ValidationFrames r).tail.length + 4 by
        rcases r with ⟨tag, arg1, arg2, vals⟩
        simp [g1ValidationFrames, encodeG1Frames]
        omega,
    runConfig_add]
  have htail' : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length ((encodeG1 r).length + 4 - 1)
        (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .rewind .p3 false false false g1Ctx0)
      (4 * (g1ValidationFrames r).tail.length) =
      g1AlignedConfig (encodeG1 r).length 3 (g1_lt_tapeLength (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .rewind .p3 false false false g1Ctx0 := by
    simpa only [hlen] using htail
  rw [htail']
  have hbofSafe : 4 < G1M.tapeLength (encodeG1 r).length :=
    g1_lt_tapeLength (by omega)
  have hbof := g1CS_rewind_bof (encodeG1 r).length hbofSafe
    (G1M.initialConfig (g1Point (encodeG1 r))).tape g1Ctx0 (by
      rw [← g1ListTape_validation_eq_initial r]
      have raw := physicalBitsAt_flatMap (L := G1M.tapeLength (encodeG1 r).length)
        g1FrameCodec [] (g1ValidationFrames r).tail .bof (by simpa using hbofSafe)
      simpa [g1ValidationFrames, encodeG1Frames] using raw)
  exact hbof

/-! ## The three components of the capstone, separately -/

theorem g1CS_readB_head (r : G1Request) (hc : r.Canonical) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).head : Nat) = 0 := by
  rw [g1CS_validate_rewind_readB_exact r hc]; rfl

/-- The capstone remains in the machine's unique public start phase. -/
theorem g1CS_readB_phase (r : G1Request) (hc : r.Canonical) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).state.fst = g1CS.toPhased.startPhase := by
  rw [g1CS_validate_rewind_readB_exact r hc]
  rfl

theorem g1CS_readB_state (r : G1Request) (hc : r.Canonical) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).state.snd =
      g1State .readBStart .p0 false false false g1Ctx0 := by
  rw [g1CS_validate_rewind_readB_exact r hc]; rfl

/-- **Read-only.**  The T2a prefix does not change a single tape cell. -/
theorem g1CS_readB_tape (r : G1Request) (hc : r.Canonical) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_validate_rewind_readB_exact r hc]; rfl

/-! ## Exact rejection of a noncanonical encoded request

The converse half of the capstone.  The frame-level grammar correspondence of
`GateOneControl` says a noncanonical encoded word drives the forward control
into the `reject` sink; the three lemmas below turn that into a genuine
`TM.runConfig` statement from the *real* initial configuration, over the same
fixed `(encodeG1 r).length + 4`-step validation prefix as
`g1CS_validate_encoded_exact`.

The head is deliberately not pinned: it stops wherever the offending frame is.
Nothing is claimed here about arbitrary padded physical tapes — only about the
canonical encoding of a noncanonical request. -/

theorem g1CS_aligned_step_right (n h : Nat) (hh : h < G1M.tapeLength n)
    (hb : h + 1 < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (q q' : G1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      g1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, Move.right)) :
    TM.stepConfig (M := G1M) (g1AlignedConfigQ n h hh tape q) =
      g1AlignedConfigQ n (h + 1) hb (writeCell h w tape) q' :=
  g1FrameScanner.alignedStepRight n h hh hb tape q q' w (htr 0)

private theorem g1CS_step_reject_sink (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) :
    TM.stepConfig (M := G1M) (g1AlignedConfigQ n h hh tape g1RejectState) =
      g1AlignedConfigQ n h hh tape g1RejectState := by
  have hstep := g1CS_aligned_step_stay n h hh tape g1RejectState g1RejectState
    (tape ⟨h, hh⟩) (fun phase => g1Transition_reject_sink phase (tape ⟨h, hh⟩))
  rwa [writeCell_self] at hstep

/-- **The `reject` sink is stable for the whole remaining budget.** -/
theorem g1CS_runConfig_reject_sink (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (k : Nat) :
    TM.runConfig (M := G1M) (g1AlignedConfigQ n h hh tape g1RejectState) k =
      g1AlignedConfigQ n h hh tape g1RejectState := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show k + 1 = 1 + k from Nat.add_comm k 1, runConfig_add, runConfig_one,
        g1CS_step_reject_sink]
      exact ih

/-- **The rejecting frame, exactly.**  Reading a frame whose completion is
`reject` takes four physical steps: three to buffer the cells, one to enter the
sink without moving.  The tape is untouched. -/
private theorem g1CS_frame_reject (n h : Nat) (hsafe : h + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode)
    (hmode : G1ForwardMode mode) (frame : G1Frame) (ctx : G1Ctx)
    (hnext : g1Advance mode frame = .reject)
    (hbits : physicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := G1M)
        (g1FrameScanner.alignedFrame n h
          (by show h < G1M.tapeLength n; omega) tape mode ctx) 4 =
      g1AlignedConfigQ n (h + 3) (by omega) tape g1RejectState := by
  have hcomplete : g1Complete mode (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
      (tape ⟨h + 2, by omega⟩) (tape ⟨h + 3, by omega⟩) = .reject := by
    have hcb := g1FrameScanner.complete_of_bits mode frame
      (b0 := tape ⟨h, by omega⟩) (b1 := tape ⟨h + 1, by omega⟩)
      (b2 := tape ⟨h + 2, by omega⟩) (b3 := tape ⟨h + 3, by omega⟩)
      (by simpa [physicalBitsAt] using hbits)
    exact hcb.trans hnext
  show TM.runConfig (M := G1M)
      (g1AlignedConfigQ n h (by omega) tape
        (g1State mode .p0 false false false ctx)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have hs0 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n h (by omega) tape
        (g1State mode .p0 false false false ctx)) =
      g1AlignedConfigQ n (h + 1) (by omega) tape
        (g1State mode .p1 (tape ⟨h, by omega⟩) false false ctx) := by
    have hstep := g1CS_aligned_step_right n h (by omega) (by omega) tape
      (g1State mode .p0 false false false ctx)
      (g1State mode .p1 (tape ⟨h, by omega⟩) false false ctx)
      (tape ⟨h, by omega⟩)
      (fun phase => g1Transition_forward_p0 hmode phase false false false _ ctx)
    rwa [writeCell_self] at hstep
  have hs1 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n (h + 1) (by omega) tape
        (g1State mode .p1 (tape ⟨h, by omega⟩) false false ctx)) =
      g1AlignedConfigQ n (h + 2) (by omega) tape
        (g1State mode .p2 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩) false
          ctx) := by
    have hstep := g1CS_aligned_step_right n (h + 1) (by omega) (by omega) tape
      (g1State mode .p1 (tape ⟨h, by omega⟩) false false ctx)
      (g1State mode .p2 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩) false ctx)
      (tape ⟨h + 1, by omega⟩)
      (fun phase => g1Transition_forward_p1 hmode phase _ false false _ ctx)
    rwa [writeCell_self] at hstep
  have hs2 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n (h + 2) (by omega) tape
        (g1State mode .p2 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩) false
          ctx)) =
      g1AlignedConfigQ n (h + 3) (by omega) tape
        (g1State mode .p3 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
          (tape ⟨h + 2, by omega⟩) ctx) := by
    have hstep := g1CS_aligned_step_right n (h + 2) (by omega) (by omega) tape
      (g1State mode .p2 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩) false ctx)
      (g1State mode .p3 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
        (tape ⟨h + 2, by omega⟩) ctx)
      (tape ⟨h + 2, by omega⟩)
      (fun phase => g1Transition_forward_p2 hmode phase _ _ false _ ctx)
    rwa [writeCell_self] at hstep
  have hs3 : TM.stepConfig (M := G1M)
      (g1AlignedConfigQ n (h + 3) (by omega) tape
        (g1State mode .p3 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
          (tape ⟨h + 2, by omega⟩) ctx)) =
      g1AlignedConfigQ n (h + 3) (by omega) tape g1RejectState := by
    have hstep := g1CS_aligned_step_stay n (h + 3) (by omega) tape
      (g1State mode .p3 (tape ⟨h, by omega⟩) (tape ⟨h + 1, by omega⟩)
        (tape ⟨h + 2, by omega⟩) ctx)
      g1RejectState (tape ⟨h + 3, by omega⟩)
      (fun phase => g1Transition_forward_p3_reject hmode phase _ _ _ _ ctx
        hcomplete)
    rwa [writeCell_self] at hstep
  rw [hs0, hs1, hs2, hs3]

/-- **Exact rejecting scan.**  A rejecting frame path is consumed in exactly
four TM steps per frame, ending in the literal `reject` sink with the complete
list-backed tape preserved. -/
theorem g1CS_scan_reject (n : Nat) (pre frames suffix : List G1Frame)
    (mode : G1Mode) (ctx : G1Ctx) (hpath : G1RejectPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < G1M.tapeLength n) :
    ∃ (h : Nat) (hh : h < G1M.tapeLength n),
      TM.runConfig (M := G1M)
          (g1FrameScanner.alignedFrame n (4 * pre.length)
            (by show 4 * pre.length < G1M.tapeLength n; omega)
            (g1ListTape ((pre ++ frames ++ suffix).flatMap G1Frame.bits))
            mode ctx)
          (4 * frames.length) =
        g1AlignedConfigQ n h hh
          (g1ListTape ((pre ++ frames ++ suffix).flatMap G1Frame.bits))
          g1RejectState := by
  induction frames generalizing pre mode with
  | nil => exact hpath.elim
  | cons frame rest ih =>
      obtain ⟨hmode, hcase⟩ := hpath
      have hframeSafe : 4 * pre.length + 4 < G1M.tapeLength n := by
        simp only [List.length_cons] at hsafe
        omega
      have hbits : physicalBitsAt hframeSafe
          (g1ListTape (n := n)
            ((pre ++ frame :: rest ++ suffix).flatMap G1Frame.bits)) =
          frame.bits := by
        simpa [List.append_assoc] using
          physicalBitsAt_flatMap (L := G1M.tapeLength n) g1FrameCodec pre
            (rest ++ suffix) frame hframeSafe
      rcases hcase with hr | hr
      · refine ⟨4 * pre.length + 3, by omega, ?_⟩
        rw [show 4 * (frame :: rest).length = 4 + 4 * rest.length by
            simp; omega,
          runConfig_add,
          g1CS_frame_reject n (4 * pre.length) hframeSafe _ mode hmode frame ctx
            hr hbits,
          g1CS_runConfig_reject_sink]
      · have hnext : g1Advance mode frame ≠ .reject := by
          intro hz
          exact G1ForwardMode.not_reject (hz ▸ hr.forward)
        have hmacro := g1FrameScanner_frameMacrostep n (4 * pre.length)
          hframeSafe
          (g1ListTape ((pre ++ frame :: rest ++ suffix).flatMap G1Frame.bits))
          mode frame ctx hmode hnext hbits
        have hsafeTail :
            4 * ((pre ++ [frame]).length + rest.length) < G1M.tapeLength n := by
          simp only [List.length_cons, List.length_append, List.length_nil]
            at hsafe ⊢
          omega
        obtain ⟨h', hh', htail⟩ := ih (pre ++ [frame]) (g1Advance mode frame)
          hr hsafeTail
        refine ⟨h', hh', ?_⟩
        rw [show 4 * (frame :: rest).length = 4 + 4 * rest.length by
            simp; omega,
          runConfig_add, hmacro]
        simpa [List.length_append, List.length_nil, List.length_cons,
          List.singleton_append, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- **Exact noncanonical rejection.**  From the real initial configuration of
the one fixed machine, the *same* fixed `(encodeG1 r).length + 4`-step
validation prefix that accepts a canonical request drives a noncanonical one
into the literal `g1RejectState`, leaving the tape exactly unchanged. -/
theorem g1CS_validate_noncanonical_reject_exact (r : G1Request)
    (hc : ¬ r.Canonical) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).state.snd = g1RejectState ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  have hframes : 4 * (g1ValidationFrames r).length =
      (encodeG1 r).length + 4 := by
    simp [g1ValidationFrames, encodeG1_length]; omega
  have hsafe : 4 * (0 + (g1ValidationFrames r).length) <
      G1M.tapeLength (encodeG1 r).length := by
    rw [Nat.zero_add, hframes]; exact g1_lt_tapeLength (by omega)
  obtain ⟨h, hh, hrun⟩ := g1CS_scan_reject (encodeG1 r).length []
    (g1ValidationFrames r) [] .vBof g1Ctx0 (g1RejectPath_encode r hc)
    (by simpa using hsafe)
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.mul_zero,
    g1AlignedFrame_eq, hframes, g1ListTape_validation_eq_initial] at hrun
  have hrun' : TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4) =
      g1AlignedConfigQ (encodeG1 r).length h hh
        (G1M.initialConfig (g1Point (encodeG1 r))).tape g1RejectState := hrun
  rw [hrun']
  exact ⟨rfl, rfl⟩

/-- **At the end of the validation prefix, a noncanonical encoded request is
not at the pass-B handoff.**  The context is universally quantified, so the
excluded endpoint covers the handoff state in any context. -/
theorem g1CS_noncanonical_ne_readB (r : G1Request) (hc : ¬ r.Canonical)
    (ctx : G1Ctx) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        ((encodeG1 r).length + 4)).state.snd ≠ g1ReadBState ctx := by
  rw [(g1CS_validate_noncanonical_reject_exact r hc).1]
  exact g1RejectState_ne_readB ctx

end Pnp3.Internal.PsubsetPpoly.TM
