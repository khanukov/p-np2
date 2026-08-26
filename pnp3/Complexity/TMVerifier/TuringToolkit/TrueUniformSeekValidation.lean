import Complexity.TMVerifier.TuringToolkit.TrueUniformSeek
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridge

/-!
# Generic T1 execution theorems: read-only validation and rewind

The results here are genuine `TM.runConfig` traces of the compiled machine,
not statements about a separate pure interpreter.  They establish the four-bit
forward macrostep, stable terminal sinks, the two idle T1c boundary states,
and the exact read-only validation/rewind trace for every canonical request.
Every trace is finite-prefix: no full-clock `TM.run` statement about T1
survives in this slice, because `startMutation` is no longer idle.

**Proof discipline.**  Every `TM.stepConfig` fact in this module is obtained
by applying a corollary of the generic `ConstStatePhasedStepBridge` to a
standalone transition-table lemma of `TrueUniformSeek`; the dependent
mutation-execution slice is required to keep the same discipline.  The three
public `t1CS_aligned_step_*` adapters below are the primary reuse surface, and
the small internal stability proof applies the generic `stay` corollary
directly.  `t1Transition` is never unfolded inside a `stepConfig` proof.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- The concrete T1 machine used by the execution-theorem surface. -/
abbrev T1M := t1CS.toPhased.toTM

private def t1Phase : Fin t1CS.toPhased.numPhases := t1CS.toPhased.startPhase

@[simp] private theorem T1M_step (s : T1State) (scan : Bool) :
    T1M.step ⟨t1Phase, s⟩ scan =
      let r := t1Transition 0 s scan
      (⟨r.1, r.2.1⟩, r.2.2.1, r.2.2.2) := rfl

/-- A configuration with arbitrary tape, an aligned control state, and an
explicit physical head position.  This constructor only packages `Fin`
bookkeeping. -/
def t1AlignedConfigQ (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q : T1State) :
    Configuration (M := T1M) n where
  state := ⟨t1Phase, q⟩
  head := ⟨h, hh⟩
  tape := tape

/-- `t1AlignedConfigQ` with the control state spelled out componentwise. -/
def t1AlignedConfig (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (mode : T1Mode)
    (position := T1FramePosition.p0) (b0 := false) (b1 := false)
    (b2 := false) (latch := false) : Configuration (M := T1M) n :=
  t1AlignedConfigQ n h hh tape (t1State mode position b0 b1 b2 latch)

@[simp] theorem t1AlignedConfig_state
    (n h hh tape mode position b0 b1 b2 latch) :
    (t1AlignedConfig n h hh tape mode position b0 b1 b2 latch).state =
      ⟨t1Phase, t1State mode position b0 b1 b2 latch⟩ := rfl

@[simp] theorem t1AlignedConfig_head_val
    (n h hh tape mode position b0 b1 b2 latch) :
    ((t1AlignedConfig n h hh tape mode position b0 b1 b2 latch).head : Nat) =
      h := rfl

@[simp] theorem t1AlignedConfig_tape
    (n h hh tape mode position b0 b1 b2 latch) :
    (t1AlignedConfig n h hh tape mode position b0 b1 b2 latch).tape = tape := rfl

/-! ## The three T1 step adapters

Each adapter turns one standalone transition-table equation into one exact
`TM.stepConfig` equation on aligned configurations, by applying the matching
generic bridge corollary.  The table equation is quantified over the phase so
that it instantiates at whatever `Fin`-encoded phase the configuration
carries. -/

theorem t1CS_aligned_step_right
    (n h : Nat) (hh : h < T1M.tapeLength n) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, Move.right)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n (h+1) hb (t1WriteCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_right t1CS
    (t1AlignedConfigQ n h hh tape q) (htr 0) hb _ rfl rfl (fun _ => rfl)

theorem t1CS_aligned_step_left
    (n h : Nat) (hh : h < T1M.tapeLength n) (hpos : 0 < h)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, Move.left)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n (h-1) (by omega) (t1WriteCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_left t1CS
    (t1AlignedConfigQ n h hh tape q) (htr 0) hpos _ rfl rfl (fun _ => rfl)

theorem t1CS_aligned_step_stay
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, Move.stay)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n h hh (t1WriteCell h w tape) q' :=
  ConstStatePhasedProgram.stepConfig_eq_of_transition_stay t1CS
    (t1AlignedConfigQ n h hh tape q) (htr 0) _ rfl rfl (fun _ => rfl)

/-- Four physical cells, read at an aligned head position. -/
def t1PhysicalBitsAt {n h : Nat} (hh : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) : List Bool :=
  [tape ⟨h, by omega⟩, tape ⟨h+1, by omega⟩,
   tape ⟨h+2, by omega⟩, tape ⟨h+3, by omega⟩]

/-! ## The shared forward frame macrostep -/

private theorem t1CS_step_forward_p0
    (n h : Nat) (hh : h < T1M.tapeLength n) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) {mode : T1Mode}
    (hmode : T1ForwardMode mode) (b0 b1 b2 latch : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape mode .p0 b0 b1 b2 latch) =
      t1AlignedConfig n (h+1) hb tape mode .p1 (tape ⟨h, hh⟩) false false latch := by
  have hstep := t1CS_aligned_step_right n h hh hb tape
    (t1State mode .p0 b0 b1 b2 latch)
    (t1State mode .p1 (tape ⟨h, hh⟩) false false latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_forward_p0 hmode phase b0 b1 b2 latch _)
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_step_forward_p1
    (n h : Nat) (hh : h < T1M.tapeLength n) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) {mode : T1Mode}
    (hmode : T1ForwardMode mode) (b0 b1 b2 latch : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape mode .p1 b0 b1 b2 latch) =
      t1AlignedConfig n (h+1) hb tape mode .p2 b0 (tape ⟨h, hh⟩) false latch := by
  have hstep := t1CS_aligned_step_right n h hh hb tape
    (t1State mode .p1 b0 b1 b2 latch)
    (t1State mode .p2 b0 (tape ⟨h, hh⟩) false latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_forward_p1 hmode phase b0 b1 b2 latch _)
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_step_forward_p2
    (n h : Nat) (hh : h < T1M.tapeLength n) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) {mode : T1Mode}
    (hmode : T1ForwardMode mode) (b0 b1 b2 latch : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape mode .p2 b0 b1 b2 latch) =
      t1AlignedConfig n (h+1) hb tape mode .p3 b0 b1 (tape ⟨h, hh⟩) latch := by
  have hstep := t1CS_aligned_step_right n h hh hb tape
    (t1State mode .p2 b0 b1 b2 latch)
    (t1State mode .p3 b0 b1 (tape ⟨h, hh⟩) latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_forward_p2 hmode phase b0 b1 b2 latch _)
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_step_forward_p3
    (n h : Nat) (hh : h < T1M.tapeLength n) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) {mode : T1Mode}
    (hmode : T1ForwardMode mode) (b0 b1 b2 latch : Bool)
    (hnext : t1Complete mode b0 b1 b2 (tape ⟨h, hh⟩) ≠ .reject) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape mode .p3 b0 b1 b2 latch) =
      t1AlignedConfig n (h+1) hb tape
        (t1Complete mode b0 b1 b2 (tape ⟨h, hh⟩)) .p0 false false false latch := by
  have hstep := t1CS_aligned_step_right n h hh hb tape
    (t1State mode .p3 b0 b1 b2 latch)
    (t1State (t1Complete mode b0 b1 b2 (tape ⟨h, hh⟩)) .p0 false false false latch)
    (tape ⟨h, hh⟩)
    (fun phase => t1Transition_forward_p3_advance hmode phase b0 b1 b2 latch _ hnext)
  rwa [t1WriteCell_self] at hstep

/-- **Four-bit decoding macrostep.**  In any forward mode — the five T1a
validation modes or the two T1b forward scans — a grammar-valid frame on an
arbitrary surrounding tape is decoded in exactly four physical TM steps.  The
head advances by four, no tape cell changes, and the latch is carried
through.  The latch is an explicit argument rather than an `optParam`, so an
import-side probe cannot silently pin only the `latch = false` instance. -/
theorem t1CS_frame_macrostep
    (n h : Nat) (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (mode : T1Mode) (frame : T1Frame)
    (hmode : T1ForwardMode mode)
    (hnext : t1Advance mode frame ≠ .reject)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape mode .p0 false false false latch) 4 =
      t1AlignedConfig n (h+4) hsafe tape (t1Advance mode frame)
        .p0 false false false latch := by
  have hcomplete : t1Complete mode (tape ⟨h, by omega⟩)
      (tape ⟨h+1, by omega⟩) (tape ⟨h+2, by omega⟩)
      (tape ⟨h+3, by omega⟩) = t1Advance mode frame := by
    simp only [t1PhysicalBitsAt] at hbits
    have hb0 : tape ⟨h, by omega⟩ = frame.bits[0]! := by
      simpa using congrArg (fun xs => xs[0]!) hbits
    have hb1 : tape ⟨h+1, by omega⟩ = frame.bits[1]! := by
      simpa using congrArg (fun xs => xs[1]!) hbits
    have hb2 : tape ⟨h+2, by omega⟩ = frame.bits[2]! := by
      simpa using congrArg (fun xs => xs[2]!) hbits
    have hb3 : tape ⟨h+3, by omega⟩ = frame.bits[3]! := by
      simpa using congrArg (fun xs => xs[3]!) hbits
    rw [hb0, hb1, hb2, hb3]
    cases frame with
    | data value | output value => cases value <;> rfl
    | blank | bof | index | spent | separator | cursor | finish => rfl
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n h (by omega) tape mode .p0 false false false latch)
      (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [t1CS_step_forward_p0 n h (by omega) (by omega) tape hmode
    false false false latch]
  rw [t1CS_step_forward_p1 n (h+1) (by omega) (by omega) tape hmode
    (tape ⟨h, by omega⟩) false false latch]
  rw [t1CS_step_forward_p2 n (h+2) (by omega) (by omega) tape hmode
    (tape ⟨h, by omega⟩) (tape ⟨h+1, by omega⟩) false latch]
  rw [t1CS_step_forward_p3 n (h+3) (by omega) hsafe tape hmode
    (tape ⟨h, by omega⟩) (tape ⟨h+1, by omega⟩) (tape ⟨h+2, by omega⟩) latch
    (by rw [hcomplete]; exact hnext)]
  rw [hcomplete]

/-! ## Stable sinks and idle boundary states -/

private theorem t1CS_stepConfig_stay_self {n : Nat}
    (c : Configuration (M := T1M) n) (q : T1State)
    (hs : c.state = ⟨t1Phase, q⟩)
    (htr : ∀ (phase : Fin 1) (scan : Bool),
      t1Transition phase q scan = (0, q, scan, Move.stay)) :
    TM.stepConfig (M := T1M) c = c := by
  have hfst : c.state.fst = t1Phase := by rw [hs]
  have hsnd : c.state.snd = q := by rw [hs]
  have htr' : t1CS.transition c.state.fst c.state.snd (c.tape c.head) =
      ((0 : Fin 1), q, c.tape c.head, Move.stay) := by
    rw [hfst, hsnd]; exact htr 0 (c.tape c.head)
  refine ConstStatePhasedProgram.stepConfig_eq_of_transition_stay t1CS c htr'
    c ?_ rfl ?_
  · rw [hs]; rfl
  · intro i
    by_cases hi : (i : Nat) = (c.head : Nat)
    · have hfin : i = c.head := Fin.ext hi
      simp [hfin]
    · simp [hi]

private theorem t1CS_runConfig_stay_self {n : Nat}
    (c : Configuration (M := T1M) n) (q : T1State)
    (hs : c.state = ⟨t1Phase, q⟩)
    (htr : ∀ (phase : Fin 1) (scan : Bool),
      t1Transition phase q scan = (0, q, scan, Move.stay))
    (steps : Nat) : TM.runConfig (M := T1M) c steps = c := by
  induction steps with
  | zero => rfl
  | succ k ih =>
      rw [runConfig_succ, ih]
      exact t1CS_stepConfig_stay_self c q hs htr

/-- A sink transition leaves the complete configuration unchanged. -/
theorem t1CS_stepConfig_sink {n : Nat} (c : Configuration (M := T1M) n)
    (q : T1State) (hq : q = t1AcceptState ∨ q = t1RejectState)
    (hs : c.state = ⟨t1Phase, q⟩) : TM.stepConfig (M := T1M) c = c := by
  refine t1CS_stepConfig_stay_self c q hs ?_
  rcases hq with rfl | rfl
  · exact fun phase scan => t1Transition_accept_sink phase scan
  · exact fun phase scan => t1Transition_reject_sink phase scan

/-- **Stable-sink run theorem.**  Either terminal sink preserves the entire
configuration for an arbitrary number of genuine TM steps. -/
theorem t1CS_runConfig_sink {n : Nat} (c : Configuration (M := T1M) n)
    (q : T1State) (hq : q = t1AcceptState ∨ q = t1RejectState)
    (hs : c.state = ⟨t1Phase, q⟩) (steps : Nat) :
    TM.runConfig (M := T1M) c steps = c := by
  induction steps with
  | zero => rfl
  | succ k ih =>
      rw [runConfig_succ, ih]
      exact t1CS_stepConfig_sink c q hq hs

/-- **The success boundary is idle.**  This is one of the two states that
replace T1a's idle `startMutation` handoff: `startMutation` is now an active
mutation mode, and the two idle handoff points for T1c are `successStart`
and `oobStart`.  The latched data value is preserved for T1c's output
write. -/
theorem t1CS_runConfig_successStart
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .successStart .p0 false false false latch)
        steps =
      t1AlignedConfig n h hh tape .successStart .p0 false false false latch :=
  t1CS_runConfig_stay_self _ (t1SuccessState latch) rfl
    (fun phase scan => t1Transition_successStart_idle phase latch scan) steps

/-- **The out-of-bounds boundary is idle.**  The second T1c handoff point. -/
theorem t1CS_runConfig_oobStart
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .oobStart .p0 false false false latch)
        steps =
      t1AlignedConfig n h hh tape .oobStart .p0 false false false latch :=
  t1CS_runConfig_stay_self _ (t1OobState latch) rfl
    (fun phase scan => t1Transition_oobStart_idle phase latch scan) steps

/-! ## Exact generic read-only validation -/

def t1ListTape {n : Nat} (bits : List Bool) :
    Fin (T1M.tapeLength n) → Bool := fun i => bits.getD i.val false

private theorem t1PhysicalBitsAt_flatMap
    (n : Nat) (pre suffix : List T1Frame) (frame : T1Frame)
    (hsafe : 4 * pre.length + 4 < T1M.tapeLength n) :
    t1PhysicalBitsAt hsafe
        (t1ListTape ((pre ++ frame :: suffix).flatMap T1Frame.bits)) =
      frame.bits := by
  have hlen := T1Frame.flatMap_bits_length pre
  cases frame with
  | data value | output value => cases value <;>
      simp [t1PhysicalBitsAt, t1ListTape, List.getD,
        List.flatMap_append, hlen, T1Frame.bits]
  | blank | bof | index | spent | separator | cursor | finish =>
      simp [t1PhysicalBitsAt, t1ListTape, List.getD,
        List.flatMap_append, hlen, T1Frame.bits]

def T1ValidPath : T1Mode → List T1Frame → Prop
  | _, [] => True
  | mode, frame :: rest =>
      T1ForwardMode mode ∧ t1Advance mode frame ≠ .reject ∧
        T1ValidPath (t1Advance mode frame) rest

def t1AdvanceList : T1Mode → List T1Frame → T1Mode
  | mode, [] => mode
  | mode, frame :: rest => t1AdvanceList (t1Advance mode frame) rest

/-- Scan a grammar-valid list of frames from left to right in exactly four TM
steps per frame.  The theorem preserves the complete list-backed tape and the
latch, and ends at the mode obtained by folding `t1Advance` over the scanned
frames.  As in `t1CS_frame_macrostep`, the latch is an explicit argument, not
an `optParam`. -/
theorem t1CS_scan_frames
    (n : Nat) (pre frames suffix : List T1Frame) (mode : T1Mode)
    (hpath : T1ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < T1M.tapeLength n)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * pre.length) (by omega)
          (t1ListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits)) mode
          .p0 false false false latch)
        (4 * frames.length) =
      t1AlignedConfig n (4 * (pre.length + frames.length)) hsafe
        (t1ListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits))
        (t1AdvanceList mode frames) .p0 false false false latch := by
  induction frames generalizing pre mode with
  | nil => simp [t1AdvanceList]
  | cons frame rest ih =>
      rcases hpath with ⟨hfwd, hnext, hrest⟩
      have hframeSafe : 4 * pre.length + 4 < T1M.tapeLength n := by
        simp only [List.length_cons] at hsafe
        omega
      have hmacro := t1CS_frame_macrostep n (4 * pre.length) hframeSafe
        (t1ListTape ((pre ++ frame :: rest ++ suffix).flatMap T1Frame.bits))
        mode frame hfwd hnext
        (by simpa [List.append_assoc] using
          t1PhysicalBitsAt_flatMap n pre (rest ++ suffix) frame hframeSafe)
        latch
      rw [show 4 * (frame :: rest).length = 4 + 4 * rest.length by simp; omega,
        runConfig_add, hmacro]
      have hsafeTail :
          4 * ((pre ++ [frame]).length + rest.length) < T1M.tapeLength n := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hsafe ⊢
        omega
      have htail := ih (pre ++ [frame]) (t1Advance mode frame) hrest hsafeTail
      simpa [List.length_append, List.length_nil, List.length_cons,
        List.singleton_append, List.append_assoc, t1AdvanceList, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

def t1ValidationFrames (r : T1Request) : List T1Frame :=
  encodeT1Frames r ++ [.blank]

@[simp] theorem t1ValidationFrames_length (r : T1Request) :
    (t1ValidationFrames r).length = r.index + r.data.length + 5 := by
  simp [t1ValidationFrames, encodeT1Frames]
  omega

@[simp] theorem t1ValidationPath (r : T1Request) :
    T1ValidPath .validateBof (t1ValidationFrames r) := by
  rcases r with ⟨index, data⟩
  have hd : T1ValidPath .validateData
      (data.map .data ++ [.output false, .finish, .blank]) := by
    induction data with
    | nil => simp [T1ValidPath, T1ForwardMode, t1Advance]
    | cons b bs ih => cases b <;>
        simp [T1ValidPath, T1ForwardMode, t1Advance, ih]
  have hi : T1ValidPath .validateIndex
      (List.replicate index .index ++ .separator ::
        data.map .data ++ [.output false, .finish, .blank]) := by
    induction index with
    | zero => simpa [T1ValidPath, T1ForwardMode, t1Advance] using hd
    | succ k ih => simpa [List.replicate_succ, T1ValidPath,
        T1ForwardMode, t1Advance] using ih
  simpa [t1ValidationFrames, encodeT1Frames, T1ValidPath,
    T1ForwardMode, t1Advance] using hi

@[simp] theorem t1ValidationAdvance (r : T1Request) :
    t1AdvanceList .validateBof (t1ValidationFrames r) = .rewindStart := by
  rcases r with ⟨index, data⟩
  have hd : t1AdvanceList .validateData
      (data.map .data ++ [.output false, .finish, .blank]) = .rewindStart := by
    induction data with
    | nil => rfl
    | cons b bs ih => cases b <;> simpa [t1AdvanceList, t1Advance] using ih
  have hi : t1AdvanceList .validateIndex
      (List.replicate index .index ++ .separator ::
        data.map .data ++ [.output false, .finish, .blank]) = .rewindStart := by
    induction index with
    | zero => simpa [t1AdvanceList, t1Advance] using hd
    | succ k ih => simpa [List.replicate_succ, t1AdvanceList, t1Advance] using ih
  simpa [t1ValidationFrames, encodeT1Frames, t1AdvanceList, t1Advance] using hi

/-- The canonical encoder frames followed by the physical blank frame form a
complete valid trace of the forward control automaton, ending at rewind.  This
states an encoder/automaton trace, not full parser/machine equivalence. -/
theorem t1CanonicalEncoderAutomatonTrace (r : T1Request) :
    T1ValidPath .validateBof (encodeT1Frames r ++ [.blank]) ∧
      t1AdvanceList .validateBof (encodeT1Frames r ++ [.blank]) =
        .rewindStart := by
  simpa [t1ValidationFrames] using
    And.intro (t1ValidationPath r) (t1ValidationAdvance r)

/-- Canonical input tape equals the same tape with one explicit blank frame
appended.  This is precisely where the binary-tape EOF ambiguity is handled. -/
private theorem t1Blank_getD (k : Nat) : T1Frame.blank.bits.getD k false = false := by
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rfl

theorem t1ListTape_validation_eq_initial (r : T1Request) :
    t1ListTape (n := (encodeT1 r).length)
        ((t1ValidationFrames r).flatMap T1Frame.bits) =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape := by
  funext i
  simp only [t1ListTape, t1ValidationFrames, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, encodeT1, TM.initialConfig, t1Point]
  simp only [List.append_nil, List.getD, List.getElem?_append]
  have hlen : (encodeT1 r).length = (encodeT1Frames r).length * 4 := by
    rw [encodeT1, T1Frame.flatMap_bits_length]
    omega
  have hflat := T1Frame.flatMap_bits_length (encodeT1Frames r)
  by_cases h : i.val < (encodeT1 r).length
  · have h' : i.val < ((encodeT1Frames r).flatMap T1Frame.bits).length := by
      exact h
    have h'' : i.val < (encodeT1Frames r).length * 4 := by omega
    simp [h'']
  · have h' : ¬ i.val < ((encodeT1Frames r).flatMap T1Frame.bits).length := by
      exact h
    have h'' : ¬ i.val < (encodeT1Frames r).length * 4 := by omega
    simp only [if_neg h', dif_neg h']
    change T1Frame.blank.bits.getD
      (i.val - ((encodeT1Frames r).flatMap T1Frame.bits).length) false = false
    exact t1Blank_getD _

/-- **Exact generic validation theorem.**  Every canonical request—whether
the represented index is in bounds or not—passes the complete grammar and one
blank frame in exactly `encodeT1 r.length + 4` genuine TM steps.  The machine
is then at `rewindStart`, and the entire tape is still the initial tape. -/
theorem t1CS_validate_encoded_exact (r : T1Request) :
    let n := (encodeT1 r).length
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r))) (n + 4) =
      t1AlignedConfig n (n + 4) (by
        simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength, t1Clock]; omega)
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .rewindStart := by
  dsimp
  have hsafe : 4 * (t1ValidationFrames r).length <
      T1M.tapeLength (encodeT1 r).length := by
    simp [T1M, t1CS, ConstStatePhasedProgram.toPhased, PhasedProgram.toTM,
      TM.tapeLength, t1Clock]
    omega
  have hscan := t1CS_scan_frames (encodeT1 r).length [] (t1ValidationFrames r) []
    .validateBof (t1ValidationPath r) (by simpa using hsafe) false
  simp only [List.nil_append, List.append_nil, List.length_nil, zero_add,
    t1ValidationAdvance] at hscan
  have hinit : T1M.initialConfig (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length 0 (by
        simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength])
        (t1ListTape ((t1ValidationFrames r).flatMap T1Frame.bits))
        .validateBof := by
    cases r with
    | mk index data =>
      simp [TM.initialConfig, t1Point, t1AlignedConfig, t1AlignedConfigQ,
        t1Phase, t1CS, ConstStatePhasedProgram.toPhased, PhasedProgram.toTM,
        t1ListTape_validation_eq_initial]
  rw [hinit]
  simp only [t1AlignedConfig_tape]
  simpa using hscan

/-! ### Exact rewind to the mutation handoff -/

private theorem t1CS_step_rewind_p3
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p3 false false false latch) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p2 false false
        (tape ⟨h, hh⟩) latch := by
  have hstep := t1CS_aligned_step_left n h hh hpos tape
    (t1State .rewind .p3 false false false latch)
    (t1State .rewind .p2 false false (tape ⟨h, hh⟩) latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_rewind_p3 phase false false false latch _)
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_step_rewind_p2
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b2 latch : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p2 false false b2 latch) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p1 false
        (tape ⟨h, hh⟩) b2 latch := by
  have hstep := t1CS_aligned_step_left n h hh hpos tape
    (t1State .rewind .p2 false false b2 latch)
    (t1State .rewind .p1 false (tape ⟨h, hh⟩) b2 latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_rewind_p2 phase false false b2 latch _)
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_step_rewind_p1
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b1 b2 latch : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p1 false b1 b2 latch) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p0
        (tape ⟨h, hh⟩) b1 b2 latch := by
  have hstep := t1CS_aligned_step_left n h hh hpos tape
    (t1State .rewind .p1 false b1 b2 latch)
    (t1State .rewind .p0 (tape ⟨h, hh⟩) b1 b2 latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_rewind_p1 phase false b1 b2 latch _)
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_step_rewind_p0_other
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b0 b1 b2 latch : Bool)
    (hne : decodeT1Frame? [tape ⟨h, hh⟩, b0, b1, b2] ≠ some .bof) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p0 b0 b1 b2 latch) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p3
        false false false latch := by
  have hstep := t1CS_aligned_step_left n h hh hpos tape
    (t1State .rewind .p0 b0 b1 b2 latch)
    (t1State .rewind .p3 false false false latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_rewind_p0_other phase b0 b1 b2 latch _ hne)
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_step_rewind_p0_bof
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b0 b1 b2 latch : Bool)
    (heq : decodeT1Frame? [tape ⟨h, hh⟩, b0, b1, b2] = some .bof) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p0 b0 b1 b2 latch) =
      t1AlignedConfig n h hh tape .startMutation .p0 false false false latch := by
  have hstep := t1CS_aligned_step_stay n h hh tape
    (t1State .rewind .p0 b0 b1 b2 latch)
    (t1State .startMutation .p0 false false false latch) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_rewind_p0_bof phase b0 b1 b2 latch _ heq)
  rwa [t1WriteCell_self] at hstep

/-- Reverse-decode one non-`bof` frame in exactly four physical steps. -/
private theorem t1CS_rewind_frame_other
    (n base : Nat) (hbase : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (frame : T1Frame)
    (hne : frame ≠ .bof)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .rewind .p3) 4 =
      t1AlignedConfig n (base-1) (by omega) tape .rewind .p3 := by
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .rewind .p3)
      (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .rewind .p3) =
      t1AlignedConfig n (base+2) (by omega) tape .rewind .p2 false false
        (tape ⟨base+3, by omega⟩) := by
    simpa using t1CS_step_rewind_p3 n (base+3) (by omega) (by omega) tape false
  rw [hs1]
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .rewind .p2 false false
        (tape ⟨base+3, by omega⟩)) =
      t1AlignedConfig n (base+1) (by omega) tape .rewind .p1 false
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) := by
    simpa using t1CS_step_rewind_p2 n (base+2) (by omega) (by omega) tape
      (tape ⟨base+3, by omega⟩) false
  rw [hs2]
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .rewind .p1 false
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩)) =
      t1AlignedConfig n base (by omega) tape .rewind .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) := by
    simpa using t1CS_step_rewind_p1 n (base+1) (by omega) (by omega) tape
      (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) false
  rw [hs3]
  apply t1CS_step_rewind_p0_other
  · omega
  · simp only [t1PhysicalBitsAt] at hbits
    have hdecode : decodeT1Frame? [tape ⟨base, by omega⟩,
        tape ⟨base+1, by omega⟩, tape ⟨base+2, by omega⟩,
        tape ⟨base+3, by omega⟩] = some frame := by
      rw [hbits]
      exact decodeT1Frame_bits frame
    simpa [hdecode] using hne

/-- Reverse-decode the left anchor and enter the mutation handoff. -/
private theorem t1CS_rewind_bof
    (n : Nat) (hsafe : 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = T1Frame.bof.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n 3 (by omega) tape .rewind .p3) 4 =
      t1AlignedConfig n 0 (by omega) tape .startMutation := by
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n 3 (by omega) tape .rewind .p3) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [t1CS_step_rewind_p3 n 3 (by omega) (by omega) tape false]
  rw [t1CS_step_rewind_p2 n 2 (by omega) (by omega) tape
    (tape ⟨3, by omega⟩) false]
  rw [t1CS_step_rewind_p1 n 1 (by omega) (by omega) tape
    (tape ⟨2, by omega⟩) (tape ⟨3, by omega⟩) false]
  apply t1CS_step_rewind_p0_bof
  simp only [t1PhysicalBitsAt] at hbits
  rw [hbits]
  rfl

private theorem t1CS_step_rewindStart
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewindStart) 1 =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p3 := by
  rw [runConfig_one]
  have hstep := t1CS_aligned_step_left n h hh hpos tape
    (t1State .rewindStart .p0 false false false false)
    (t1State .rewind .p3 false false false false) (tape ⟨h, hh⟩)
    (fun phase => t1Transition_rewindStart phase .p0 false false false false _)
  rwa [t1WriteCell_self] at hstep

/-- Rewind right-to-left across a list of non-`bof` frames in exactly four TM
steps per frame.  The complete list-backed tape is preserved and the head
finishes on the final bit of the leading `bof` frame. -/
theorem t1CS_rewind_tail
    (n : Nat) (tail suffix : List T1Frame)
    (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < T1M.tapeLength n) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
          .rewind .p3) (4 * tail.length) =
      t1AlignedConfig n 3 (by omega)
        (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
        .rewind .p3 := by
  induction tail using List.reverseRecOn generalizing suffix with
  | nil => simp
  | append_singleton rest frame ih =>
      have hframeNe : frame ≠ .bof := hne frame (by simp)
      have hrestNe : ∀ f ∈ rest, f ≠ .bof := by
        intro f hf
        exact hne f (by simp [hf])
      have hframeSafe : 4 * (1 + rest.length) + 4 < T1M.tapeLength n := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hsafe
        omega
      have hframeBits : t1PhysicalBitsAt hframeSafe
          (t1ListTape ((.bof :: (rest ++ [frame]) ++ suffix).flatMap T1Frame.bits)) =
          frame.bits := by
        have raw := t1PhysicalBitsAt_flatMap n (.bof :: rest) suffix frame (by
          simpa [Nat.add_comm] using hframeSafe)
        convert raw using 1
        all_goals simp [List.append_assoc, Nat.add_comm]
      have hframe := t1CS_rewind_frame_other n (4 * (1 + rest.length))
        (by omega) hframeSafe
        (t1ListTape ((.bof :: (rest ++ [frame]) ++ suffix).flatMap T1Frame.bits))
        frame hframeNe hframeBits
      have hframe' : TM.runConfig (M := T1M)
          (t1AlignedConfig n (4 * (1 + (rest ++ [frame]).length) - 1) (by omega)
            (t1ListTape ((.bof :: (rest ++ [frame]) ++ suffix).flatMap T1Frame.bits))
            .rewind .p3) 4 =
          t1AlignedConfig n (4 * (1 + rest.length) - 1) (by omega)
            (t1ListTape ((.bof :: (rest ++ [frame]) ++ suffix).flatMap T1Frame.bits))
            .rewind .p3 := by
        simpa [List.length_append, Nat.mul_add] using hframe
      rw [show 4 * (rest ++ [frame]).length = 4 + 4 * rest.length by simp; omega,
        runConfig_add, hframe']
      have hrestSafe : 4 * (1 + rest.length) < T1M.tapeLength n := by omega
      have htail := ih (frame :: suffix) hrestNe hrestSafe
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htail

set_option maxHeartbeats 800000 in
/-- Canonical validation and rewind reach the exact start-of-mutation boundary
in `2 * encodeT1 r.length + 9` steps, with the complete tape unchanged.  This
is the T1a result, preserved verbatim: it is the entry point of the T1b
mutation phase. -/
theorem t1CS_validate_rewind_encoded_exact (r : T1Request) :
    let n := (encodeT1 r).length
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (2 * n + 9) =
      t1AlignedConfig n 0 (by
        simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength])
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation := by
  dsimp
  rw [show 2 * (encodeT1 r).length + 9 =
      ((encodeT1 r).length + 4) + 1 + 4 * (t1ValidationFrames r).length by
        simp [t1ValidationFrames_length]; omega,
    runConfig_add, runConfig_add, t1CS_validate_encoded_exact r]
  have hsafe : 4 * (1 + (t1ValidationFrames r).tail.length) <
      T1M.tapeLength (encodeT1 r).length := by
    have hleft : 4 * (1 + (t1ValidationFrames r).tail.length) =
        (encodeT1 r).length + 4 := by
      rcases r with ⟨index, data⟩
      simp [t1ValidationFrames, encodeT1Frames]
      omega
    rw [hleft]
    simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
      PhasedProgram.toTM, TM.tapeLength, t1Clock]
    omega
  rw [t1CS_step_rewindStart (encodeT1 r).length ((encodeT1 r).length + 4)
    (by omega)]
  have hne : ∀ f ∈ (t1ValidationFrames r).tail, f ≠ T1Frame.bof := by
    intro f hf heq
    subst f
    rcases r with ⟨index, data⟩
    simp [t1ValidationFrames, encodeT1Frames] at hf
  have htail := t1CS_rewind_tail (encodeT1 r).length
    (t1ValidationFrames r).tail [] hne hsafe
  have hbofSafe : 4 < T1M.tapeLength (encodeT1 r).length := by
    simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
      PhasedProgram.toTM, TM.tapeLength, t1Clock]
    omega
  have hbof := t1CS_rewind_bof (encodeT1 r).length hbofSafe
    (T1M.initialConfig (t1Point (encodeT1 r))).tape (by
      rw [← t1ListTape_validation_eq_initial r]
      simpa [t1ValidationFrames, encodeT1Frames] using
        t1PhysicalBitsAt_flatMap (encodeT1 r).length []
          (t1ValidationFrames r).tail .bof hbofSafe)
  rw [show 4 * (t1ValidationFrames r).length =
      4 * (t1ValidationFrames r).tail.length + 4 by
        simp [t1ValidationFrames, encodeT1Frames]; omega,
    runConfig_add]
  have htape : t1ListTape (n := (encodeT1 r).length)
      ((T1Frame.bof :: (t1ValidationFrames r).tail ++ []).flatMap T1Frame.bits) =
      (T1M.initialConfig (t1Point (encodeT1 r))).tape := by
    simpa [t1ValidationFrames, encodeT1Frames] using
      t1ListTape_validation_eq_initial r
  rw [htape] at htail
  have hleft : 4 * (1 + (t1ValidationFrames r).tail.length) =
      (encodeT1 r).length + 4 := by
    rcases r with ⟨index, data⟩
    simp [t1ValidationFrames, encodeT1Frames]
    omega
  have hheadSafe : (encodeT1 r).length + 4 - 1 <
      T1M.tapeLength (encodeT1 r).length := by omega
  have htail' : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length ((encodeT1 r).length + 4 - 1)
        hheadSafe (T1M.initialConfig (t1Point (encodeT1 r))).tape
        .rewind .p3) (4 * (t1ValidationFrames r).tail.length) =
      t1AlignedConfig (encodeT1 r).length 3 (by omega)
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .rewind .p3 := by
    simpa only [hleft] using htail
  rw [htail', hbof]

end Pnp3.Internal.PsubsetPpoly.TM
