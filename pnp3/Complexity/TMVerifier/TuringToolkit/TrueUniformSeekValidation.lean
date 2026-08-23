import Complexity.TMVerifier.TuringToolkit.TrueUniformSeek

/-!
# Generic T1a execution theorems

The results here are about `TM.runConfig`/`TM.run`, not a separate pure
interpreter.  They establish the four-bit forward macrostep, stable terminal
sinks, and the exact read-only validation/rewind trace for every canonical
request.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- The concrete T1 machine used by the execution-theorem surface. -/
abbrev T1M := t1CS.toPhased.toTM

private def t1Phase : Fin t1CS.toPhased.numPhases := t1CS.toPhased.startPhase

@[simp] private theorem T1M_step (s : T1State) (scan : Bool) :
    T1M.step ⟨t1Phase, s⟩ scan =
      let r := t1Transition 0 s scan
      (⟨r.1, r.2.1⟩, r.2.2.1, r.2.2.2) := rfl

/-- A configuration with arbitrary tape, aligned control, and an explicit
physical head position.  This constructor only packages `Fin` bookkeeping. -/
def t1AlignedConfig (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (mode : T1Mode)
    (position := T1FramePosition.p0) (b0 := false) (b1 := false)
    (b2 := false) : Configuration (M := T1M) n where
  state := ⟨t1Phase, t1State mode position b0 b1 b2⟩
  head := ⟨h, hh⟩
  tape := tape

@[simp] theorem t1AlignedConfig_state (n h hh tape mode position b0 b1 b2) :
    (t1AlignedConfig n h hh tape mode position b0 b1 b2).state =
      ⟨t1Phase, t1State mode position b0 b1 b2⟩ := rfl

@[simp] theorem t1AlignedConfig_head_val (n h hh tape mode position b0 b1 b2) :
    ((t1AlignedConfig n h hh tape mode position b0 b1 b2).head : Nat) = h := rfl

@[simp] theorem t1AlignedConfig_tape (n h hh tape mode position b0 b1 b2) :
    (t1AlignedConfig n h hh tape mode position b0 b1 b2).tape = tape := rfl

/-- Four physical cells, read at an aligned head position. -/
def t1PhysicalBitsAt {n h : Nat} (hh : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) : List Bool :=
  [tape ⟨h, by omega⟩, tape ⟨h+1, by omega⟩,
   tape ⟨h+2, by omega⟩, tape ⟨h+3, by omega⟩]

/-- Modes in which the T1 control reads a frame from left to right. -/
def T1ForwardMode : T1Mode → Prop
  | .validateBof | .validateIndex | .validateData | .validateFinish
  | .validateBlank => True
  | _ => False

/-- **Four-bit decoding macrostep.**  From any aligned configuration and any
arbitrary surrounding tape, a grammar-valid frame is decoded in exactly four
physical TM steps.  The head advances by four and no tape cell changes. -/
private theorem t1CS_step_forward
    (n h : Nat) (hsafe : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (mode : T1Mode)
    (position : T1FramePosition) (b0 b1 b2 : Bool)
    (hmode : mode = .validateBof ∨ mode = .validateIndex ∨
      mode = .validateData ∨ mode = .validateFinish ∨ mode = .validateBlank) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape mode position b0 b1 b2) =
      match position with
      | .p0 => t1AlignedConfig n (h+1) hsafe tape mode .p1
          (tape ⟨h, by omega⟩)
      | .p1 => t1AlignedConfig n (h+1) hsafe tape mode .p2 b0
          (tape ⟨h, by omega⟩)
      | .p2 => t1AlignedConfig n (h+1) hsafe tape mode .p3 b0 b1
          (tape ⟨h, by omega⟩)
      | .p3 =>
          let next := t1Complete mode b0 b1 b2 (tape ⟨h, by omega⟩)
          if next = .reject then
            { state := ⟨t1Phase, t1RejectState⟩,
              head := ⟨h, by omega⟩, tape := tape }
          else t1AlignedConfig n (h+1) hsafe tape next := by
  have hsafe' : h + 1 < n + t1Clock n + 1 := by
    simpa [T1M, t1CS, ConstStatePhasedProgram.toPhased,
      PhasedProgram.toTM, TM.tapeLength] using hsafe
  rcases hmode with rfl | rfl | rfl | rfl | rfl <;> cases position <;>
    simp [TM.stepConfig, t1AlignedConfig, T1M, t1Phase, t1CS,
      ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
      t1State, TM.tapeLength, Configuration.moveHead,
      Configuration.write, funext_iff, hsafe'] <;>
    split <;> simp_all [Configuration.write, funext_iff]

/-- **Four-bit decoding macrostep.**  In any forward validation mode, a
grammar-valid frame on an arbitrary surrounding tape is decoded in exactly
four physical TM steps.  The head advances by four and no tape cell changes. -/
theorem t1CS_frame_macrostep
    (n h : Nat) (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (mode : T1Mode) (frame : T1Frame)
    (hmode : T1ForwardMode mode)
    (hnext : t1Advance mode frame ≠ .reject)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape mode) 4 =
      t1AlignedConfig n (h+4) hsafe tape (t1Advance mode frame) := by
  have hfwd : mode = .validateBof ∨ mode = .validateIndex ∨
      mode = .validateData ∨ mode = .validateFinish ∨ mode = .validateBlank := by
    cases mode <;> simp_all [T1ForwardMode]
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n h (by omega) tape mode) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [t1CS_step_forward n h (by omega) tape mode .p0 false false false hfwd]
  rw [t1CS_step_forward n (h+1) (by omega) tape mode .p1
    (tape ⟨h, by omega⟩) false false hfwd]
  rw [t1CS_step_forward n (h+2) (by omega) tape mode .p2
    (tape ⟨h, by omega⟩) (tape ⟨h+1, by omega⟩) false hfwd]
  rw [t1CS_step_forward n (h+3) hsafe tape mode .p3
    (tape ⟨h, by omega⟩) (tape ⟨h+1, by omega⟩)
    (tape ⟨h+2, by omega⟩) hfwd]
  simp only [t1PhysicalBitsAt] at hbits
  have hcomplete : t1Complete mode (tape ⟨h, by omega⟩)
      (tape ⟨h+1, by omega⟩) (tape ⟨h+2, by omega⟩)
      (tape ⟨h+3, by omega⟩) = t1Advance mode frame := by
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
    | data value | output value => cases value <;>
        rfl
    | blank | bof | index | spent | separator | cursor | finish => rfl
  simp [hcomplete, hnext]

/-- A sink transition leaves the complete configuration unchanged. -/
theorem t1CS_stepConfig_sink {n : Nat} (c : Configuration (M := T1M) n)
    (q : T1State) (hq : q = t1AcceptState ∨ q = t1RejectState)
    (hs : c.state = ⟨t1Phase, q⟩) : TM.stepConfig (M := T1M) c = c := by
  rcases hq with rfl | rfl <;>
    cases c with
    | mk state head tape =>
      simp only at hs
      subst state
      simp [TM.stepConfig, t1Phase, t1CS,
        ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
        t1AcceptState, t1RejectState, t1State, Configuration.moveHead,
        Configuration.write, funext_iff]

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

private theorem t1CS_stepConfig_mutation {n : Nat}
    (c : Configuration (M := T1M) n)
    (hs : c.state = ⟨t1Phase, t1MutationState⟩) :
    TM.stepConfig (M := T1M) c = c := by
  cases c with
  | mk state head tape =>
    simp only at hs
    subst state
    simp [TM.stepConfig, t1Phase, t1CS, ConstStatePhasedProgram.toPhased,
      PhasedProgram.toTM, t1Transition, t1MutationState, t1State,
      Configuration.moveHead, Configuration.write, funext_iff]

/-- The T1a mutation boundary is idle until T1b supplies the destructive seek. -/
theorem t1CS_runConfig_mutation {n : Nat} (c : Configuration (M := T1M) n)
    (hs : c.state = ⟨t1Phase, t1MutationState⟩) (steps : Nat) :
    TM.runConfig (M := T1M) c steps = c := by
  induction steps with
  | zero => rfl
  | succ k ih =>
      rw [runConfig_succ, ih]
      exact t1CS_stepConfig_mutation c hs

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
steps per frame.  The theorem preserves the complete list-backed tape and
ends at the mode obtained by folding `t1Advance` over the scanned frames. -/
theorem t1CS_scan_frames
    (n : Nat) (pre frames suffix : List T1Frame) (mode : T1Mode)
    (hpath : T1ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < T1M.tapeLength n) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * pre.length) (by omega)
          (t1ListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits)) mode)
        (4 * frames.length) =
      t1AlignedConfig n (4 * (pre.length + frames.length)) hsafe
        (t1ListTape ((pre ++ frames ++ suffix).flatMap T1Frame.bits))
        (t1AdvanceList mode frames) := by
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
    .validateBof (t1ValidationPath r) (by simpa using hsafe)
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
      simp [TM.initialConfig, t1Point, t1AlignedConfig, t1Phase, t1CS,
        ConstStatePhasedProgram.toPhased, PhasedProgram.toTM,
        t1ListTape_validation_eq_initial]
  rw [hinit]
  simp only [t1AlignedConfig_tape]
  simpa using hscan

/-! ### Exact rewind to the mutation handoff -/

private theorem t1CS_step_rewind_p3
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) :
    TM.stepConfig (M := T1M) (t1AlignedConfig n h hh tape .rewind .p3) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p2 false false
        (tape ⟨h, hh⟩) := by
  have hne : h ≠ 0 := Nat.ne_of_gt hpos
  simp [TM.stepConfig, t1AlignedConfig, t1Phase, t1CS,
    ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
    t1State, Configuration.moveHead, Configuration.write, funext_iff, hne]

private theorem t1CS_step_rewind_p2
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b2 : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p2 false false b2) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p1 false
        (tape ⟨h, hh⟩) b2 := by
  have hne : h ≠ 0 := Nat.ne_of_gt hpos
  simp [TM.stepConfig, t1AlignedConfig, t1Phase, t1CS,
    ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
    t1State, Configuration.moveHead, Configuration.write, funext_iff, hne]

private theorem t1CS_step_rewind_p1
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b1 b2 : Bool) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p1 false b1 b2) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p0
        (tape ⟨h, hh⟩) b1 b2 := by
  have hne : h ≠ 0 := Nat.ne_of_gt hpos
  simp [TM.stepConfig, t1AlignedConfig, t1Phase, t1CS,
    ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
    t1State, Configuration.moveHead, Configuration.write, funext_iff, hne]

private theorem t1CS_step_rewind_p0_other
    (n h : Nat) (hpos : 0 < h) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b0 b1 b2 : Bool)
    (hne : decodeT1Frame? [tape ⟨h, hh⟩, b0, b1, b2] ≠ some .bof) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p0 b0 b1 b2) =
      t1AlignedConfig n (h-1) (by omega) tape .rewind .p3 := by
  have hzero : h ≠ 0 := Nat.ne_of_gt hpos
  simp [TM.stepConfig, t1AlignedConfig, t1Phase, t1CS,
    ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
    t1State, Configuration.moveHead, Configuration.write, funext_iff, hzero, hne]

private theorem t1CS_step_rewind_p0_bof
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (b0 b1 b2 : Bool)
    (heq : decodeT1Frame? [tape ⟨h, hh⟩, b0, b1, b2] = some .bof) :
    TM.stepConfig (M := T1M)
        (t1AlignedConfig n h hh tape .rewind .p0 b0 b1 b2) =
      t1AlignedConfig n h hh tape .startMutation := by
  simp [TM.stepConfig, t1AlignedConfig, t1Phase, t1CS,
    ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
    t1State, t1MutationState, Configuration.moveHead, Configuration.write,
    funext_iff, heq]

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
    simpa using t1CS_step_rewind_p3 n (base+3) (by omega) (by omega) tape
  rw [hs1]
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .rewind .p2 false false
        (tape ⟨base+3, by omega⟩)) =
      t1AlignedConfig n (base+1) (by omega) tape .rewind .p1 false
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) := by
    simpa using t1CS_step_rewind_p2 n (base+2) (by omega) (by omega) tape
      (tape ⟨base+3, by omega⟩)
  rw [hs2]
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .rewind .p1 false
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩)) =
      t1AlignedConfig n base (by omega) tape .rewind .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) := by
    simpa using t1CS_step_rewind_p1 n (base+1) (by omega) (by omega) tape
      (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩)
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
  rw [t1CS_step_rewind_p3 n 3 (by omega) (by omega) tape]
  rw [t1CS_step_rewind_p2 n 2 (by omega) (by omega) tape
    (tape ⟨3, by omega⟩)]
  rw [t1CS_step_rewind_p1 n 1 (by omega) (by omega) tape
    (tape ⟨2, by omega⟩) (tape ⟨3, by omega⟩)]
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
  have hne : h ≠ 0 := Nat.ne_of_gt hpos
  simp [runConfig_one, TM.stepConfig, t1AlignedConfig, t1Phase, t1CS,
    ConstStatePhasedProgram.toPhased, PhasedProgram.toTM, t1Transition,
    t1State, Configuration.moveHead, Configuration.write, funext_iff, hne]

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
in `2 * encodeT1 r.length + 9` steps, with the complete tape unchanged. -/
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

/-- A canonical request reaches the read-only mutation boundary under the
machine's public exact quadratic clock.  This is a `TM.run` theorem; it is not
an addressing-success theorem. -/
theorem t1CS_run_encoded_reaches_mutation (r : T1Request) :
    let n := (encodeT1 r).length
    T1M.run (t1Point (encodeT1 r)) =
      t1AlignedConfig n 0 (by
        simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength])
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation := by
  dsimp
  let N := (encodeT1 r).length
  have hsq : N + 1 ≤ (N + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right (N + 1) (by omega)
  have hle : 2 * N + 9 ≤ t1Clock N := by
    calc
      2 * N + 9 ≤ 128 * (N + 1) + 128 := by omega
      _ ≤ 128 * (N + 1) ^ 2 + 128 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 128 hsq) 128
      _ = t1Clock N := rfl
  let remaining := t1Clock N - (2 * N + 9)
  have hclock : t1Clock N = 2 * N + 9 + remaining := by
    exact (Nat.add_sub_of_le hle).symm
  let target : Configuration (M := T1M) N :=
    t1AlignedConfig N 0 (by
      simp [T1M, t1CS, ConstStatePhasedProgram.toPhased,
        PhasedProgram.toTM, TM.tapeLength])
      (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation
  rw [TM.run]
  change TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
      (t1Clock N) = target
  rw [hclock, runConfig_add, t1CS_validate_rewind_encoded_exact r]
  apply t1CS_runConfig_mutation
  rfl

end Pnp3.Internal.PsubsetPpoly.TM
