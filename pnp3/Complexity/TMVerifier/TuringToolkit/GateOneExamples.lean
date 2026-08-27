import Complexity.TMVerifier.TuringToolkit.GateOneSemantics
import Complexity.TMVerifier.TuringToolkit.GateOneValidation

/-!
# G1 named examples

**Progress classification: Infrastructure.**  Concrete instances of the T2a
surface: the ABI round trip, the pure rejections, the pure semantics, the
executable capstone at every gate tag, frame-control rejection of wrong tag
counts, and concrete machine-level rejection of every encoded noncanonical
request class.  Nothing depends on this module; it is an audit surface.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1Examples

/-! ## Concrete requests, one per tag -/

def reqInput : G1Request := ⟨.input, 1, 0, [true, false]⟩
def reqConst : G1Request := ⟨.const, 1, 0, []⟩
def reqNot : G1Request := ⟨.not, 0, 0, [true]⟩
def reqAnd : G1Request := ⟨.and, 0, 1, [true, false]⟩
def reqOr : G1Request := ⟨.or, 0, 1, [false, true]⟩

theorem reqInput_canonical : reqInput.Canonical := by decide
theorem reqConst_canonical : reqConst.Canonical := by decide
theorem reqNot_canonical : reqNot.Canonical := by decide
theorem reqAnd_canonical : reqAnd.Canonical := by decide
theorem reqOr_canonical : reqOr.Canonical := by decide

/-! ## ABI round trip -/

theorem decode_encode_reqInput : decodeG1Tape? (encodeG1 reqInput) =
    some reqInput := decodeG1Tape_encode _ reqInput_canonical

theorem decode_encode_reqConst : decodeG1Tape? (encodeG1 reqConst) =
    some reqConst := decodeG1Tape_encode _ reqConst_canonical

theorem decode_encode_reqNot : decodeG1Tape? (encodeG1 reqNot) =
    some reqNot := decodeG1Tape_encode _ reqNot_canonical

theorem decode_encode_reqAnd : decodeG1Tape? (encodeG1 reqAnd) =
    some reqAnd := decodeG1Tape_encode _ reqAnd_canonical

theorem decode_encode_reqOr : decodeG1Tape? (encodeG1 reqOr) =
    some reqOr := decodeG1Tape_encode _ reqOr_canonical

/-- Exact physical length of a concrete canonical word. -/
theorem encode_reqAnd_length : (encodeG1 reqAnd).length = 4 * 13 := by
  rw [encodeG1_length]; rfl

/-- The output cell of a concrete canonical word starts at `false`. -/
theorem encode_reqAnd_output :
    (encodeG1 reqAnd).getD (g1OutputPosition reqAnd) false = false :=
  encodeG1_getD_outputPosition reqAnd

/-! ## Pure rejection

Every case the T2a deliverable lists, concretely.  Each is an instance of the
canonicity characterisation `decodeG1Tape?_iff`, or a direct evaluation of the
pure decoder. -/

/-- A reserved code (`1111`) is rejected. -/
theorem reject_reserved_code :
    decodeG1Tape? [true, true, true, true] = none := rfl

/-- A word of length not divisible by four is rejected. -/
theorem reject_ragged_word : decodeG1Tape? [false, false, false] = none := rfl

/-- **Wrong tag count: empty tag run.** -/
theorem reject_zero_tags (rest : List G1Frame) :
    decodeG1FrameList? (.bof :: .argSep :: rest) = none := by
  simpa using decodeG1FrameList?_reject_tagRun 0 rfl rest

/-- **Wrong tag count: six tag units.** -/
theorem reject_six_tags (rest : List G1Frame) :
    decodeG1FrameList?
      (.bof :: .tag :: .tag :: .tag :: .tag :: .tag :: .tag :: .argSep ::
        rest) = none := by
  simpa [List.replicate] using decodeG1FrameList?_reject_tagRun 6 rfl rest

/-- **Missing delimiter**: the second `argSep` is absent. -/
theorem reject_missing_argSep :
    decodeG1FrameList?
      [.bof, .tag, .argSep, .separator, .output false, .finish] = none := by
  decide

/-- **Missing terminator**: the `finish` frame is absent. -/
theorem reject_missing_finish :
    decodeG1FrameList?
      [.bof, .tag, .argSep, .argSep, .separator, .output false] = none := by
  decide

/-- **Trailing junk** after the terminator. -/
theorem reject_trailing_frame :
    decodeG1FrameList?
      [.bof, .tag, .argSep, .argSep, .separator, .output false, .finish,
        .blank] = none := by
  decide

/-- **A machine-internal marker** in the input word is rejected. -/
theorem reject_internal_marker :
    decodeG1FrameList?
      [.bof, .tag, .argSep, .argSep, .separator, .cursor, .output false,
        .finish] = none := by
  decide

/-- **Violated unused-field convention.**  `not` is arity-1, so `arg2 = 1` is
not canonical and the pure decoder refuses the word. -/
theorem reject_unused_field :
    decodeG1FrameList? (encodeG1Frames ⟨.not, 0, 1, [true]⟩) = none := by
  decide

/-- **`const` outside the unary bit convention.** -/
theorem reject_const_convention :
    decodeG1FrameList? (encodeG1Frames ⟨.const, 2, 0, []⟩) = none := by
  decide

/-! ## Pure semantics -/

theorem spec_reqInput : reqInput.spec = some false := rfl
theorem spec_reqConst : reqConst.spec = some true := rfl
theorem spec_reqNot : reqNot.spec = some false := rfl
theorem spec_reqAnd : reqAnd.spec = some false := rfl
theorem spec_reqOr : reqOr.spec = some true := rfl

/-! ## The executable capstone, at every tag

Each of these is the exact `TM.runConfig` statement of
`g1CS_validate_rewind_readB_exact`, instantiated at a concrete request of the
given tag: a genuine finite run of the one fixed machine from its real initial
configuration to the `readBStart` handoff at head zero, with the tape
unchanged. -/

/-- The capstone statement, at a concrete request. -/
abbrev CapstoneAt (r : G1Request) : Prop :=
  TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBHandoffSteps r) =
    g1AlignedConfig (encodeG1 r).length 0 (g1_lt_tapeLength (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .readBStart .p0 false false false g1Ctx0

theorem capstone_input : CapstoneAt reqInput :=
  g1CS_validate_rewind_readB_exact reqInput reqInput_canonical

theorem capstone_const : CapstoneAt reqConst :=
  g1CS_validate_rewind_readB_exact reqConst reqConst_canonical

theorem capstone_not : CapstoneAt reqNot :=
  g1CS_validate_rewind_readB_exact reqNot reqNot_canonical

theorem capstone_and : CapstoneAt reqAnd :=
  g1CS_validate_rewind_readB_exact reqAnd reqAnd_canonical

theorem capstone_or : CapstoneAt reqOr :=
  g1CS_validate_rewind_readB_exact reqOr reqOr_canonical

/-- The concrete step count of the `and` example: `2 * 52 + 9`. -/
theorem capstone_and_steps : g1ReadBHandoffSteps reqAnd = 2 * 52 + 9 := by
  simp [g1ReadBHandoffSteps, encodeG1_length, reqAnd, G1Tag.units]

/-- The proved prefix of the `and` example fits the public clock. -/
theorem capstone_and_clock :
    g1ReadBHandoffSteps reqAnd ≤ g1Clock (encodeG1 reqAnd).length :=
  g1ReadBHandoffSteps_le_clock reqAnd

/-! ## Frame-control and machine rejection

Parser rejection alone is not evidence about the machine, so each class below
is witnessed by a genuine automaton or `TM.runConfig` rejection of the *fixed
control*, not only by `decodeG1FrameList? … = none`.

Wrong tag counts are not expressible as `encodeG1Frames r` (`G1Tag.units` is
always `1 … 5`), so those two classes are witnessed at frame-word level; the
operand-convention classes are genuine requests and are witnessed by an exact
TM run. -/

/-- The exact noncanonical rejection statement, at a concrete request: the same
fixed `(encodeG1 r).length + 4`-step validation prefix that accepts a canonical
request lands in the literal reject sink, tape untouched. -/
abbrev RejectAt (r : G1Request) : Prop :=
  (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4)).state.snd = g1RejectState ∧
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape

/-- The matching "validation-prefix endpoint is not the pass-B handoff"
statement. -/
abbrev NotReadBAt (r : G1Request) : Prop :=
  (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      ((encodeG1 r).length + 4)).state.snd ≠ g1ReadBState g1Ctx0

/-! ### Wrong tag count — frame-word witnesses -/

/-- **Zero tag units**, at the automaton: the fixed control rejects the empty
tag run.  The pure parser rejects the same word (`reject_zero_tags`). -/
theorem automaton_reject_zero_tags :
    g1AdvanceList .vBof
        [.bof, .argSep, .argSep, .separator, .output false, .finish, .blank] =
      .reject :=
  g1_reject_tagRun_zero _

/-- **Six tag units**, at the automaton.  The pure parser rejects the same word
(`reject_six_tags`). -/
theorem automaton_reject_six_tags :
    g1AdvanceList .vBof
        [.bof, .tag, .tag, .tag, .tag, .tag, .tag, .argSep, .argSep,
          .separator, .output false, .finish, .blank] = .reject :=
  g1_reject_tagRun_six _

/-! ### Out-of-convention operand fields — exact TM runs -/

/-- `const` with `arg1 = 2`: outside the unary constant-bit convention. -/
def reqConstBig : G1Request := ⟨.const, 2, 0, []⟩

/-- `not` (arity 1) with a non-empty operand-2 field. -/
def reqNotUnused : G1Request := ⟨.not, 0, 1, [true]⟩

/-- `input` (arity 1) with a non-empty operand-2 field. -/
def reqInputUnused : G1Request := ⟨.input, 0, 1, [true]⟩

/-- `const` (arity 1) with a non-empty operand-2 field. -/
def reqConstUnused : G1Request := ⟨.const, 1, 1, []⟩

theorem reqConstBig_not_canonical : ¬ reqConstBig.Canonical := by decide
theorem reqNotUnused_not_canonical : ¬ reqNotUnused.Canonical := by decide
theorem reqInputUnused_not_canonical : ¬ reqInputUnused.Canonical := by decide
theorem reqConstUnused_not_canonical : ¬ reqConstUnused.Canonical := by decide

theorem machine_reject_constBig : RejectAt reqConstBig :=
  g1CS_validate_noncanonical_reject_exact reqConstBig reqConstBig_not_canonical

theorem machine_reject_notUnused : RejectAt reqNotUnused :=
  g1CS_validate_noncanonical_reject_exact reqNotUnused reqNotUnused_not_canonical

theorem machine_reject_inputUnused : RejectAt reqInputUnused :=
  g1CS_validate_noncanonical_reject_exact reqInputUnused
    reqInputUnused_not_canonical

theorem machine_reject_constUnused : RejectAt reqConstUnused :=
  g1CS_validate_noncanonical_reject_exact reqConstUnused
    reqConstUnused_not_canonical

theorem machine_no_handoff_constBig : NotReadBAt reqConstBig :=
  g1CS_noncanonical_ne_readB reqConstBig reqConstBig_not_canonical g1Ctx0

theorem machine_no_handoff_notUnused : NotReadBAt reqNotUnused :=
  g1CS_noncanonical_ne_readB reqNotUnused reqNotUnused_not_canonical g1Ctx0

theorem machine_no_handoff_inputUnused : NotReadBAt reqInputUnused :=
  g1CS_noncanonical_ne_readB reqInputUnused reqInputUnused_not_canonical g1Ctx0

theorem machine_no_handoff_constUnused : NotReadBAt reqConstUnused :=
  g1CS_noncanonical_ne_readB reqConstUnused reqConstUnused_not_canonical g1Ctx0

/-! ### Parser/machine agreement, at concrete words

The general theorem is `g1Automaton_accepts_iff_decode`; these read off the two
directions at concrete words. -/

theorem automaton_accepts_reqAnd :
    g1AdvanceList .vBof (encodeG1Frames reqAnd ++ [.blank]) = .rewindStart :=
  (g1CanonicalEncoderAutomatonTrace_iff reqAnd).mpr reqAnd_canonical

theorem automaton_rejects_reqNotUnused :
    g1AdvanceList .vBof (encodeG1Frames reqNotUnused ++ [.blank]) = .reject :=
  g1AdvanceList_encode_reject reqNotUnused reqNotUnused_not_canonical

/-- The pure parser agrees, on the very same word. -/
theorem parser_rejects_reqNotUnused :
    decodeG1FrameList? (encodeG1Frames reqNotUnused) = none := by
  decide

end G1Examples

end Pnp3.Internal.PsubsetPpoly.TM
