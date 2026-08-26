import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation

/-!
# T1 true uniform-seek surface tests

These compile-time probes pin the canonical codec, the public quadratic clock,
the exact read-only validation/rewind handoff, and the T1b-A1 fixed-control
surfaces: the mutation transition table, the mutation ABI vocabulary, the three
generic-step adapters, and the two idle T1c boundary states.  They deliberately
expose no T1b addressing-success surface: no probe here claims cursor
installation, a unary decrement, the `j → j+1` loop, restoration, output, or
acceptance.

**Coverage discipline.**  Every entry is a `theorem check_*` restating the
pinned statement, never a bare `#check`: existence and elaboration are not
enough, since for the transition-table lemmas the written bit, the head move
and the successor state *are* the content.  The set of pinned declarations is
kept equal to the T1a/T1b-A1 blocks of `Tests/AxiomsAudit.lean`.  Table lemmas
that an audited capstone already consumes (the rewind readers, the forward
readers `p0`–`p2`, `t1Transition_forward_p3_advance`, the sinks and the two
idle-boundary table lemmas) are covered transitively through that capstone's
dependency closure and are not restated again here.
-/

namespace Pnp3.Tests.TMTrueUniformSeekSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

/-! ## Canonical codec, clock and read-only validation/rewind (T1a) -/

theorem check_decodeT1Tape_encode (r : T1Request) :
    decodeT1Tape? (encodeT1 r) = some r :=
  decodeT1Tape_encode r

theorem check_decodeT1Tape?_eq_some {bits : List Bool} {r : T1Request}
    (h : decodeT1Tape? bits = some r) : bits = encodeT1 r :=
  decodeT1Tape?_eq_some h

theorem check_t1CS_runTime (N : Nat) :
    t1CS.toPhased.toTM.runTime N = 128 * (N + 1) ^ 2 + 128 :=
  t1CS_runTime N

theorem check_t1CS_frame_macrostep
    (n h : Nat) (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (mode : T1Mode) (frame : T1Frame)
    (hmode : T1ForwardMode mode)
    (hnext : t1Advance mode frame ≠ .reject)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape mode .p0 false false false latch)
        4 =
      t1AlignedConfig n (h+4) hsafe tape (t1Advance mode frame)
        .p0 false false false latch :=
  t1CS_frame_macrostep n h hsafe tape mode frame hmode hnext hbits latch

theorem check_t1CS_scan_frames
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
        (t1AdvanceList mode frames) .p0 false false false latch :=
  t1CS_scan_frames n pre frames suffix mode hpath hsafe latch

theorem check_t1CanonicalEncoderAutomatonTrace (r : T1Request) :
    T1ValidPath .validateBof (encodeT1Frames r ++ [.blank]) ∧
      t1AdvanceList .validateBof (encodeT1Frames r ++ [.blank]) =
        .rewindStart :=
  t1CanonicalEncoderAutomatonTrace r

theorem check_t1CS_rewind_tail
    (n : Nat) (tail suffix : List T1Frame)
    (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < T1M.tapeLength n) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
          .rewind .p3) (4 * tail.length) =
      t1AlignedConfig n 3 (by omega)
        (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
        .rewind .p3 :=
  t1CS_rewind_tail n tail suffix hne hsafe

theorem check_t1CS_validate_encoded_exact (r : T1Request) :
    let n := (encodeT1 r).length
    TM.runConfig (M := t1CS.toPhased.toTM)
        ((t1CS.toPhased.toTM).initialConfig (t1Point (encodeT1 r))) (n + 4) =
      t1AlignedConfig n (n + 4) (by
        simp [t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength, t1Clock]; omega)
        ((t1CS.toPhased.toTM).initialConfig
          (t1Point (encodeT1 r))).tape .rewindStart :=
  t1CS_validate_encoded_exact r

theorem check_t1CS_validate_rewind_encoded_exact (r : T1Request) :
    let n := (encodeT1 r).length
    TM.runConfig (M := t1CS.toPhased.toTM)
        ((t1CS.toPhased.toTM).initialConfig (t1Point (encodeT1 r)))
        (2 * n + 9) =
      t1AlignedConfig n 0 (by
        simp [t1CS, ConstStatePhasedProgram.toPhased,
          PhasedProgram.toTM, TM.tapeLength])
        ((t1CS.toPhased.toTM).initialConfig
          (t1Point (encodeT1 r))).tape .startMutation :=
  t1CS_validate_rewind_encoded_exact r

/-! ## T1b-A1 cursor-installation table lemmas -/

theorem check_t1Transition_startMutation_active
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .startMutation position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .startMutation .p1 false false false latch
          | .p1 => t1State .startMutation .p2 false false false latch
          | .p2 => t1State .startMutation .p3 false false false latch
          | .p3 => t1State .seekSeparator .p0 false false false latch,
        scan, .right) :=
  t1Transition_startMutation_active phase position b0 b1 b2 latch scan

theorem check_t1Transition_probeData_p0
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .probeData .p0 b0 b1 b2 latch) scan =
      (0, t1State .probeData .p1 scan false false latch, scan, .right) :=
  t1Transition_probeData_p0 phase b0 b1 b2 latch scan

theorem check_t1Transition_probeData_p1
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .probeData .p1 b0 b1 b2 latch) scan =
      (0, t1State .probeData .p2 b0 scan false latch, scan, .right) :=
  t1Transition_probeData_p1 phase b0 b1 b2 latch scan

theorem check_t1Transition_probeData_p2
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .probeData .p2 b0 b1 b2 latch) scan =
      (0, t1State .probeData .p3 b0 b1 scan latch, scan, .right) :=
  t1Transition_probeData_p2 phase b0 b1 b2 latch scan

theorem check_t1Transition_probeData_p3_data
    (phase : Fin 1) (b0 b1 b2 latch scan value : Bool)
    (h : decodeT1Frame? [b0, b1, b2, scan] = some (.data value)) :
    t1Transition phase (t1State .probeData .p3 b0 b1 b2 latch) scan =
      (0, t1State .turnInstall .p0 false false false value, scan, .right) :=
  t1Transition_probeData_p3_data phase b0 b1 b2 latch scan value h

theorem check_t1Transition_probeData_p3_oob
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [b0, b1, b2, scan] = some (.output false)) :
    t1Transition phase (t1State .probeData .p3 b0 b1 b2 latch) scan =
      (0, t1OobState latch, scan, .stay) :=
  t1Transition_probeData_p3_oob phase b0 b1 b2 latch scan h

theorem check_t1Transition_turnInstall
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .turnInstall position b0 b1 b2 latch) scan =
      (0, t1State .writeCursor .p3 false false false latch, scan, .left) :=
  t1Transition_turnInstall phase position b0 b1 b2 latch scan

theorem check_t1Transition_writeCursor
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .writeCursor position b0 b1 b2 latch) scan =
      (0, match position with
          | .p3 => t1State .writeCursor .p2 false false false latch
          | .p2 => t1State .writeCursor .p1 false false false latch
          | .p1 => t1State .writeCursor .p0 false false false latch
          | .p0 => t1State .seekIndexBack .p3 false false false latch,
        match position with
        | .p0 => false
        | _ => true,
        .left) :=
  t1Transition_writeCursor phase position b0 b1 b2 latch scan

/-! ## T1b-A1 index-consumption table lemmas -/

theorem check_t1Transition_seekIndexBack_p3
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .seekIndexBack .p3 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p2 false false scan latch, scan, .left) :=
  t1Transition_seekIndexBack_p3 phase b0 b1 b2 latch scan

theorem check_t1Transition_seekIndexBack_p2
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .seekIndexBack .p2 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p1 false scan b2 latch, scan, .left) :=
  t1Transition_seekIndexBack_p2 phase b0 b1 b2 latch scan

theorem check_t1Transition_seekIndexBack_p1
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .seekIndexBack .p1 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p0 scan b1 b2 latch, scan, .left) :=
  t1Transition_seekIndexBack_p1 phase b0 b1 b2 latch scan

theorem check_t1Transition_seekIndexBack_p0_mark
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some .index) :
    t1Transition phase (t1State .seekIndexBack .p0 b0 b1 b2 latch) scan =
      (0, t1State .markSpent .p0 false false false latch, scan, .stay) :=
  t1Transition_seekIndexBack_p0_mark phase b0 b1 b2 latch scan h

theorem check_t1Transition_seekIndexBack_p0_skip
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) (frame : T1Frame)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some frame)
    (hframe : frame = .spent ∨ frame = .separator ∨ ∃ v, frame = .data v) :
    t1Transition phase (t1State .seekIndexBack .p0 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p3 false false false latch, scan, .left) :=
  t1Transition_seekIndexBack_p0_skip phase b0 b1 b2 latch scan frame h hframe

theorem check_t1Transition_seekIndexBack_p0_success
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some .bof) :
    t1Transition phase (t1State .seekIndexBack .p0 b0 b1 b2 latch) scan =
      (0, t1SuccessState latch, scan, .stay) :=
  t1Transition_seekIndexBack_p0_success phase b0 b1 b2 latch scan h

theorem check_t1Transition_markSpent
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .markSpent position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .markSpent .p1 false false false latch
          | .p1 => t1State .markSpent .p2 false false false latch
          | .p2 => t1State .markSpent .p3 false false false latch
          | .p3 => t1State .seekCursorFwd .p0 false false false latch,
        match position with
        | .p0 => false
        | .p1 => false
        | .p2 => true
        | .p3 => true,
        .right) :=
  t1Transition_markSpent phase position b0 b1 b2 latch scan

/-! ## T1b-A1 cursor-motion table lemmas -/

theorem check_t1Transition_backupCursor
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .backupCursor position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .backupCursor .p1 false false false latch
          | .p1 => t1State .backupCursor .p2 false false false latch
          | .p2 => t1State .backupCursor .p3 false false false latch
          | .p3 => t1State .writeData .p0 false false false latch,
        scan, .left) :=
  t1Transition_backupCursor phase position b0 b1 b2 latch scan

theorem check_t1Transition_writeData
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .writeData position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .writeData .p1 false false false latch
          | .p1 => t1State .writeData .p2 false false false latch
          | .p2 => t1State .writeData .p3 false false false latch
          | .p3 => t1State .probeData .p0 false false false latch,
        match position with
        | .p0 => false
        | .p1 => true
        | .p2 => latch
        | .p3 => !latch,
        .right) :=
  t1Transition_writeData phase position b0 b1 b2 latch scan

/-! ## The forward reader's reject branch -/

theorem check_t1Transition_forward_p3_reject {mode : T1Mode}
    (hmode : T1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (heq : t1Complete mode b0 b1 b2 scan = .reject) :
    t1Transition phase (t1State mode .p3 b0 b1 b2 latch) scan =
      (0, t1RejectState, scan, .stay) :=
  t1Transition_forward_p3_reject hmode phase b0 b1 b2 latch scan heq

/-! ## Mutation ABI vocabulary

The three frame-bit lemmas are what tie the bits written by `writeCursor`,
`markSpent` and `writeData` to the frame ABI of `TrueUniformSeekEncoding`. -/

theorem check_T1Frame_bits_spent :
    T1Frame.spent.bits = [false, false, true, true] :=
  T1Frame.bits_spent

theorem check_T1Frame_bits_cursor :
    T1Frame.cursor.bits = [false, true, true, true] :=
  T1Frame.bits_cursor

theorem check_T1Frame_bits_data (b : Bool) :
    (T1Frame.data b).bits = [false, true, b, !b] :=
  T1Frame.bits_data b

theorem check_t1WriteFrame_ascending (L : Nat) (base : Nat)
    (b0 b1 b2 b3 : Bool) (tape : Fin L → Bool) :
    t1WriteCell (base+3) b3 (t1WriteCell (base+2) b2
        (t1WriteCell (base+1) b1 (t1WriteCell base b0 tape))) =
      t1WriteFrame base [b0, b1, b2, b3] tape :=
  t1WriteFrame_ascending base b0 b1 b2 b3 tape

theorem check_t1WriteFrame_descending (L : Nat) (base : Nat)
    (b0 b1 b2 b3 : Bool) (tape : Fin L → Bool) :
    t1WriteCell base b0 (t1WriteCell (base+1) b1
        (t1WriteCell (base+2) b2 (t1WriteCell (base+3) b3 tape))) =
      t1WriteFrame base [b0, b1, b2, b3] tape :=
  t1WriteFrame_descending base b0 b1 b2 b3 tape

theorem check_t1MutationFrames_length (r : T1Request) (j : Nat)
    (hj : j ≤ r.index) (hdata : j < r.data.length) :
    (t1MutationFrames r j).length = r.index + r.data.length + 4 :=
  t1MutationFrames_length r j hj hdata

theorem check_t1MutationFrames_getElem?_cursor (r : T1Request) (j : Nat)
    (hj : j ≤ r.index) (hdata : j < r.data.length) :
    (t1MutationFrames r j)[t1CursorFrameIndex r j]? = some .cursor :=
  t1MutationFrames_getElem?_cursor r j hj hdata

theorem check_t1MutationFrames_zero (r : T1Request) (b : Bool)
    (rest : List Bool) (hdata : r.data = b :: rest) :
    t1MutationFrames r 0 =
      ([.bof] ++ List.replicate r.index .index ++ [.separator]) ++
        .cursor :: (rest.map .data ++ [.output false, .finish]) :=
  t1MutationFrames_zero r b rest hdata

theorem check_encodeT1Frames_split (r : T1Request) (b : Bool)
    (rest : List Bool) (hdata : r.data = b :: rest) :
    encodeT1Frames r =
      ([.bof] ++ List.replicate r.index .index ++ [.separator]) ++
        .data b :: (rest.map .data ++ [.output false, .finish]) :=
  encodeT1Frames_split r b rest hdata

/-! ## Generic-step adapters and the two idle T1c boundaries -/

theorem check_t1CS_aligned_step_right
    (n h : Nat) (hh : h < T1M.tapeLength n) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, .right)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n (h+1) hb (t1WriteCell h w tape) q' :=
  t1CS_aligned_step_right n h hh hb tape q q' w htr

theorem check_t1CS_aligned_step_left
    (n h : Nat) (hh : h < T1M.tapeLength n) (hpos : 0 < h)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, .left)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n (h-1) (by omega) (t1WriteCell h w tape) q' :=
  t1CS_aligned_step_left n h hh hpos tape q q' w htr

theorem check_t1CS_aligned_step_stay
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State) (w : Bool)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', w, .stay)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n h hh (t1WriteCell h w tape) q' :=
  t1CS_aligned_step_stay n h hh tape q q' w htr

theorem check_t1CS_runConfig_successStart
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .successStart .p0 false false false latch)
        steps =
      t1AlignedConfig n h hh tape .successStart .p0 false false false latch :=
  t1CS_runConfig_successStart n h hh tape latch steps

theorem check_t1CS_runConfig_oobStart
    (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .oobStart .p0 false false false latch)
        steps =
      t1AlignedConfig n h hh tape .oobStart .p0 false false false latch :=
  t1CS_runConfig_oobStart n h hh tape latch steps

end Pnp3.Tests.TMTrueUniformSeekSurface
