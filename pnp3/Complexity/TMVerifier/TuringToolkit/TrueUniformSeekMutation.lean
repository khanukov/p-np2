import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation

/-!
# T1b-A: genuine execution of the destructive seek's opening moves

This module proves real `TM.runConfig` facts about the mutation phase of the
T1 machine, starting from the `startMutation` boundary that T1a's
`t1CS_validate_rewind_encoded_exact` reaches exactly.

Three groups of results:

1. **Atomic macro steps** (`t1CS_startMutation_walk`, `t1CS_probeData_*`,
   `t1CS_turnInstall_step`, `t1CS_writeCursor_frame`, `t1CS_markSpent_frame`,
   `t1CS_seekIndexBack_frame_*`, `t1CS_backupCursor_walk`,
   `t1CS_writeData_frame`).  Each is stated on an explicit aligned
   configuration over an *arbitrary* surrounding tape, so T1b-B can reuse them
   at every loop iteration.  In particular `t1CS_markSpent_frame` is the
   on-tape decrement and `t1CS_writeData_frame` is the cursor restore.

2. **Canonical mutation vocabulary** (`t1MutationFrames` from the encoding
   module, `t1MutationTape`, `t1ListTape_write_frame`).  The `j = 0` layout is
   identified with the tape the genuine installation run produces.  The
   `j → j+1` loop step is *not* claimed here; it is T1b-B's obligation.

3. **Exact execution theorems**: installation of the first cursor for a
   canonical request with nonempty data (`t1CS_install_first_cursor_exact`,
   `t1CS_runConfig_install_first_cursor_exact`), and the empty-data
   out-of-bounds boundary, including a full `TM.run` theorem under the public
   clock (`t1CS_oob_empty_data_exact`, `t1CS_run_encoded_oob_empty_data`).

Every `TM.stepConfig` fact used here comes from a `TrueUniformSeek`
transition-table lemma through the `t1CS_aligned_step_*` adapters, which are
in turn applications of the generic `ConstStatePhasedStepBridge`.  The control
table is never unfolded in this file.

No acceptance, restoration or addressing-success claim is made: `successStart`
and `oobStart` are idle boundaries, and this slice stops at them.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Tape-length and encoder arithmetic helpers -/

theorem t1TapeLength_eq (n : Nat) : T1M.tapeLength n = n + t1Clock n + 1 := rfl

theorem t1_lt_tapeLength (n h : Nat) (hh : h ≤ n) : h < T1M.tapeLength n := by
  have hlen := t1TapeLength_eq n
  omega

private theorem t1EncodeLength_cons (r : T1Request) (b : Bool) (rest : List Bool)
    (hdata : r.data = b :: rest) :
    (encodeT1 r).length = 4 * (r.index + rest.length + 5) := by
  rw [encodeT1_length, hdata]
  simp
  omega

private theorem t1EncodeLength_nil (r : T1Request) (hdata : r.data = []) :
    (encodeT1 r).length = 4 * (r.index + 4) := by
  rw [encodeT1_length, hdata]
  simp

/-! ## Tape-preserving step helpers

Three specialisations of the `t1CS_aligned_step_*` adapters for transitions
that write the scanned bit back, i.e. leave the tape completely unchanged. -/

private theorem t1CS_keep_right (n h : Nat) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, by omega⟩) =
        (0, q', tape ⟨h, by omega⟩, Move.right)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h (by omega) tape q) =
      t1AlignedConfigQ n (h+1) hb tape q' := by
  have hstep := t1CS_aligned_step_right n h (by omega) hb tape q q'
    (tape ⟨h, by omega⟩) htr
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_keep_left (n h : Nat) (hh : h < T1M.tapeLength n)
    (hpos : 0 < h) (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', tape ⟨h, hh⟩, Move.left)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n (h-1) (by omega) tape q' := by
  have hstep := t1CS_aligned_step_left n h hh hpos tape q q' (tape ⟨h, hh⟩) htr
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_keep_stay (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', tape ⟨h, hh⟩, Move.stay)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n h hh tape q' := by
  have hstep := t1CS_aligned_step_stay n h hh tape q q' (tape ⟨h, hh⟩) htr
  rwa [t1WriteCell_self] at hstep

/-! ## Atomic mutation macro steps -/

/-- **Leaving the anchor.**  `startMutation` walks off the `bof` frame in
exactly four steps and enters the index scan.  The tape is untouched and the
latch is carried through.  This is the active replacement for T1a's idle
mutation handoff. -/
theorem t1CS_startMutation_walk (n h : Nat) (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape .startMutation .p0
          false false false latch) 4 =
      t1AlignedConfig n (h+4) hsafe tape .seekSeparator .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n h (by omega) tape .startMutation .p0
        false false false latch) =
      t1AlignedConfig n (h+1) (by omega) tape .startMutation .p1
        false false false latch :=
    t1CS_keep_right n h (by omega) tape
      (t1State .startMutation .p0 false false false latch)
      (t1State .startMutation .p1 false false false latch)
      (fun phase => t1Transition_startMutation_active phase .p0
        false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (h+1) (by omega) tape .startMutation .p1
        false false false latch) =
      t1AlignedConfig n (h+2) (by omega) tape .startMutation .p2
        false false false latch :=
    t1CS_keep_right n (h+1) (by omega) tape
      (t1State .startMutation .p1 false false false latch)
      (t1State .startMutation .p2 false false false latch)
      (fun phase => t1Transition_startMutation_active phase .p1
        false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (h+2) (by omega) tape .startMutation .p2
        false false false latch) =
      t1AlignedConfig n (h+3) (by omega) tape .startMutation .p3
        false false false latch :=
    t1CS_keep_right n (h+2) (by omega) tape
      (t1State .startMutation .p2 false false false latch)
      (t1State .startMutation .p3 false false false latch)
      (fun phase => t1Transition_startMutation_active phase .p2
        false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (h+3) (by omega) tape .startMutation .p3
        false false false latch) =
      t1AlignedConfig n (h+4) hsafe tape .seekSeparator .p0
        false false false latch :=
    t1CS_keep_right n (h+3) hsafe tape
      (t1State .startMutation .p3 false false false latch)
      (t1State .seekSeparator .p0 false false false latch)
      (fun phase => t1Transition_startMutation_active phase .p3
        false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n h (by omega) tape .startMutation .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3]

/-- The first three steps of a `probeData` frame read, shared by the data and
out-of-bounds outcomes. -/
private theorem t1CS_probeData_read (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n base (by omega) tape .probeData .p0
          false false false latch) 3 =
      t1AlignedConfig n (base+3) (by omega) tape .probeData .p3
        (tape ⟨base, by omega⟩) (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .probeData .p0
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega) tape .probeData .p1
        (tape ⟨base, by omega⟩) false false latch :=
    t1CS_keep_right n base (by omega) tape
      (t1State .probeData .p0 false false false latch)
      (t1State .probeData .p1 (tape ⟨base, by omega⟩) false false latch)
      (fun phase => t1Transition_probeData_p0 phase false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .probeData .p1
        (tape ⟨base, by omega⟩) false false latch) =
      t1AlignedConfig n (base+2) (by omega) tape .probeData .p2
        (tape ⟨base, by omega⟩) (tape ⟨base+1, by omega⟩) false latch :=
    t1CS_keep_right n (base+1) (by omega) tape
      (t1State .probeData .p1 (tape ⟨base, by omega⟩) false false latch)
      (t1State .probeData .p2 (tape ⟨base, by omega⟩)
        (tape ⟨base+1, by omega⟩) false latch)
      (fun phase => t1Transition_probeData_p1 phase (tape ⟨base, by omega⟩)
        false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .probeData .p2
        (tape ⟨base, by omega⟩) (tape ⟨base+1, by omega⟩) false latch) =
      t1AlignedConfig n (base+3) (by omega) tape .probeData .p3
        (tape ⟨base, by omega⟩) (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) latch :=
    t1CS_keep_right n (base+2) (by omega) tape
      (t1State .probeData .p2 (tape ⟨base, by omega⟩)
        (tape ⟨base+1, by omega⟩) false latch)
      (t1State .probeData .p3 (tape ⟨base, by omega⟩)
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩) latch)
      (fun phase => t1Transition_probeData_p2 phase (tape ⟨base, by omega⟩)
        (tape ⟨base+1, by omega⟩) false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .probeData .p0
        false false false latch) (1+1+1) = _
  rw [runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2]

private theorem t1CS_frame_decode (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (frame : T1Frame)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) :
    decodeT1Frame? [tape ⟨base, by omega⟩, tape ⟨base+1, by omega⟩,
      tape ⟨base+2, by omega⟩, tape ⟨base+3, by omega⟩] = some frame := by
  simp only [t1PhysicalBitsAt] at hbits
  rw [hbits]
  exact decodeT1Frame_bits frame

/-- **Probing a data frame.**  Four steps latch the frame's value and turn the
control around onto the frame, ready to install the cursor. -/
theorem t1CS_probeData_frame_data (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch value : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = (T1Frame.data value).bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n base (by omega) tape .probeData .p0
          false false false latch) 4 =
      t1AlignedConfig n (base+4) hsafe tape .turnInstall .p0
        false false false value := by
  have hdecode := t1CS_frame_decode n base hsafe tape (.data value) hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .probeData .p3
        (tape ⟨base, by omega⟩) (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) latch) =
      t1AlignedConfig n (base+4) hsafe tape .turnInstall .p0
        false false false value :=
    t1CS_keep_right n (base+3) hsafe tape
      (t1State .probeData .p3 (tape ⟨base, by omega⟩)
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩) latch)
      (t1State .turnInstall .p0 false false false value)
      (fun phase => t1Transition_probeData_p3_data phase _ _ _ latch _ value hdecode)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .probeData .p0
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_probeData_read n base hsafe tape latch,
    runConfig_one, hs3]

/-- **Probing the output frame.**  The data field is exhausted: four steps
reach the out-of-bounds boundary with the tape completely unchanged. -/
theorem t1CS_probeData_frame_oob (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = (T1Frame.output false).bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n base (by omega) tape .probeData .p0
          false false false latch) 4 =
      t1AlignedConfig n (base+3) (by omega) tape .oobStart .p0
        false false false latch := by
  have hdecode := t1CS_frame_decode n base hsafe tape (.output false) hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .probeData .p3
        (tape ⟨base, by omega⟩) (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) latch) =
      t1AlignedConfig n (base+3) (by omega) tape .oobStart .p0
        false false false latch :=
    t1CS_keep_stay n (base+3) (by omega) tape
      (t1State .probeData .p3 (tape ⟨base, by omega⟩)
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩) latch)
      (t1OobState latch)
      (fun phase => t1Transition_probeData_p3_oob phase _ _ _ latch _ hdecode)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .probeData .p0
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_probeData_read n base hsafe tape latch,
    runConfig_one, hs3]

/-- One step turns the control around onto the frame just probed. -/
theorem t1CS_turnInstall_step (n h : Nat) (hpos : 0 < h)
    (hh : h < T1M.tapeLength n) (tape : Fin (T1M.tapeLength n) → Bool)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .turnInstall .p0
          false false false latch) 1 =
      t1AlignedConfig n (h-1) (by omega) tape .writeCursor .p3
        false false false latch := by
  rw [runConfig_one]
  exact t1CS_keep_left n h hh hpos tape
    (t1State .turnInstall .p0 false false false latch)
    (t1State .writeCursor .p3 false false false latch)
    (fun phase => t1Transition_turnInstall phase .p0 false false false latch _)

/-- **Cursor installation.**  Four right-to-left steps overwrite the frame at
`base` with the `cursor` marker and leave the control on the last cell of the
preceding frame, in the backward index scan. -/
theorem t1CS_writeCursor_frame (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .writeCursor .p3
          false false false latch) 4 =
      t1AlignedConfig n (base-1) (by omega)
        (t1WriteFrame base T1Frame.cursor.bits tape) .seekIndexBack .p3
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .writeCursor .p3
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+3) true tape) .writeCursor .p2
        false false false latch := by
    simpa using t1CS_aligned_step_left n (base+3) (by omega) (by omega) tape
      (t1State .writeCursor .p3 false false false latch)
      (t1State .writeCursor .p2 false false false latch) true
      (fun phase => t1Transition_writeCursor phase .p3 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+3) true tape) .writeCursor .p2
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell (base+2) true (t1WriteCell (base+3) true tape))
        .writeCursor .p1 false false false latch := by
    simpa using t1CS_aligned_step_left n (base+2) (by omega) (by omega)
      (t1WriteCell (base+3) true tape)
      (t1State .writeCursor .p2 false false false latch)
      (t1State .writeCursor .p1 false false false latch) true
      (fun phase => t1Transition_writeCursor phase .p2 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell (base+2) true (t1WriteCell (base+3) true tape))
        .writeCursor .p1 false false false latch) =
      t1AlignedConfig n base (by omega)
        (t1WriteCell (base+1) true
          (t1WriteCell (base+2) true (t1WriteCell (base+3) true tape)))
        .writeCursor .p0 false false false latch := by
    simpa using t1CS_aligned_step_left n (base+1) (by omega) (by omega)
      (t1WriteCell (base+2) true (t1WriteCell (base+3) true tape))
      (t1State .writeCursor .p1 false false false latch)
      (t1State .writeCursor .p0 false false false latch) true
      (fun phase => t1Transition_writeCursor phase .p1 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega)
        (t1WriteCell (base+1) true
          (t1WriteCell (base+2) true (t1WriteCell (base+3) true tape)))
        .writeCursor .p0 false false false latch) =
      t1AlignedConfig n (base-1) (by omega)
        (t1WriteCell base false (t1WriteCell (base+1) true
          (t1WriteCell (base+2) true (t1WriteCell (base+3) true tape))))
        .seekIndexBack .p3 false false false latch :=
    t1CS_aligned_step_left n base (by omega) hpos
      (t1WriteCell (base+1) true
        (t1WriteCell (base+2) true (t1WriteCell (base+3) true tape)))
      (t1State .writeCursor .p0 false false false latch)
      (t1State .seekIndexBack .p3 false false false latch) false
      (fun phase => t1Transition_writeCursor phase .p0 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .writeCursor .p3
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3, t1WriteFrame_descending, T1Frame.bits_cursor]

/-- **The on-tape decrement.**  Four left-to-right steps overwrite the `index`
frame at `base` with the `spent` marker and hand over to the forward cursor
search.  Reusable at every loop iteration. -/
theorem t1CS_markSpent_frame (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n base (by omega) tape .markSpent .p0
          false false false latch) 4 =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteFrame base T1Frame.spent.bits tape) .seekCursorFwd .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .markSpent .p0
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .markSpent .p1
        false false false latch :=
    t1CS_aligned_step_right n base (by omega) (by omega) tape
      (t1State .markSpent .p0 false false false latch)
      (t1State .markSpent .p1 false false false latch) false
      (fun phase => t1Transition_markSpent phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .markSpent .p1
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) false (t1WriteCell base false tape))
        .markSpent .p2 false false false latch :=
    t1CS_aligned_step_right n (base+1) (by omega) (by omega)
      (t1WriteCell base false tape)
      (t1State .markSpent .p1 false false false latch)
      (t1State .markSpent .p2 false false false latch) false
      (fun phase => t1Transition_markSpent phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) false (t1WriteCell base false tape))
        .markSpent .p2 false false false latch) =
      t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) true
          (t1WriteCell (base+1) false (t1WriteCell base false tape)))
        .markSpent .p3 false false false latch :=
    t1CS_aligned_step_right n (base+2) (by omega) (by omega)
      (t1WriteCell (base+1) false (t1WriteCell base false tape))
      (t1State .markSpent .p2 false false false latch)
      (t1State .markSpent .p3 false false false latch) true
      (fun phase => t1Transition_markSpent phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) true
          (t1WriteCell (base+1) false (t1WriteCell base false tape)))
        .markSpent .p3 false false false latch) =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteCell (base+3) true (t1WriteCell (base+2) true
          (t1WriteCell (base+1) false (t1WriteCell base false tape))))
        .seekCursorFwd .p0 false false false latch :=
    t1CS_aligned_step_right n (base+3) (by omega) hsafe
      (t1WriteCell (base+2) true
        (t1WriteCell (base+1) false (t1WriteCell base false tape)))
      (t1State .markSpent .p3 false false false latch)
      (t1State .seekCursorFwd .p0 false false false latch) true
      (fun phase => t1Transition_markSpent phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .markSpent .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3, t1WriteFrame_ascending, T1Frame.bits_spent]

/-- Four steps back onto the cursor frame, ready to restore it. -/
theorem t1CS_backupCursor_walk (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+4) hsafe tape .backupCursor .p0
          false false false latch) 4 =
      t1AlignedConfig n base (by omega) tape .writeData .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+4) hsafe tape .backupCursor .p0
        false false false latch) =
      t1AlignedConfig n (base+3) (by omega) tape .backupCursor .p1
        false false false latch := by
    simpa using t1CS_keep_left n (base+4) hsafe (by omega) tape
      (t1State .backupCursor .p0 false false false latch)
      (t1State .backupCursor .p1 false false false latch)
      (fun phase => t1Transition_backupCursor phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .backupCursor .p1
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega) tape .backupCursor .p2
        false false false latch := by
    simpa using t1CS_keep_left n (base+3) (by omega) (by omega) tape
      (t1State .backupCursor .p1 false false false latch)
      (t1State .backupCursor .p2 false false false latch)
      (fun phase => t1Transition_backupCursor phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .backupCursor .p2
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega) tape .backupCursor .p3
        false false false latch := by
    simpa using t1CS_keep_left n (base+2) (by omega) (by omega) tape
      (t1State .backupCursor .p2 false false false latch)
      (t1State .backupCursor .p3 false false false latch)
      (fun phase => t1Transition_backupCursor phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .backupCursor .p3
        false false false latch) =
      t1AlignedConfig n base (by omega) tape .writeData .p0
        false false false latch := by
    simpa using t1CS_keep_left n (base+1) (by omega) (by omega) tape
      (t1State .backupCursor .p3 false false false latch)
      (t1State .writeData .p0 false false false latch)
      (fun phase => t1Transition_backupCursor phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+4) hsafe tape .backupCursor .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3]

/-- **The cursor restore.**  Four left-to-right steps overwrite the frame at
`base` with the latched data frame and hand over to the next probe.  Reusable
at every loop iteration. -/
theorem t1CS_writeData_frame (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n base (by omega) tape .writeData .p0
          false false false latch) 4 =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteFrame base (T1Frame.data latch).bits tape) .probeData .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .writeData .p0
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .writeData .p1
        false false false latch :=
    t1CS_aligned_step_right n base (by omega) (by omega) tape
      (t1State .writeData .p0 false false false latch)
      (t1State .writeData .p1 false false false latch) false
      (fun phase => t1Transition_writeData phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .writeData .p1
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) true (t1WriteCell base false tape))
        .writeData .p2 false false false latch :=
    t1CS_aligned_step_right n (base+1) (by omega) (by omega)
      (t1WriteCell base false tape)
      (t1State .writeData .p1 false false false latch)
      (t1State .writeData .p2 false false false latch) true
      (fun phase => t1Transition_writeData phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) true (t1WriteCell base false tape))
        .writeData .p2 false false false latch) =
      t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) latch
          (t1WriteCell (base+1) true (t1WriteCell base false tape)))
        .writeData .p3 false false false latch :=
    t1CS_aligned_step_right n (base+2) (by omega) (by omega)
      (t1WriteCell (base+1) true (t1WriteCell base false tape))
      (t1State .writeData .p2 false false false latch)
      (t1State .writeData .p3 false false false latch) latch
      (fun phase => t1Transition_writeData phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) latch
          (t1WriteCell (base+1) true (t1WriteCell base false tape)))
        .writeData .p3 false false false latch) =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteCell (base+3) (!latch) (t1WriteCell (base+2) latch
          (t1WriteCell (base+1) true (t1WriteCell base false tape))))
        .probeData .p0 false false false latch :=
    t1CS_aligned_step_right n (base+3) (by omega) hsafe
      (t1WriteCell (base+2) latch
        (t1WriteCell (base+1) true (t1WriteCell base false tape)))
      (t1State .writeData .p3 false false false latch)
      (t1State .probeData .p0 false false false latch) (!latch)
      (fun phase => t1Transition_writeData phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .writeData .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3, t1WriteFrame_ascending, T1Frame.bits_data]

/-! ### The backward index scan -/

/-- The first three steps of a `seekIndexBack` frame read. -/
private theorem t1CS_seekIndexBack_read (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
          false false false latch) 3 =
      t1AlignedConfig n base (by omega) tape .seekIndexBack .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega) tape .seekIndexBack .p2
        false false (tape ⟨base+3, by omega⟩) latch := by
    simpa using t1CS_keep_left n (base+3) (by omega) (by omega) tape
      (t1State .seekIndexBack .p3 false false false latch)
      (t1State .seekIndexBack .p2 false false (tape ⟨base+3, by omega⟩) latch)
      (fun phase => t1Transition_seekIndexBack_p3 phase false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .seekIndexBack .p2
        false false (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n (base+1) (by omega) tape .seekIndexBack .p1
        false (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch := by
    simpa using t1CS_keep_left n (base+2) (by omega) (by omega) tape
      (t1State .seekIndexBack .p2 false false (tape ⟨base+3, by omega⟩) latch)
      (t1State .seekIndexBack .p1 false (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch)
      (fun phase => t1Transition_seekIndexBack_p2 phase false false
        (tape ⟨base+3, by omega⟩) latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .seekIndexBack .p1
        false (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n base (by omega) tape .seekIndexBack .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch := by
    simpa using t1CS_keep_left n (base+1) (by omega) (by omega) tape
      (t1State .seekIndexBack .p1 false (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch)
      (t1State .seekIndexBack .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (fun phase => t1Transition_seekIndexBack_p1 phase false
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
        false false false latch) (1+1+1) = _
  rw [runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2]

/-- Backward scan across a skipped frame (`spent`, `separator` or data): four
steps, tape unchanged, head on the last cell of the preceding frame. -/
theorem t1CS_seekIndexBack_frame_skip (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) (frame : T1Frame)
    (hframe : frame = .spent ∨ frame = .separator ∨ ∃ v, frame = .data v)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
          false false false latch) 4 =
      t1AlignedConfig n (base-1) (by omega) tape .seekIndexBack .p3
        false false false latch := by
  have hdecode := t1CS_frame_decode n base hsafe tape frame hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .seekIndexBack .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n (base-1) (by omega) tape .seekIndexBack .p3
        false false false latch :=
    t1CS_keep_left n base (by omega) hpos tape
      (t1State .seekIndexBack .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (t1State .seekIndexBack .p3 false false false latch)
      (fun phase => t1Transition_seekIndexBack_p0_skip phase _ _ _ latch _
        frame hdecode hframe)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_seekIndexBack_read n base hsafe tape latch,
    runConfig_one, hs3]

/-- Backward scan onto the rightmost unconsumed `index` frame: four steps,
tape unchanged, control handed to the on-tape decrement at the frame's first
cell. -/
theorem t1CS_seekIndexBack_frame_mark (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = T1Frame.index.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
          false false false latch) 4 =
      t1AlignedConfig n base (by omega) tape .markSpent .p0
        false false false latch := by
  have hdecode := t1CS_frame_decode n base hsafe tape .index hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .seekIndexBack .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n base (by omega) tape .markSpent .p0
        false false false latch :=
    t1CS_keep_stay n base (by omega) tape
      (t1State .seekIndexBack .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (t1State .markSpent .p0 false false false latch)
      (fun phase => t1Transition_seekIndexBack_p0_mark phase _ _ _ latch _ hdecode)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_seekIndexBack_read n base hsafe tape latch,
    runConfig_one, hs3]

/-- Backward scan onto the `bof` anchor: every index unit has been consumed,
so four steps reach the idle success boundary with the latch intact. -/
theorem t1CS_seekIndexBack_frame_success (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = T1Frame.bof.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
          false false false latch) 4 =
      t1AlignedConfig n base (by omega) tape .successStart .p0
        false false false latch := by
  have hdecode := t1CS_frame_decode n base hsafe tape .bof hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .seekIndexBack .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n base (by omega) tape .successStart .p0
        false false false latch :=
    t1CS_keep_stay n base (by omega) tape
      (t1State .seekIndexBack .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (t1SuccessState latch)
      (fun phase => t1Transition_seekIndexBack_p0_success phase _ _ _ latch _ hdecode)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .seekIndexBack .p3
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_seekIndexBack_read n base hsafe tape latch,
    runConfig_one, hs3]

/-! ## Canonical mutation tape vocabulary -/

private theorem t1GetD_append_left {α : Type} (l₁ l₂ : List α) (d : α) :
    ∀ i, i < l₁.length → (l₁ ++ l₂).getD i d = l₁.getD i d := by
  intro i
  induction l₁ generalizing i with
  | nil => intro h; simp at h
  | cons a t ih =>
      intro h
      cases i with
      | zero => rfl
      | succ i =>
          have hrest := ih i (by simpa using h)
          simpa [List.getD, List.getElem?_cons_succ] using hrest

private theorem t1GetD_append_right {α : Type} (l₁ l₂ : List α) (d : α) :
    ∀ i, l₁.length ≤ i → (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  intro i
  induction l₁ generalizing i with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      cases i with
      | zero => simp at h
      | succ i =>
          have hrest := ih i (by simpa using h)
          simpa [List.getD, List.getElem?_cons_succ] using hrest

/-- **Replacing one frame of a list-backed tape is a single frame write.**
This is the bridge between the frame-list vocabulary the T1b invariants are
stated in and the cell-level `t1WriteFrame` the execution theorems produce. -/
theorem t1ListTape_write_frame (n : Nat) (pre suf : List T1Frame)
    (f f' : T1Frame) :
    t1ListTape (n := n) ((pre ++ f' :: suf).flatMap T1Frame.bits) =
      t1WriteFrame (4 * pre.length) f'.bits
        (t1ListTape (n := n) ((pre ++ f :: suf).flatMap T1Frame.bits)) := by
  funext i
  have hP : (pre.flatMap T1Frame.bits).length = 4 * pre.length :=
    T1Frame.flatMap_bits_length pre
  have hf : f.bits.length = 4 := T1Frame.bits_length f
  have hf' : f'.bits.length = 4 := T1Frame.bits_length f'
  simp only [t1ListTape, t1WriteFrame, List.flatMap_append, List.flatMap_cons]
  by_cases hlt : (i : Nat) < 4 * pre.length
  · have hcond : ¬ (4 * pre.length ≤ (i : Nat) ∧ (i : Nat) < 4 * pre.length + 4) := by
      omega
    rw [if_neg hcond,
      t1GetD_append_left _ _ _ _ (by omega),
      t1GetD_append_left _ _ _ _ (by omega)]
  · by_cases hin : (i : Nat) < 4 * pre.length + 4
    · rw [if_pos ⟨by omega, hin⟩,
        t1GetD_append_right _ _ _ _ (by omega),
        t1GetD_append_left _ _ _ _ (by omega), hP]
    · rw [if_neg (by omega),
        t1GetD_append_right _ _ _ _ (by omega),
        t1GetD_append_right _ _ _ _ (by omega),
        t1GetD_append_right _ _ _ _ (by omega),
        t1GetD_append_right _ _ _ _ (by omega), hf, hf']

/-- The canonical mutation tape after `j` on-tape decrements: the frame layout
`t1MutationFrames r j`, followed by the observable blank frame. -/
def t1MutationTape (n : Nat) (r : T1Request) (j : Nat) :
    Fin (T1M.tapeLength n) → Bool :=
  t1ListTape ((t1MutationFrames r j ++ [T1Frame.blank]).flatMap T1Frame.bits)

/-- **The `j = 0` mutation layout is what the machine actually writes.**  The
canonical vocabulary tape after zero decrements is the initial tape with the
first data frame overwritten by the cursor marker — exactly the tape produced
by `t1CS_install_first_cursor_exact` below. -/
theorem t1MutationTape_zero (r : T1Request) (b : Bool) (rest : List Bool)
    (hdata : r.data = b :: rest) :
    t1MutationTape (encodeT1 r).length r 0 =
      t1WriteFrame (4 * (r.index + 2)) T1Frame.cursor.bits
        (T1M.initialConfig (t1Point (encodeT1 r))).tape := by
  have hpre : ([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
      [T1Frame.separator]).length = r.index + 2 := by simp
  have hzero : t1MutationFrames r 0 ++ [T1Frame.blank] =
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
        [T1Frame.separator]) ++
        T1Frame.cursor ::
          (rest.map T1Frame.data ++
            [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
    rw [t1MutationFrames_zero r b rest hdata]
    simp [List.append_assoc]
  have hval : t1ValidationFrames r =
      ([T1Frame.bof] ++ List.replicate r.index T1Frame.index ++
        [T1Frame.separator]) ++
        T1Frame.data b ::
          (rest.map T1Frame.data ++
            [T1Frame.output false, T1Frame.finish, T1Frame.blank]) := by
    rw [t1ValidationFrames, encodeT1Frames_split r b rest hdata]
    simp [List.append_assoc]
  rw [← t1ListTape_validation_eq_initial r, t1MutationTape, hzero, hval,
    t1ListTape_write_frame _ _ _ (T1Frame.data b), hpre]

/-! ## Exact execution theorems -/

private theorem t1SeekSeparator_path (k : Nat) :
    T1ValidPath .seekSeparator (List.replicate k .index ++ [.separator]) := by
  induction k with
  | zero => simp [T1ValidPath, T1ForwardMode, t1Advance]
  | succ j ih =>
      simpa [List.replicate_succ, T1ValidPath, T1ForwardMode, t1Advance] using ih

private theorem t1SeekSeparator_advance (k : Nat) :
    t1AdvanceList .seekSeparator (List.replicate k .index ++ [.separator]) =
      .probeData := by
  induction k with
  | zero => rfl
  | succ j ih => simpa [List.replicate_succ, t1AdvanceList, t1Advance] using ih

/-- The index-field scan, on the canonical validation tape: from the first
`index` frame to the first data position in exactly `4 * (k+1)` steps. -/
private theorem t1CS_seekSeparator_scan (r : T1Request) (suffix : List T1Frame)
    (hframes : t1ValidationFrames r =
      [T1Frame.bof] ++ (List.replicate r.index .index ++ [.separator]) ++ suffix)
    (hsafe : 4 * (1 + (r.index + 1)) < T1M.tapeLength (encodeT1 r).length) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length 4 (by omega)
          (t1ListTape ((t1ValidationFrames r).flatMap T1Frame.bits))
          .seekSeparator .p0 false false false false)
        (4 * (r.index + 1)) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2)) (by omega)
        (t1ListTape ((t1ValidationFrames r).flatMap T1Frame.bits))
        .probeData .p0 false false false false := by
  have hscan := t1CS_scan_frames (encodeT1 r).length [T1Frame.bof]
    (List.replicate r.index .index ++ [.separator]) suffix .seekSeparator
    (t1SeekSeparator_path r.index) (by simpa using hsafe) false
  rw [← hframes] at hscan
  rw [t1SeekSeparator_advance] at hscan
  simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hscan

/-- **Exact cursor installation.**  From the `startMutation` boundary, a
canonical request with nonempty data installs the cursor on the first data
frame in exactly `4 * index + 17` genuine TM steps: the tape is the initial
tape with that one frame rewritten, the head sits on the last cell of the
separator frame, the control is in the backward index scan, and the latch
holds the first data bit. -/
theorem t1CS_install_first_cursor_exact (r : T1Request) (b : Bool)
    (rest : List Bool) (hdata : r.data = b :: rest) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length 0
          (t1_lt_tapeLength _ _ (by omega))
          (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation)
        (4 * r.index + 17) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) - 1)
        (t1_lt_tapeLength _ _
          (by rw [t1EncodeLength_cons r b rest hdata]; omega))
        (t1WriteFrame (4 * (r.index + 2)) T1Frame.cursor.bits
          (T1M.initialConfig (t1Point (encodeT1 r))).tape)
        .seekIndexBack .p3 false false false b := by
  have hlen := t1EncodeLength_cons r b rest hdata
  have hL : (encodeT1 r).length < T1M.tapeLength (encodeT1 r).length :=
    t1_lt_tapeLength _ _ (by omega)
  have hframes : t1ValidationFrames r =
      [T1Frame.bof] ++ (List.replicate r.index .index ++ [.separator]) ++
        (T1Frame.data b :: (rest.map .data ++ [.output false, .finish, .blank])) := by
    rw [t1ValidationFrames, encodeT1Frames_split r b rest hdata]
    simp [List.append_assoc]
  set T := t1ListTape (n := (encodeT1 r).length)
    ((t1ValidationFrames r).flatMap T1Frame.bits) with hT
  have hinit : (T1M.initialConfig (t1Point (encodeT1 r))).tape = T := by
    rw [hT, t1ListTape_validation_eq_initial r]
  have hcursorSafe : 4 * (r.index + 2) + 4 < T1M.tapeLength (encodeT1 r).length := by
    omega
  have hdataBits : t1PhysicalBitsAt hcursorSafe T = (T1Frame.data b).bits := by
    have hraw := t1PhysicalBitsAt_flatMap (encodeT1 r).length
      ([T1Frame.bof] ++ (List.replicate r.index .index ++ [.separator]))
      (rest.map .data ++ [.output false, .finish, .blank]) (T1Frame.data b)
      (by simpa using hcursorSafe)
    rw [hT, hframes]
    convert hraw using 2
    simp
  rw [hinit]
  rw [show 4 * r.index + 17 = 4 + (4 * (r.index + 1) + (4 + (1 + 4))) by omega]
  rw [runConfig_add, t1CS_startMutation_walk (encodeT1 r).length 0 (by omega) T false]
  rw [runConfig_add, t1CS_seekSeparator_scan r
    (T1Frame.data b :: (rest.map .data ++ [.output false, .finish, .blank]))
    hframes (by omega)]
  rw [runConfig_add, t1CS_probeData_frame_data (encodeT1 r).length
    (4 * (r.index + 2)) hcursorSafe T false b hdataBits]
  have hturn : TM.runConfig (M := T1M)
      (t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 4) (by omega) T
        .turnInstall .p0 false false false b) 1 =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3) (by omega) T
        .writeCursor .p3 false false false b := by
    simpa using t1CS_turnInstall_step (encodeT1 r).length
      (4 * (r.index + 2) + 4) (by omega) (by omega) T b
  rw [runConfig_add, hturn]
  rw [t1CS_writeCursor_frame (encodeT1 r).length (4 * (r.index + 2))
    (by omega) hcursorSafe T b]

/-- The same installation, from the genuine initial configuration: validation,
rewind and installation together take exactly `2n + 9 + 4 * index + 17`
steps. -/
theorem t1CS_runConfig_install_first_cursor_exact (r : T1Request) (b : Bool)
    (rest : List Bool) (hdata : r.data = b :: rest) :
    TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
        (2 * (encodeT1 r).length + 9 + (4 * r.index + 17)) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) - 1)
        (t1_lt_tapeLength _ _
          (by rw [t1EncodeLength_cons r b rest hdata]; omega))
        (t1WriteFrame (4 * (r.index + 2)) T1Frame.cursor.bits
          (T1M.initialConfig (t1Point (encodeT1 r))).tape)
        .seekIndexBack .p3 false false false b := by
  rw [runConfig_add]
  have hval := t1CS_validate_rewind_encoded_exact r
  simp only at hval
  rw [hval]
  exact t1CS_install_first_cursor_exact r b rest hdata

/-- **Exact empty-data out-of-bounds boundary.**  When the data field is
empty, the probe of the first data position finds the output frame instead:
from `startMutation`, the machine reaches the idle out-of-bounds boundary in
exactly `4 * index + 12` steps with the entire tape unchanged. -/
theorem t1CS_oob_empty_data_exact (r : T1Request) (hdata : r.data = []) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig (encodeT1 r).length 0
          (t1_lt_tapeLength _ _ (by omega))
          (T1M.initialConfig (t1Point (encodeT1 r))).tape .startMutation)
        (4 * r.index + 12) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
        (t1_lt_tapeLength _ _
          (by rw [t1EncodeLength_nil r hdata]; omega))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
        false false false false := by
  have hlen := t1EncodeLength_nil r hdata
  have hframes : t1ValidationFrames r =
      [T1Frame.bof] ++ (List.replicate r.index .index ++ [.separator]) ++
        (T1Frame.output false :: [.finish, .blank]) := by
    rw [t1ValidationFrames, encodeT1Frames, hdata]
    simp [List.append_assoc]
  set T := t1ListTape (n := (encodeT1 r).length)
    ((t1ValidationFrames r).flatMap T1Frame.bits) with hT
  have hinit : (T1M.initialConfig (t1Point (encodeT1 r))).tape = T := by
    rw [hT, t1ListTape_validation_eq_initial r]
  have houtSafe : 4 * (r.index + 2) + 4 < T1M.tapeLength (encodeT1 r).length := by
    have := t1_lt_tapeLength (encodeT1 r).length (encodeT1 r).length (le_refl _)
    omega
  have houtBits : t1PhysicalBitsAt houtSafe T = (T1Frame.output false).bits := by
    have hraw := t1PhysicalBitsAt_flatMap (encodeT1 r).length
      ([T1Frame.bof] ++ (List.replicate r.index .index ++ [.separator]))
      [T1Frame.finish, .blank] (T1Frame.output false)
      (by simpa using houtSafe)
    rw [hT, hframes]
    convert hraw using 2
    simp
  rw [hinit]
  rw [show 4 * r.index + 12 = 4 + (4 * (r.index + 1) + 4) by omega]
  rw [runConfig_add, t1CS_startMutation_walk (encodeT1 r).length 0 (by omega) T false]
  rw [runConfig_add, t1CS_seekSeparator_scan r
    (T1Frame.output false :: [.finish, .blank]) hframes (by omega)]
  rw [t1CS_probeData_frame_oob (encodeT1 r).length (4 * (r.index + 2))
    houtSafe T false houtBits]

/-- **Empty-data out-of-bounds under the public clock.**  A canonical request
with no data frames runs to the idle out-of-bounds boundary and stays there:
the machine's whole `TM.run` is that configuration, and the tape is exactly
the input tape.  This is a genuine full-clock execution theorem; it is not an
acceptance or rejection claim, since T1c owns the recovery and the sinks. -/
theorem t1CS_run_encoded_oob_empty_data (r : T1Request) (hdata : r.data = []) :
    T1M.run (t1Point (encodeT1 r)) =
      t1AlignedConfig (encodeT1 r).length (4 * (r.index + 2) + 3)
        (t1_lt_tapeLength _ _
          (by rw [t1EncodeLength_nil r hdata]; omega))
        (T1M.initialConfig (t1Point (encodeT1 r))).tape .oobStart .p0
        false false false false := by
  have hlen := t1EncodeLength_nil r hdata
  set N := (encodeT1 r).length with hN
  have hsq : N + 1 ≤ (N + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right (N + 1) (by omega)
  have hle : 3 * N + 5 ≤ t1Clock N := by
    calc
      3 * N + 5 ≤ 128 * (N + 1) + 128 := by omega
      _ ≤ 128 * (N + 1) ^ 2 + 128 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 128 hsq) 128
      _ = t1Clock N := rfl
  have hsplit : t1Clock N =
      (2 * N + 9) + (4 * r.index + 12) + (t1Clock N - (3 * N + 5)) := by
    omega
  rw [TM.run]
  change TM.runConfig (M := T1M) (T1M.initialConfig (t1Point (encodeT1 r)))
      (t1Clock N) = _
  rw [hsplit, runConfig_add, runConfig_add]
  have hval := t1CS_validate_rewind_encoded_exact r
  simp only at hval
  rw [hval, t1CS_oob_empty_data_exact r hdata]
  exact t1CS_runConfig_oobStart _ _ _ _ false _

end Pnp3.Internal.PsubsetPpoly.TM
