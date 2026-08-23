import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation

/-!
# T1c-1: entering the terminal arms

T1b left the machine at one of two boundary states, `successStart` (every
index unit consumed, head on the first cell of the `bof` anchor, latch holding
the selected data value) or `oobStart` (the data field ran out, head on the
last cell of the output frame).  Both were idle.  T1c-1 activates them and
fixes the whole terminal control; this module is the *execution* companion:
one genuine `TM.runConfig` theorem per new mode, obtained — like every step
fact in this development — by feeding a standalone transition-table lemma of
`TrueUniformSeek` to a generic `ConstStatePhasedStepBridge` adapter.  The
control table is never unfolded here.

## Scope

Every theorem below is a *generic* statement about an arbitrary tape at an
arbitrary safe head position.  Together they cover both terminal arms
mode-by-mode:

* success arm — `t1CS_successStart_dispatch`, `t1CS_outWalk_walk`,
  `t1CS_outSeekCursor_frame`, `t1CS_outBackup_walk`,
  `t1CS_outWriteData_frame`, `t1CS_outSeekOutput_frame`,
  `t1CS_outTurn_step`, `t1CS_outWriteOut_frame`;
* shared repair — `t1CS_oobStart_dispatch`, `t1CS_repairSeek_frame_skip`,
  `t1CS_repairSeek_frame_write`, `t1CS_repairSeek_frame_done`,
  `t1CS_repairWrite_frame`, `t1CS_repairBack_walk`, `t1CS_repairHop_step`;
* dispatch — `t1CS_repairDone_accept`, `t1CS_repairDone_reject`.

What is **not** here, and is the whole content of T1c-2: the composite traces
that chain these macro steps along a canonical tape, the terminal step counts,
the conservation statement (`spent ↦ index` everywhere, exactly one output
cell changed), the padding of `t1Clock` through the sinks, and the acceptance
`iff`.  Nothing below claims that the machine reaches a sink on any concrete
input.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Tape-preserving step helpers

The same three specialisations of the `t1CS_aligned_step_*` adapters that the
mutation slice uses, for transitions writing the scanned bit back. -/

private theorem t1CS_hold_right (n h : Nat) (hb : h + 1 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, by omega⟩) =
        (0, q', tape ⟨h, by omega⟩, Move.right)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h (by omega) tape q) =
      t1AlignedConfigQ n (h+1) hb tape q' := by
  have hstep := t1CS_aligned_step_right n h (by omega) hb tape q q'
    (tape ⟨h, by omega⟩) htr
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_hold_left (n h : Nat) (hh : h < T1M.tapeLength n)
    (hpos : 0 < h) (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', tape ⟨h, hh⟩, Move.left)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n (h-1) (by omega) tape q' := by
  have hstep := t1CS_aligned_step_left n h hh hpos tape q q' (tape ⟨h, hh⟩) htr
  rwa [t1WriteCell_self] at hstep

private theorem t1CS_hold_stay (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (q q' : T1State)
    (htr : ∀ phase : Fin 1,
      t1Transition phase q (tape ⟨h, hh⟩) = (0, q', tape ⟨h, hh⟩, Move.stay)) :
    TM.stepConfig (M := T1M) (t1AlignedConfigQ n h hh tape q) =
      t1AlignedConfigQ n h hh tape q' := by
  have hstep := t1CS_aligned_step_stay n h hh tape q q' (tape ⟨h, hh⟩) htr
  rwa [t1WriteCell_self] at hstep

/-! ## Entering the two arms -/

/-- **The success boundary fires.**  One genuine step hands the latched data
value to the output arm.  The head does not move — it is still on the first
cell of the `bof` anchor — and the tape is untouched. -/
theorem t1CS_successStart_dispatch (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .successStart .p0
          false false false latch) 1 =
      t1AlignedConfig n h hh tape .outWalk .p0 false false false latch := by
  rw [runConfig_one]
  exact t1CS_hold_stay n h hh tape
    (t1State .successStart .p0 false false false latch)
    (t1State .outWalk .p0 false false false latch)
    (fun phase => t1Transition_successStart_active phase .p0
      false false false latch _)

/-- **The out-of-bounds boundary fires.**  One genuine step enters the shared
repair pass with the latch cleared to the reject tag.  The head already sits
on the last cell of the output frame, which is the repair scan's entry shape,
so it does not move; the tape is untouched. -/
theorem t1CS_oobStart_dispatch (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .oobStart .p0 false false false latch) 1 =
      t1AlignedConfig n h hh tape .repairSeek .p3 false false false false := by
  rw [runConfig_one]
  exact t1CS_hold_stay n h hh tape
    (t1State .oobStart .p0 false false false latch)
    (t1State .repairSeek .p3 false false false false)
    (fun phase => t1Transition_oobStart_active phase .p0
      false false false latch _)

/-! ## The success arm -/

/-- **Leaving the anchor, again.**  `outWalk` walks off the `bof` frame in
exactly four steps and enters the forward cursor search.  Tape untouched,
latch carried. -/
theorem t1CS_outWalk_walk (n h : Nat) (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape .outWalk .p0
          false false false latch) 4 =
      t1AlignedConfig n (h+4) hsafe tape .outSeekCursor .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n h (by omega) tape .outWalk .p0
        false false false latch) =
      t1AlignedConfig n (h+1) (by omega) tape .outWalk .p1
        false false false latch :=
    t1CS_hold_right n h (by omega) tape
      (t1State .outWalk .p0 false false false latch)
      (t1State .outWalk .p1 false false false latch)
      (fun phase => t1Transition_outWalk phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (h+1) (by omega) tape .outWalk .p1
        false false false latch) =
      t1AlignedConfig n (h+2) (by omega) tape .outWalk .p2
        false false false latch :=
    t1CS_hold_right n (h+1) (by omega) tape
      (t1State .outWalk .p1 false false false latch)
      (t1State .outWalk .p2 false false false latch)
      (fun phase => t1Transition_outWalk phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (h+2) (by omega) tape .outWalk .p2
        false false false latch) =
      t1AlignedConfig n (h+3) (by omega) tape .outWalk .p3
        false false false latch :=
    t1CS_hold_right n (h+2) (by omega) tape
      (t1State .outWalk .p2 false false false latch)
      (t1State .outWalk .p3 false false false latch)
      (fun phase => t1Transition_outWalk phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (h+3) (by omega) tape .outWalk .p3
        false false false latch) =
      t1AlignedConfig n (h+4) hsafe tape .outSeekCursor .p0
        false false false latch :=
    t1CS_hold_right n (h+3) hsafe tape
      (t1State .outWalk .p3 false false false latch)
      (t1State .outSeekCursor .p0 false false false latch)
      (fun phase => t1Transition_outWalk phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n h (by omega) tape .outWalk .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3]

/-- **The forward cursor search reads one frame.**  `outSeekCursor` is a
`T1ForwardMode`, so this is a direct instance of the shared four-bit
macrostep: `spent`, `separator` and data frames are skipped, the `cursor`
marker hands over to `outBackup`. -/
theorem t1CS_outSeekCursor_frame (n h : Nat)
    (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (frame : T1Frame)
    (hnext : t1Advance .outSeekCursor frame ≠ .reject)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape .outSeekCursor .p0
          false false false latch) 4 =
      t1AlignedConfig n (h+4) hsafe tape (t1Advance .outSeekCursor frame)
        .p0 false false false latch :=
  t1CS_frame_macrostep n h hsafe tape .outSeekCursor frame
    T1ForwardMode.outSeekCursor hnext hbits latch

/-- Four steps back onto the cursor frame, ready to restore it. -/
theorem t1CS_outBackup_walk (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+4) hsafe tape .outBackup .p0
          false false false latch) 4 =
      t1AlignedConfig n base (by omega) tape .outWriteData .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+4) hsafe tape .outBackup .p0
        false false false latch) =
      t1AlignedConfig n (base+3) (by omega) tape .outBackup .p1
        false false false latch := by
    simpa using t1CS_hold_left n (base+4) hsafe (by omega) tape
      (t1State .outBackup .p0 false false false latch)
      (t1State .outBackup .p1 false false false latch)
      (fun phase => t1Transition_outBackup phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .outBackup .p1
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega) tape .outBackup .p2
        false false false latch := by
    simpa using t1CS_hold_left n (base+3) (by omega) (by omega) tape
      (t1State .outBackup .p1 false false false latch)
      (t1State .outBackup .p2 false false false latch)
      (fun phase => t1Transition_outBackup phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .outBackup .p2
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega) tape .outBackup .p3
        false false false latch := by
    simpa using t1CS_hold_left n (base+2) (by omega) (by omega) tape
      (t1State .outBackup .p2 false false false latch)
      (t1State .outBackup .p3 false false false latch)
      (fun phase => t1Transition_outBackup phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .outBackup .p3
        false false false latch) =
      t1AlignedConfig n base (by omega) tape .outWriteData .p0
        false false false latch := by
    simpa using t1CS_hold_left n (base+1) (by omega) (by omega) tape
      (t1State .outBackup .p3 false false false latch)
      (t1State .outWriteData .p0 false false false latch)
      (fun phase => t1Transition_outBackup phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+4) hsafe tape .outBackup .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3]

/-- **The cursor restore on the success arm.**  Four ascending writes put the
latched data frame back where the cursor was, and hand over to the search for
the output frame. -/
theorem t1CS_outWriteData_frame (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n base (by omega) tape .outWriteData .p0
          false false false latch) 4 =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteFrame base (T1Frame.data latch).bits tape) .outSeekOutput .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .outWriteData .p0
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .outWriteData .p1
        false false false latch :=
    t1CS_aligned_step_right n base (by omega) (by omega) tape
      (t1State .outWriteData .p0 false false false latch)
      (t1State .outWriteData .p1 false false false latch) false
      (fun phase => t1Transition_outWriteData phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .outWriteData .p1
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) true (t1WriteCell base false tape))
        .outWriteData .p2 false false false latch :=
    t1CS_aligned_step_right n (base+1) (by omega) (by omega)
      (t1WriteCell base false tape)
      (t1State .outWriteData .p1 false false false latch)
      (t1State .outWriteData .p2 false false false latch) true
      (fun phase => t1Transition_outWriteData phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) true (t1WriteCell base false tape))
        .outWriteData .p2 false false false latch) =
      t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) latch
          (t1WriteCell (base+1) true (t1WriteCell base false tape)))
        .outWriteData .p3 false false false latch :=
    t1CS_aligned_step_right n (base+2) (by omega) (by omega)
      (t1WriteCell (base+1) true (t1WriteCell base false tape))
      (t1State .outWriteData .p2 false false false latch)
      (t1State .outWriteData .p3 false false false latch) latch
      (fun phase => t1Transition_outWriteData phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) latch
          (t1WriteCell (base+1) true (t1WriteCell base false tape)))
        .outWriteData .p3 false false false latch) =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteCell (base+3) (!latch) (t1WriteCell (base+2) latch
          (t1WriteCell (base+1) true (t1WriteCell base false tape))))
        .outSeekOutput .p0 false false false latch :=
    t1CS_aligned_step_right n (base+3) (by omega) hsafe
      (t1WriteCell (base+2) latch
        (t1WriteCell (base+1) true (t1WriteCell base false tape)))
      (t1State .outWriteData .p3 false false false latch)
      (t1State .outSeekOutput .p0 false false false latch) (!latch)
      (fun phase => t1Transition_outWriteData phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .outWriteData .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3, t1WriteFrame_ascending, T1Frame.bits_data]

/-- **The output-frame search reads one frame.**  Another instance of the
shared macrostep: data frames are skipped, `output false` hands over to
`outTurn`. -/
theorem t1CS_outSeekOutput_frame (n h : Nat)
    (hsafe : h + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (frame : T1Frame)
    (hnext : t1Advance .outSeekOutput frame ≠ .reject)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h (by omega) tape .outSeekOutput .p0
          false false false latch) 4 =
      t1AlignedConfig n (h+4) hsafe tape (t1Advance .outSeekOutput frame)
        .p0 false false false latch :=
  t1CS_frame_macrostep n h hsafe tape .outSeekOutput frame
    T1ForwardMode.outSeekOutput hnext hbits latch

/-- One step turns the control around onto the output frame. -/
theorem t1CS_outTurn_step (n h : Nat) (hpos : 0 < h)
    (hh : h < T1M.tapeLength n) (tape : Fin (T1M.tapeLength n) → Bool)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .outTurn .p0 false false false latch) 1 =
      t1AlignedConfig n (h-1) (by omega) tape .outWriteOut .p3
        false false false latch := by
  rw [runConfig_one]
  exact t1CS_hold_left n h hh hpos tape
    (t1State .outTurn .p0 false false false latch)
    (t1State .outWriteOut .p3 false false false latch)
    (fun phase => t1Transition_outTurn phase .p0 false false false latch _)

/-- **The output write.**  Four right-to-left steps overwrite the frame at
`base` with `output latch` and leave the control on the last cell of the
preceding frame, in the repair scan, with the latch set to the accept tag.
Since `(T1Frame.output false).bits` and `(T1Frame.output latch).bits` differ
at most in their last cell, this is where the machine's single output bit is
produced. -/
theorem t1CS_outWriteOut_frame (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .outWriteOut .p3
          false false false latch) 4 =
      t1AlignedConfig n (base-1) (by omega)
        (t1WriteFrame base (T1Frame.output latch).bits tape) .repairSeek .p3
        false false false true := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .outWriteOut .p3
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+3) latch tape) .outWriteOut .p2
        false false false latch := by
    simpa using t1CS_aligned_step_left n (base+3) (by omega) (by omega) tape
      (t1State .outWriteOut .p3 false false false latch)
      (t1State .outWriteOut .p2 false false false latch) latch
      (fun phase => t1Transition_outWriteOut phase .p3 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+3) latch tape) .outWriteOut .p2
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell (base+2) false (t1WriteCell (base+3) latch tape))
        .outWriteOut .p1 false false false latch := by
    simpa using t1CS_aligned_step_left n (base+2) (by omega) (by omega)
      (t1WriteCell (base+3) latch tape)
      (t1State .outWriteOut .p2 false false false latch)
      (t1State .outWriteOut .p1 false false false latch) false
      (fun phase => t1Transition_outWriteOut phase .p2 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell (base+2) false (t1WriteCell (base+3) latch tape))
        .outWriteOut .p1 false false false latch) =
      t1AlignedConfig n base (by omega)
        (t1WriteCell (base+1) false
          (t1WriteCell (base+2) false (t1WriteCell (base+3) latch tape)))
        .outWriteOut .p0 false false false latch := by
    simpa using t1CS_aligned_step_left n (base+1) (by omega) (by omega)
      (t1WriteCell (base+2) false (t1WriteCell (base+3) latch tape))
      (t1State .outWriteOut .p1 false false false latch)
      (t1State .outWriteOut .p0 false false false latch) false
      (fun phase => t1Transition_outWriteOut phase .p1 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega)
        (t1WriteCell (base+1) false
          (t1WriteCell (base+2) false (t1WriteCell (base+3) latch tape)))
        .outWriteOut .p0 false false false latch) =
      t1AlignedConfig n (base-1) (by omega)
        (t1WriteCell base true (t1WriteCell (base+1) false
          (t1WriteCell (base+2) false (t1WriteCell (base+3) latch tape))))
        .repairSeek .p3 false false false true :=
    t1CS_aligned_step_left n base (by omega) hpos
      (t1WriteCell (base+1) false
        (t1WriteCell (base+2) false (t1WriteCell (base+3) latch tape)))
      (t1State .outWriteOut .p0 false false false latch)
      (t1State .repairSeek .p3 false false false true) true
      (fun phase => t1Transition_outWriteOut phase .p0 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .outWriteOut .p3
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3, t1WriteFrame_descending]
  cases latch <;> rfl

/-! ## The shared repair pass -/

/-- The first three steps of a `repairSeek` frame read. -/
private theorem t1CS_repairSeek_read (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
          false false false latch) 3 =
      t1AlignedConfig n base (by omega) tape .repairSeek .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega) tape .repairSeek .p2
        false false (tape ⟨base+3, by omega⟩) latch := by
    simpa using t1CS_hold_left n (base+3) (by omega) (by omega) tape
      (t1State .repairSeek .p3 false false false latch)
      (t1State .repairSeek .p2 false false (tape ⟨base+3, by omega⟩) latch)
      (fun phase => t1Transition_repairSeek_p3 phase false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .repairSeek .p2
        false false (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n (base+1) (by omega) tape .repairSeek .p1
        false (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch := by
    simpa using t1CS_hold_left n (base+2) (by omega) (by omega) tape
      (t1State .repairSeek .p2 false false (tape ⟨base+3, by omega⟩) latch)
      (t1State .repairSeek .p1 false (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch)
      (fun phase => t1Transition_repairSeek_p2 phase false false
        (tape ⟨base+3, by omega⟩) latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .repairSeek .p1
        false (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n base (by omega) tape .repairSeek .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch := by
    simpa using t1CS_hold_left n (base+1) (by omega) (by omega) tape
      (t1State .repairSeek .p1 false (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch)
      (t1State .repairSeek .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (fun phase => t1Transition_repairSeek_p1 phase false
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
        false false false latch) (1+1+1) = _
  rw [runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2]

private theorem t1CS_repairSeek_decode (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (frame : T1Frame)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) :
    decodeT1Frame? [tape ⟨base, by omega⟩, tape ⟨base+1, by omega⟩,
      tape ⟨base+2, by omega⟩, tape ⟨base+3, by omega⟩] = some frame := by
  simp only [t1PhysicalBitsAt] at hbits
  rw [hbits]
  exact decodeT1Frame_bits frame

/-- Repair scan across a frame that needs no repair: four steps, tape
unchanged, head on the last cell of the preceding frame. -/
theorem t1CS_repairSeek_frame_skip (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) (frame : T1Frame)
    (hframe : frame = .index ∨ frame = .separator ∨ frame = .finish ∨
      (∃ v, frame = .data v) ∨ ∃ v, frame = .output v)
    (hbits : t1PhysicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
          false false false latch) 4 =
      t1AlignedConfig n (base-1) (by omega) tape .repairSeek .p3
        false false false latch := by
  have hdecode := t1CS_repairSeek_decode n base hsafe tape frame hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .repairSeek .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n (base-1) (by omega) tape .repairSeek .p3
        false false false latch :=
    t1CS_hold_left n base (by omega) hpos tape
      (t1State .repairSeek .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (t1State .repairSeek .p3 false false false latch)
      (fun phase => t1Transition_repairSeek_p0_skip phase _ _ _ latch _
        frame hdecode hframe)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_repairSeek_read n base hsafe tape latch,
    runConfig_one, hs3]

/-- Repair scan onto a `spent` marker: four steps, tape unchanged, head on the
first cell of that frame, ready to rewrite it. -/
theorem t1CS_repairSeek_frame_write (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = T1Frame.spent.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
          false false false latch) 4 =
      t1AlignedConfig n base (by omega) tape .repairWrite .p0
        false false false latch := by
  have hdecode := t1CS_repairSeek_decode n base hsafe tape .spent hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .repairSeek .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n base (by omega) tape .repairWrite .p0
        false false false latch :=
    t1CS_hold_stay n base (by omega) tape
      (t1State .repairSeek .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (t1State .repairWrite .p0 false false false latch)
      (fun phase => t1Transition_repairSeek_p0_write phase _ _ _ latch _ hdecode)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_repairSeek_read n base hsafe tape latch,
    runConfig_one, hs3]

/-- Repair scan onto the `bof` anchor: the index field is fully repaired, so
four steps reach the final dispatch with the head on cell `base` and the
arm tag still in the latch. -/
theorem t1CS_repairSeek_frame_done (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool)
    (hbits : t1PhysicalBitsAt hsafe tape = T1Frame.bof.bits) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
          false false false latch) 4 =
      t1AlignedConfig n base (by omega) tape .repairDone .p0
        false false false latch := by
  have hdecode := t1CS_repairSeek_decode n base hsafe tape .bof hbits
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .repairSeek .p0
        (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
        (tape ⟨base+3, by omega⟩) latch) =
      t1AlignedConfig n base (by omega) tape .repairDone .p0
        false false false latch :=
    t1CS_hold_stay n base (by omega) tape
      (t1State .repairSeek .p0 (tape ⟨base+1, by omega⟩)
        (tape ⟨base+2, by omega⟩) (tape ⟨base+3, by omega⟩) latch)
      (t1State .repairDone .p0 false false false latch)
      (fun phase => t1Transition_repairSeek_p0_done phase _ _ _ latch _ hdecode)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .repairSeek .p3
        false false false latch) (3+1) = _
  rw [runConfig_add, t1CS_repairSeek_read n base hsafe tape latch,
    runConfig_one, hs3]

/-- **The on-tape increment.**  Four left-to-right steps overwrite the `spent`
marker at `base` with the `index` frame — the exact inverse of
`t1CS_markSpent_frame` — and hand over to the walk back. -/
theorem t1CS_repairWrite_frame (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n base (by omega) tape .repairWrite .p0
          false false false latch) 4 =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteFrame base T1Frame.index.bits tape) .repairBack .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .repairWrite .p0
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .repairWrite .p1
        false false false latch :=
    t1CS_aligned_step_right n base (by omega) (by omega) tape
      (t1State .repairWrite .p0 false false false latch)
      (t1State .repairWrite .p1 false false false latch) false
      (fun phase => t1Transition_repairWrite phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega)
        (t1WriteCell base false tape) .repairWrite .p1
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) false (t1WriteCell base false tape))
        .repairWrite .p2 false false false latch :=
    t1CS_aligned_step_right n (base+1) (by omega) (by omega)
      (t1WriteCell base false tape)
      (t1State .repairWrite .p1 false false false latch)
      (t1State .repairWrite .p2 false false false latch) false
      (fun phase => t1Transition_repairWrite phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega)
        (t1WriteCell (base+1) false (t1WriteCell base false tape))
        .repairWrite .p2 false false false latch) =
      t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) true
          (t1WriteCell (base+1) false (t1WriteCell base false tape)))
        .repairWrite .p3 false false false latch :=
    t1CS_aligned_step_right n (base+2) (by omega) (by omega)
      (t1WriteCell (base+1) false (t1WriteCell base false tape))
      (t1State .repairWrite .p2 false false false latch)
      (t1State .repairWrite .p3 false false false latch) true
      (fun phase => t1Transition_repairWrite phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega)
        (t1WriteCell (base+2) true
          (t1WriteCell (base+1) false (t1WriteCell base false tape)))
        .repairWrite .p3 false false false latch) =
      t1AlignedConfig n (base+4) hsafe
        (t1WriteCell (base+3) false (t1WriteCell (base+2) true
          (t1WriteCell (base+1) false (t1WriteCell base false tape))))
        .repairBack .p0 false false false latch :=
    t1CS_aligned_step_right n (base+3) (by omega) hsafe
      (t1WriteCell (base+2) true
        (t1WriteCell (base+1) false (t1WriteCell base false tape)))
      (t1State .repairWrite .p3 false false false latch)
      (t1State .repairBack .p0 false false false latch) false
      (fun phase => t1Transition_repairWrite phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n base (by omega) tape .repairWrite .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3, t1WriteFrame_ascending]
  rfl

/-- Four steps back onto the repaired frame. -/
theorem t1CS_repairBack_walk (n base : Nat)
    (hsafe : base + 4 < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (base+4) hsafe tape .repairBack .p0
          false false false latch) 4 =
      t1AlignedConfig n base (by omega) tape .repairHop .p0
        false false false latch := by
  have hs0 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+4) hsafe tape .repairBack .p0
        false false false latch) =
      t1AlignedConfig n (base+3) (by omega) tape .repairBack .p1
        false false false latch := by
    simpa using t1CS_hold_left n (base+4) hsafe (by omega) tape
      (t1State .repairBack .p0 false false false latch)
      (t1State .repairBack .p1 false false false latch)
      (fun phase => t1Transition_repairBack phase .p0 false false false latch _)
  have hs1 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+3) (by omega) tape .repairBack .p1
        false false false latch) =
      t1AlignedConfig n (base+2) (by omega) tape .repairBack .p2
        false false false latch := by
    simpa using t1CS_hold_left n (base+3) (by omega) (by omega) tape
      (t1State .repairBack .p1 false false false latch)
      (t1State .repairBack .p2 false false false latch)
      (fun phase => t1Transition_repairBack phase .p1 false false false latch _)
  have hs2 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+2) (by omega) tape .repairBack .p2
        false false false latch) =
      t1AlignedConfig n (base+1) (by omega) tape .repairBack .p3
        false false false latch := by
    simpa using t1CS_hold_left n (base+2) (by omega) (by omega) tape
      (t1State .repairBack .p2 false false false latch)
      (t1State .repairBack .p3 false false false latch)
      (fun phase => t1Transition_repairBack phase .p2 false false false latch _)
  have hs3 : TM.stepConfig (M := T1M)
      (t1AlignedConfig n (base+1) (by omega) tape .repairBack .p3
        false false false latch) =
      t1AlignedConfig n base (by omega) tape .repairHop .p0
        false false false latch := by
    simpa using t1CS_hold_left n (base+1) (by omega) (by omega) tape
      (t1State .repairBack .p3 false false false latch)
      (t1State .repairHop .p0 false false false latch)
      (fun phase => t1Transition_repairBack phase .p3 false false false latch _)
  change TM.runConfig (M := T1M)
      (t1AlignedConfig n (base+4) hsafe tape .repairBack .p0
        false false false latch) (1+1+1+1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [hs0, hs1, hs2, hs3]

/-- One step off the repaired frame, back into the repair scan's entry
shape.  This closes the thirteen-step repair cycle
`4 + 4 + 4 + 1`. -/
theorem t1CS_repairHop_step (n h : Nat) (hpos : 0 < h)
    (hh : h < T1M.tapeLength n) (tape : Fin (T1M.tapeLength n) → Bool)
    (latch : Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .repairHop .p0 false false false latch) 1 =
      t1AlignedConfig n (h-1) (by omega) tape .repairSeek .p3
        false false false latch := by
  rw [runConfig_one]
  exact t1CS_hold_left n h hh hpos tape
    (t1State .repairHop .p0 false false false latch)
    (t1State .repairSeek .p3 false false false latch)
    (fun phase => t1Transition_repairHop phase .p0 false false false latch _)

/-! ## Final dispatch

Both dispatch steps enter *literally* `t1AcceptState` / `t1RejectState` —
every scratch bit and the latch cleared — so `t1CS_runConfig_sink` applies
verbatim afterwards and, in the accepting case, the state is definitionally
`t1CS.acceptState`, which is what `TM.accepts` compares against. -/

theorem t1CS_repairDone_accept (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .repairDone .p0 false false false true) 1 =
      t1AlignedConfig n h hh tape .accept .p0 false false false false := by
  rw [runConfig_one]
  exact t1CS_hold_stay n h hh tape
    (t1State .repairDone .p0 false false false true) t1AcceptState
    (fun phase => t1Transition_repairDone_accept phase .p0 false false false _)

theorem t1CS_repairDone_reject (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .repairDone .p0 false false false false) 1 =
      t1AlignedConfig n h hh tape .reject .p0 false false false false := by
  rw [runConfig_one]
  exact t1CS_hold_stay n h hh tape
    (t1State .repairDone .p0 false false false false) t1RejectState
    (fun phase => t1Transition_repairDone_reject phase .p0 false false false _)

/-- The accepting dispatch lands in a configuration that stays put for the
remaining clock: the terminal state is a genuine sink. -/
theorem t1CS_repairDone_accept_stable (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .repairDone .p0 false false false true)
        (1 + steps) =
      t1AlignedConfig n h hh tape .accept .p0 false false false false := by
  rw [runConfig_add, t1CS_repairDone_accept n h hh tape]
  exact t1CS_runConfig_sink _ t1AcceptState (Or.inl rfl) rfl steps

/-- The rejecting dispatch is a genuine sink in the same sense. -/
theorem t1CS_repairDone_reject_stable (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .repairDone .p0 false false false false)
        (1 + steps) =
      t1AlignedConfig n h hh tape .reject .p0 false false false false := by
  rw [runConfig_add, t1CS_repairDone_reject n h hh tape]
  exact t1CS_runConfig_sink _ t1RejectState (Or.inr rfl) rfl steps

end Pnp3.Internal.PsubsetPpoly.TM
