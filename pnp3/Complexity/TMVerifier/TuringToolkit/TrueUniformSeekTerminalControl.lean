import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation
/-!
# T1c-1: entering the terminal arms
T1c-1 activates the two T1b terminal boundaries.  This companion derives
generic `TM.runConfig` macros for output traversal/write, reverse index repair,
literal dispatch, and sink stability from standalone transition lemmas.  It
never unfolds the table and claims no canonical composite run, global
restoration, output correctness, `t1Clock` padding, `TM.accepts`, or concrete
input-to-sink theorem; those obligations belong to T1c-2.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM
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

/-- **The output write.** Four right-to-left steps overwrite the frame at `base` with `output latch` and leave the control on the last cell of the preceding frame, in the repair scan, with the latch set to the accept tag. Since `(T1Frame.output false).bits` and `(T1Frame.output latch).bits` differ at most in their last cell, this is where the machine's single output bit is produced. -/
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

theorem t1CS_repairDone_accept_stable (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .repairDone .p0 false false false true)
        (1 + steps) =
      t1AlignedConfig n h hh tape .accept .p0 false false false false := by
  rw [runConfig_add, t1CS_repairDone_accept n h hh tape]
  exact t1CS_runConfig_sink _ t1AcceptState (Or.inl rfl) rfl steps

theorem t1CS_repairDone_reject_stable (n h : Nat) (hh : h < T1M.tapeLength n)
    (tape : Fin (T1M.tapeLength n) → Bool) (steps : Nat) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n h hh tape .repairDone .p0 false false false false)
        (1 + steps) =
      t1AlignedConfig n h hh tape .reject .p0 false false false false := by
  rw [runConfig_add, t1CS_repairDone_reject n h hh tape]
  exact t1CS_runConfig_sink _ t1RejectState (Or.inr rfl) rfl steps

end Pnp3.Internal.PsubsetPpoly.TM
