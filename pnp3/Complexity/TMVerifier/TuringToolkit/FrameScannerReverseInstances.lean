import Complexity.TMVerifier.TuringToolkit.FrameScannerReverse
import Complexity.TMVerifier.TuringToolkit.FrameScannerT1
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation
import Complexity.TMVerifier.TuringToolkit.GateOneValidation

/-!
# T1 and G1 as instances of the generic reverse frame-scanner kernel

Both existing rewinds are the same machine shape — three leftward buffering
steps, then a frame-position-0 decision that either steps left again or stays
in a local handoff — and both are proved separately today, in
`TrueUniformSeekValidation` and in `GateOneValidation`.  This module
instantiates `ReverseFrameScanner` at each of them and re-derives the two
public reverse-scan theorems from the *generic* induction:
`t1RevScanner_rewind_tail` matches `t1CS_rewind_tail`'s statement shape (and
generalises its latch), `g1RevScanner_rewind_tail` matches `g1CS_rewind_tail`'s.

Neither existing theorem is changed or removed; the point is that the generic
kernel reproduces the same execution, so the next reverse pass — `G1`'s pass-B
operand walk — need not duplicate the stack a third time.

All obligations of both instances are discharged by the *existing* standalone
transition-table lemmas (`t1Transition_rewind_*`, `g1Transition_rewind_*`);
neither `t1Transition` nor `g1Transition` is unfolded here, and no control
table is modified — in particular `bRoundStart` stays inert.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## T1 -/
/-- T1's right-to-left frame table: the anchor hands over to the mutation
phase, every other frame continues the rewind. -/
def t1RevAdvance : T1Mode → T1Frame → T1Mode
  | _, .bof => .startMutation
  | _, _ => .rewind

/-- The bit-level form of `t1RevAdvance`, as `t1Transition` computes it. -/
def t1RevComplete (_mode : T1Mode) (b0 b1 b2 b3 : Bool) : T1Mode :=
  match decodeT1Frame? [b0, b1, b2, b3] with
  | some .bof => .startMutation
  | _ => .rewind

/-- The single T1 mode that reads frames right to left. -/
def T1RewindMode : T1Mode → Prop
  | .rewind => True
  | _ => False

theorem T1RewindMode.eq {m : T1Mode} (h : T1RewindMode m) : m = .rewind := by
  cases m <;> simp_all [T1RewindMode]

/-- The T1 rewind stops exactly at the mutation handoff. -/
def T1RewindStop (mode : T1Mode) : Prop := mode = .startMutation

private theorem t1RevComplete_stop_iff (m : T1Mode) (b0 b1 b2 b3 : Bool) :
    t1RevComplete m b0 b1 b2 b3 = .startMutation ↔
      decodeT1Frame? [b0, b1, b2, b3] = some .bof := by
  unfold t1RevComplete
  cases h : decodeT1Frame? [b0, b1, b2, b3] with
  | none => simp
  | some f => cases f <;> simp

private theorem t1RevComplete_ne (m : T1Mode) {b0 b1 b2 b3 : Bool}
    (h : ¬ T1RewindStop (t1RevComplete m b0 b1 b2 b3)) :
    t1RevComplete m b0 b1 b2 b3 = .rewind := by
  unfold t1RevComplete at h ⊢
  cases hd : decodeT1Frame? [b0, b1, b2, b3] with
  | none => rfl
  | some f => cases f <;> simp_all [T1RewindStop]

/-- **T1's rewind is an instance of the generic reverse kernel.** -/
def t1RevScanner : ReverseFrameScanner T1State T1Frame T1Mode Bool where
  program := t1CS
  phase := t1CS.startPhase
  codec := t1FrameCodec
  Stop := T1RewindStop
  revAdvance := t1RevAdvance
  revComplete := t1RevComplete
  Reverse := T1RewindMode
  rst3 := fun m latch => t1State m .p3 false false false latch
  rst2 := fun m latch b3 => t1State m .p2 false false b3 latch
  rst1 := fun m latch b2 b3 => t1State m .p1 false b2 b3 latch
  rst0 := fun m latch b1 b2 b3 => t1State m .p0 b1 b2 b3 latch
  stopState := fun m latch => t1State m .p0 false false false latch
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    have h' : decodeT1Frame? [b0, b1, b2, b3] = some f := h
    unfold t1RevComplete
    rw [h']
    cases f <;> rfl
  rstep_p3 := by
    intro m hm latch scan
    obtain rfl := hm.eq
    exact t1Transition_rewind_p3 t1CS.startPhase false false false latch scan
  rstep_p2 := by
    intro m hm latch b3 scan
    obtain rfl := hm.eq
    exact t1Transition_rewind_p2 t1CS.startPhase false false b3 latch scan
  rstep_p1 := by
    intro m hm latch b2 b3 scan
    obtain rfl := hm.eq
    exact t1Transition_rewind_p1 t1CS.startPhase false b2 b3 latch scan
  rstep_p0 := by
    intro m hm latch b1 b2 b3 scan hne
    obtain rfl := hm.eq
    rw [t1RevComplete_ne _ hne]
    refine t1Transition_rewind_p0_other t1CS.startPhase b1 b2 b3 latch scan ?_
    exact fun hbof => hne ((t1RevComplete_stop_iff _ _ _ _ _).mpr hbof)
  rstep_p0_stop := by
    intro m hm latch b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    rw [show t1RevComplete .rewind scan b1 b2 b3 = .startMutation from hstop]
    exact t1Transition_rewind_p0_bof t1CS.startPhase b1 b2 b3 latch scan
      ((t1RevComplete_stop_iff _ _ _ _ _).mp hstop)

@[simp] theorem t1RevScanner_revAdvance :
    t1RevScanner.revAdvance = t1RevAdvance := rfl

@[simp] theorem t1RevScanner_Stop : t1RevScanner.Stop = T1RewindStop := rfl

/-- A run of non-anchor frames keeps the T1 rewind in `rewind`. -/
private theorem t1Rev_const (l : List T1Frame) (h : ∀ f ∈ l, f ≠ T1Frame.bof) :
    t1RevScanner.RevValidPath .rewind l ∧
      t1RevScanner.revAdvanceList .rewind l = .rewind :=
  t1RevScanner.revValidPath_const (m := .rewind) trivial
    (by simp [T1RewindStop]) l fun f hf => by
      have hne := h f hf
      cases f <;> simp_all [t1RevAdvance]

/-- **T1 reverse-scan regression.**  The statement is `t1CS_rewind_tail`'s and
the proof is the generic `revScanFrames` at `t1RevScanner`: exactly four TM
steps per frame rewind across a list of non-anchor frames, preserving the
list-backed tape and the latch, finishing on the last cell of the `bof`. -/
theorem t1RevScanner_rewind_tail (n : Nat) (tail suffix : List T1Frame)
    (latch : Bool) (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < T1M.tapeLength n) :
    TM.runConfig (M := T1M)
        (t1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
          .rewind .p3 false false false latch) (4 * tail.length) =
      t1AlignedConfig n 3 (by omega)
        (t1ListTape ((.bof :: tail ++ suffix).flatMap T1Frame.bits))
        .rewind .p3 false false false latch := by
  obtain ⟨hpath, hfold⟩ := t1Rev_const tail hne
  have hsafe' : 4 * tail.length + 4 < T1M.tapeLength n := by omega
  have h := t1RevScanner.revScanFrames n [] .bof tail suffix .rewind latch
    hpath (by simpa using hsafe')
  rw [hfold] at h
  simpa [show 4 * (1 + tail.length) - 1 = 4 * tail.length + 3 by omega] using h

/-! ## G1 -/
/-- G1's right-to-left frame table: the anchor hands over to the pass-B
rescan, every other frame continues the rewind. -/
def g1RevAdvance : G1Mode → G1Frame → G1Mode
  | _, .bof => .readBStart
  | _, _ => .rewind

/-- The bit-level form of `g1RevAdvance`, as `g1Transition` computes it. -/
def g1RevComplete (_mode : G1Mode) (b0 b1 b2 b3 : Bool) : G1Mode :=
  match decodeG1Frame? [b0, b1, b2, b3] with
  | some .bof => .readBStart
  | _ => .rewind

/-- The single G1 mode that reads frames right to left. -/
def G1RewindMode : G1Mode → Prop
  | .rewind => True
  | _ => False

theorem G1RewindMode.eq {m : G1Mode} (h : G1RewindMode m) : m = .rewind := by
  cases m <;> simp_all [G1RewindMode]

/-- The G1 rewind stops exactly at the pass-B handoff. -/
def G1RewindStop (mode : G1Mode) : Prop := mode = .readBStart

private theorem g1RevComplete_stop_iff (m : G1Mode) (b0 b1 b2 b3 : Bool) :
    g1RevComplete m b0 b1 b2 b3 = .readBStart ↔
      decodeG1Frame? [b0, b1, b2, b3] = some .bof := by
  unfold g1RevComplete
  cases h : decodeG1Frame? [b0, b1, b2, b3] with
  | none => simp
  | some f => cases f <;> simp

private theorem g1RevComplete_ne (m : G1Mode) {b0 b1 b2 b3 : Bool}
    (h : ¬ G1RewindStop (g1RevComplete m b0 b1 b2 b3)) :
    g1RevComplete m b0 b1 b2 b3 = .rewind := by
  unfold g1RevComplete at h ⊢
  cases hd : decodeG1Frame? [b0, b1, b2, b3] with
  | none => rfl
  | some f => cases f <;> simp_all [G1RewindStop]

/-- **G1's rewind is an instance of the generic reverse kernel.**  The carried
context is the full `G1Ctx` triple, threaded through unchanged. -/
def g1RevScanner : ReverseFrameScanner G1State G1Frame G1Mode G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  Stop := G1RewindStop
  revAdvance := g1RevAdvance
  revComplete := g1RevComplete
  Reverse := G1RewindMode
  rst3 := fun m ctx => g1State m .p3 false false false ctx
  rst2 := fun m ctx b3 => g1State m .p2 false false b3 ctx
  rst1 := fun m ctx b2 b3 => g1State m .p1 false b2 b3 ctx
  rst0 := fun m ctx b1 b2 b3 => g1State m .p0 b1 b2 b3 ctx
  stopState := fun m ctx => g1State m .p0 false false false ctx
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    have h' : decodeG1Frame? [b0, b1, b2, b3] = some f := h
    unfold g1RevComplete
    rw [h']
    cases f <;> rfl
  rstep_p3 := by
    intro m hm ctx scan
    obtain rfl := hm.eq
    exact g1Transition_rewind_p3 g1CS.startPhase false false false scan ctx
  rstep_p2 := by
    intro m hm ctx b3 scan
    obtain rfl := hm.eq
    exact g1Transition_rewind_p2 g1CS.startPhase false false b3 scan ctx
  rstep_p1 := by
    intro m hm ctx b2 b3 scan
    obtain rfl := hm.eq
    exact g1Transition_rewind_p1 g1CS.startPhase false b2 b3 scan ctx
  rstep_p0 := by
    intro m hm ctx b1 b2 b3 scan hne
    obtain rfl := hm.eq
    rw [g1RevComplete_ne _ hne]
    refine g1Transition_rewind_p0_other g1CS.startPhase b1 b2 b3 scan ctx ?_
    exact fun hbof => hne ((g1RevComplete_stop_iff _ _ _ _ _).mpr hbof)
  rstep_p0_stop := by
    intro m hm ctx b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    rw [show g1RevComplete .rewind scan b1 b2 b3 = .readBStart from hstop]
    exact g1Transition_rewind_p0_bof g1CS.startPhase b1 b2 b3 scan ctx
      ((g1RevComplete_stop_iff _ _ _ _ _).mp hstop)

@[simp] theorem g1RevScanner_revAdvance :
    g1RevScanner.revAdvance = g1RevAdvance := rfl

@[simp] theorem g1RevScanner_Stop : g1RevScanner.Stop = G1RewindStop := rfl

/-- A run of non-anchor frames keeps the G1 rewind in `rewind`. -/
private theorem g1Rev_const (l : List G1Frame) (h : ∀ f ∈ l, f ≠ G1Frame.bof) :
    g1RevScanner.RevValidPath .rewind l ∧
      g1RevScanner.revAdvanceList .rewind l = .rewind :=
  g1RevScanner.revValidPath_const (m := .rewind) trivial
    (by simp [G1RewindStop]) l fun f hf => by
      have hne := h f hf
      cases f <;> simp_all [g1RevAdvance]

/-- **G1 reverse-scan regression.**  The statement is `g1CS_rewind_tail`'s and
the proof is the generic `revScanFrames` at `g1RevScanner`: exactly four TM
steps per frame rewind across a list of non-anchor frames, preserving the
list-backed tape and the whole `G1Ctx`, finishing on the last cell of the
anchor. -/
theorem g1RevScanner_rewind_tail (n : Nat) (tail suffix : List G1Frame)
    (ctx : G1Ctx) (hne : ∀ f ∈ tail, f ≠ .bof)
    (hsafe : 4 * (1 + tail.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (1 + tail.length) - 1) (by omega)
          (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
          .rewind .p3 false false false ctx) (4 * tail.length) =
      g1AlignedConfig n 3 (by omega)
        (g1ListTape ((.bof :: tail ++ suffix).flatMap G1Frame.bits))
        .rewind .p3 false false false ctx := by
  obtain ⟨hpath, hfold⟩ := g1Rev_const tail hne
  have hsafe' : 4 * tail.length + 4 < G1M.tapeLength n := by omega
  have h := g1RevScanner.revScanFrames n [] .bof tail suffix .rewind ctx
    hpath (by simpa using hsafe')
  rw [hfold] at h
  simpa [show 4 * (1 + tail.length) - 1 = 4 * tail.length + 3 by omega] using h

end Pnp3.Internal.PsubsetPpoly.TM
