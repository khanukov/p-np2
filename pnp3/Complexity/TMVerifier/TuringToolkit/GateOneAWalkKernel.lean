import Complexity.TMVerifier.TuringToolkit.GateOneWalkKernel
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkInstallAtoms

/-!
# Dormant G1 operand-A normal and terminal walk

**Progress classification: Infrastructure.**  Every execution theorem starts
from a caller-supplied configuration.  `aInstallStart` stays idle, normal
restore ends at `aProbe`, and terminal cleanup stops at the stationary local
handoff `aRepairStart`.  No initial-configuration route, iteration or repair
sweep is supplied here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

def G1ASeekOutSkip : G1Frame → Prop
  | .data _ | .separator | .index | .spent => True
  | _ => False

instance : DecidablePred G1ASeekOutSkip := fun f => by
  cases f <;> first | exact isTrue trivial | exact isFalse id

def G1ASeekInSkip : G1Frame → Prop
  | .spent => True
  | _ => False

instance : DecidablePred G1ASeekInSkip := fun f => by
  cases f <;> first | exact isTrue trivial | exact isFalse id

def G1AWalkSkip : G1Frame → Prop
  | .spent | .argSep | .index | .separator | .data _ => True
  | _ => False

instance : DecidablePred G1AWalkSkip := fun f => by
  cases f <;> first | exact isTrue trivial | exact isFalse id

theorem g1Advance_aFwd_of_skip {f : G1Frame} (h : G1AWalkSkip f) :
    g1Advance .aFwd f = .aFwd := by
  cases f <;> first | rfl | exact (show False from h).elim

theorem g1Advance_aRet_of_skip {f : G1Frame} (h : G1AWalkSkip f) :
    g1Advance .aRet f = .aRet := by
  cases f <;> first | rfl | exact (show False from h).elim

theorem G1ASeekOutSkip_ne_argSep {f : G1Frame} (h : G1ASeekOutSkip f) :
    f ≠ .argSep := by cases f <;> simp_all [G1ASeekOutSkip]

theorem G1ASeekInSkip_ne_index {f : G1Frame} (h : G1ASeekInSkip f) :
    f ≠ .index := by cases f <;> simp_all [G1ASeekInSkip]

theorem G1ASeekInSkip_ne_argSep {f : G1Frame} (h : G1ASeekInSkip f) :
    f ≠ .argSep := by cases f <;> simp_all [G1ASeekInSkip]

def G1ASeekStop : G1Mode → Prop
  | .aDec | .aExh | .reject => True
  | _ => False

instance : DecidablePred G1ASeekStop := fun m => by
  cases m <;> first | exact isTrue trivial | exact isFalse id

def G1ASeekMode : G1Mode → Prop
  | .aSeekOut | .aSeekIn => True
  | _ => False

instance : DecidablePred G1ASeekMode := fun m => by
  cases m <;> first | exact isTrue trivial | exact isFalse id

theorem G1ASeekMode.eq {m : G1Mode} (h : G1ASeekMode m) :
    m = .aSeekOut ∨ m = .aSeekIn := by
  cases m <;> first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim h

theorem g1ASeekRevAdvance_out_of_skip {f : G1Frame}
    (h : G1ASeekOutSkip f) : g1ASeekRevAdvance .aSeekOut f = .aSeekOut := by
  cases f <;> first | rfl | exact (show False from h).elim

theorem g1ASeekRevAdvance_in_of_skip {f : G1Frame}
    (h : G1ASeekInSkip f) : g1ASeekRevAdvance .aSeekIn f = .aSeekIn := by
  cases f <;> first | rfl | exact (show False from h).elim

private theorem g1ASeekRevComplete_out (b0 b1 b2 b3 : Bool) :
    g1ASeekRevComplete .aSeekOut b0 b1 b2 b3 = .aSeekIn ∨
      g1ASeekRevComplete .aSeekOut b0 b1 b2 b3 = .aSeekOut ∨
      g1ASeekRevComplete .aSeekOut b0 b1 b2 b3 = .reject := by
  unfold g1ASeekRevComplete
  cases hd : decodeG1Frame? [b0, b1, b2, b3] with
  | none => exact Or.inr (Or.inr rfl)
  | some f => cases f <;> simp [g1ASeekRevAdvance]

private theorem g1ASeekRevComplete_in (b0 b1 b2 b3 : Bool) :
    g1ASeekRevComplete .aSeekIn b0 b1 b2 b3 = .aDec ∨
      g1ASeekRevComplete .aSeekIn b0 b1 b2 b3 = .aExh ∨
      g1ASeekRevComplete .aSeekIn b0 b1 b2 b3 = .aSeekIn ∨
      g1ASeekRevComplete .aSeekIn b0 b1 b2 b3 = .reject := by
  unfold g1ASeekRevComplete
  cases hd : decodeG1Frame? [b0, b1, b2, b3] with
  | none => exact Or.inr (Or.inr (Or.inr rfl))
  | some f => cases f <;> simp [g1ASeekRevAdvance]

def g1ASeekStopState (mode : G1Mode) (ctx : G1Ctx) : G1State :=
  match mode with
  | .aDec => g1ADecState ctx
  | .aExh => g1AExhState ctx
  | _ => g1RejectState

def g1AWalkScanner : ReverseFrameScanner G1State G1Frame G1Mode G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  Stop := G1ASeekStop
  revAdvance := g1ASeekRevAdvance
  revComplete := g1ASeekRevComplete
  Reverse := G1ASeekMode
  rst3 := fun m ctx => g1State m .p3 false false false ctx
  rst2 := fun m ctx b3 => g1State m .p2 false false b3 ctx
  rst1 := fun m ctx b2 b3 => g1State m .p1 false b2 b3 ctx
  rst0 := fun m ctx b1 b2 b3 => g1State m .p0 b1 b2 b3 ctx
  stopState := g1ASeekStopState
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    exact g1ASeekRevComplete_some h
  rstep_p3 := by
    intro m hm ctx scan
    rcases hm.eq with rfl | rfl
    · exact g1Transition_aSeekOut_p3 g1CS.startPhase _ _ _ _ _
    · exact g1Transition_aSeekIn_p3 g1CS.startPhase _ _ _ _ _
  rstep_p2 := by
    intro m hm ctx b3 scan
    rcases hm.eq with rfl | rfl
    · exact g1Transition_aSeekOut_p2 g1CS.startPhase _ _ _ _ _
    · exact g1Transition_aSeekIn_p2 g1CS.startPhase _ _ _ _ _
  rstep_p1 := by
    intro m hm ctx b2 b3 scan
    rcases hm.eq with rfl | rfl
    · exact g1Transition_aSeekOut_p1 g1CS.startPhase _ _ _ _ _
    · exact g1Transition_aSeekIn_p1 g1CS.startPhase _ _ _ _ _
  rstep_p0 := by
    intro m hm ctx b1 b2 b3 scan hne
    rcases hm.eq with rfl | rfl
    · rcases g1ASeekRevComplete_out scan b1 b2 b3 with he | he | he
      · rw [he]
        exact g1Transition_aSeekOut_p0_seekIn g1CS.startPhase _ _ _ _ _ he
      · rw [he]
        exact g1Transition_aSeekOut_p0_other g1CS.startPhase _ _ _ _ _ he
      · exact absurd (he ▸ (show G1ASeekStop .reject from trivial)) hne
    · rcases g1ASeekRevComplete_in scan b1 b2 b3 with he | he | he | he
      · exact absurd (he ▸ (show G1ASeekStop .aDec from trivial)) hne
      · exact absurd (he ▸ (show G1ASeekStop .aExh from trivial)) hne
      · rw [he]
        exact g1Transition_aSeekIn_p0_other g1CS.startPhase _ _ _ _ _ he
      · exact absurd (he ▸ (show G1ASeekStop .reject from trivial)) hne
  rstep_p0_stop := by
    intro m hm ctx b1 b2 b3 scan hstop
    rcases hm.eq with rfl | rfl
    · rcases g1ASeekRevComplete_out scan b1 b2 b3 with he | he | he
      · rw [he] at hstop; exact False.elim hstop
      · rw [he] at hstop; exact False.elim hstop
      · rw [he]
        exact g1Transition_aSeekOut_p0_bad g1CS.startPhase _ _ _ _ _ he
    · rcases g1ASeekRevComplete_in scan b1 b2 b3 with he | he | he | he
      · rw [he]
        exact g1Transition_aSeekIn_p0_dec g1CS.startPhase _ _ _ _ _ he
      · rw [he]
        exact g1Transition_aSeekIn_p0_exh g1CS.startPhase _ _ _ _ _ he
      · rw [he] at hstop; exact False.elim hstop
      · rw [he]
        exact g1Transition_aSeekIn_p0_bad g1CS.startPhase _ _ _ _ _ he

/-- Raw reserved window `1101` rejects after four reverse steps. -/
theorem g1CS_aWalk_reserved_1101_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : G1ASeekMode mode)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape mode .p3
          false false false ctx) 4 =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  have hwindow :
      [tape ⟨base, by omega⟩, tape ⟨base + 1, by omega⟩,
        tape ⟨base + 2, by omega⟩, tape ⟨base + 3, by omega⟩] =
        [true, true, false, true] := by
    simpa [physicalBitsAt] using hbits
  have hcomplete : g1ASeekRevComplete mode (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩) = .reject := by
    unfold g1ASeekRevComplete
    rw [hwindow]
    rfl
  have hstop : g1AWalkScanner.Stop
      (g1AWalkScanner.revComplete mode (tape ⟨base, by omega⟩)
        (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
        (tape ⟨base + 3, by omega⟩)) := by
    show G1ASeekStop (g1ASeekRevComplete mode (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩))
    rw [hcomplete]
    trivial
  have hrun := g1AWalkScanner.revWindowStop n base hsafe tape mode ctx hmode hstop
  simpa [g1AWalkScanner, g1ASeekStopState, hcomplete] using hrun

/-- The malformed run remains in the existing reject sink for extra budget. -/
theorem g1CS_aWalk_reserved_1101_reject_idle (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : G1ASeekMode mode)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape mode .p3
          false false false ctx) (4 + k) =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  rw [runConfig_add,
    g1CS_aWalk_reserved_1101_reject n base hsafe tape mode ctx hmode hbits]
  exact g1CS_runConfig_reject_sink n base (by omega) tape k

@[simp] theorem g1AWalkScanner_machine : g1AWalkScanner.machine = G1M := rfl

def g1ADecWriter : FrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := .spent
  w0 := true; w1 := true; w2 := false; w3 := false
  wst0 := g1ADecState
  wst1 := fun c => g1State .aDec .p1 false false false c
  wst2 := fun c => g1State .aDec .p2 false false false c
  wst3 := fun c => g1State .aDec .p3 false false false c
  exitState := g1AFwdState
  target_bits := rfl
  wstep_p0 := fun c x => g1Transition_aDec g1CS.startPhase .p0 _ _ _ x c
  wstep_p1 := fun c x => g1Transition_aDec g1CS.startPhase .p1 _ _ _ x c
  wstep_p2 := fun c x => g1Transition_aDec g1CS.startPhase .p2 _ _ _ x c
  wstep_p3 := fun c x => g1Transition_aDec g1CS.startPhase .p3 _ _ _ x c

def g1ARestoreWriter (b : Bool) : FrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := .data b
  w0 := false; w1 := true; w2 := b; w3 := !b
  wst0 := fun c => g1State (g1ARestoreMode b) .p0 false false false c
  wst1 := fun c => g1State (g1ARestoreMode b) .p1 false false false c
  wst2 := fun c => g1State (g1ARestoreMode b) .p2 false false false c
  wst3 := fun c => g1State (g1ARestoreMode b) .p3 false false false c
  exitState := g1AProbeState
  target_bits := by cases b <;> rfl
  wstep_p0 := fun c x => g1Transition_aRestore g1CS.startPhase b .p0 _ _ _ x c
  wstep_p1 := fun c x => g1Transition_aRestore g1CS.startPhase b .p1 _ _ _ x c
  wstep_p2 := fun c x => g1Transition_aRestore g1CS.startPhase b .p2 _ _ _ x c
  wstep_p3 := fun c x => g1Transition_aRestore g1CS.startPhase b .p3 _ _ _ x c

/-- Terminal `cursor → data b` writer, exiting only to `aRepairStart`. -/
def g1AFinWriter (b : Bool) : FrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := .data b
  w0 := false; w1 := true; w2 := b; w3 := !b
  wst0 := fun c => g1State (g1AFinMode b) .p0 false false false c
  wst1 := fun c => g1State (g1AFinMode b) .p1 false false false c
  wst2 := fun c => g1State (g1AFinMode b) .p2 false false false c
  wst3 := fun c => g1State (g1AFinMode b) .p3 false false false c
  exitState := g1ARepairStartState
  target_bits := by cases b <;> rfl
  wstep_p0 := fun c x => g1Transition_aFin g1CS.startPhase b .p0 _ _ _ x c
  wstep_p1 := fun c x => g1Transition_aFin g1CS.startPhase b .p1 _ _ _ x c
  wstep_p2 := fun c x => g1Transition_aFin g1CS.startPhase b .p2 _ _ _ x c
  wstep_p3 := fun c x => g1Transition_aFin g1CS.startPhase b .p3 _ _ _ x c

/-! ## Caller-supplied normal macros -/

theorem g1CS_aWalk_seek_index (n : Nat) (pre inner outer suffix : List G1Frame)
    (ctx : G1Ctx) (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hsafe : 4 * (pre.length + (inner.length + outer.length + 1)) + 4 <
      G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.index :: inner ++ G1Frame.argSep ::
            outer ++ suffix).flatMap G1Frame.bits))
          .aSeekOut .p3 false false false ctx)
        (4 * (inner.length + outer.length + 1) + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: inner ++ G1Frame.argSep ::
          outer ++ suffix).flatMap G1Frame.bits))
        .aDec .p0 false false false ctx :=
  g1AWalkScanner.revSeekAcrossBoundary n pre .index inner .argSep outer suffix
    .aSeekOut .aSeekIn ctx trivial (by simp [g1AWalkScanner, G1ASeekStop])
    trivial (by simp [g1AWalkScanner, G1ASeekStop])
    (fun f hf => g1ASeekRevAdvance_out_of_skip (houter f hf)) rfl
    (fun f hf => g1ASeekRevAdvance_in_of_skip (hinner f hf)) trivial hsafe

theorem g1CS_aWalk_seek_exhaust (n : Nat)
    (pre inner outer suffix : List G1Frame) (ctx : G1Ctx)
    (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hsafe : 4 * (pre.length + (inner.length + outer.length + 1)) + 4 <
      G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.argSep :: inner ++ G1Frame.argSep ::
            outer ++ suffix).flatMap G1Frame.bits))
          .aSeekOut .p3 false false false ctx)
        (4 * (inner.length + outer.length + 1) + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.argSep :: inner ++ G1Frame.argSep ::
          outer ++ suffix).flatMap G1Frame.bits))
        .aExh .p0 false false false ctx :=
  g1AWalkScanner.revSeekAcrossBoundary n pre .argSep inner .argSep outer suffix
    .aSeekOut .aSeekIn ctx trivial (by simp [g1AWalkScanner, G1ASeekStop])
    trivial (by simp [g1AWalkScanner, G1ASeekStop])
    (fun f hf => g1ASeekRevAdvance_out_of_skip (houter f hf)) rfl
    (fun f hf => g1ASeekRevAdvance_in_of_skip (hinner f hf)) trivial hsafe

theorem g1CS_aWalk_mark (n : Nat) (pre suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .aDec .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .aFwd .p0 false false false ctx :=
  g1ADecWriter.writeFrameOnList n pre suffix .index ctx hsafe

theorem g1CS_aWalk_fwd_to_cursor (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aFwd .p0 false false false ctx) (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aTurn .p0 false false false ctx := by
  have hfix : ∀ f ∈ skipped, g1Advance .aFwd f = .aFwd :=
    fun f hf => g1Advance_aFwd_of_skip (hskip f hf)
  have hlen : (skipped ++ [G1Frame.cursor]).length = skipped.length + 1 := by simp
  have hlist : pre ++ (skipped ++ [G1Frame.cursor]) ++ suffix =
      pre ++ skipped ++ G1Frame.cursor :: suffix := by simp [List.append_assoc]
  have hpath : G1ValidPath .aFwd (skipped ++ [G1Frame.cursor]) :=
    g1ValidPath_fix (mode := .aFwd) trivial [G1Frame.cursor]
      ⟨trivial, by decide, trivial⟩ skipped hfix
  have hfold : g1AdvanceList .aFwd (skipped ++ [.cursor]) = .aTurn := by
    rw [g1AdvanceList_fix (mode := .aFwd) [.cursor] skipped hfix]
    rfl
  have hscan := g1FrameScanner_scanFrames n pre (skipped ++ [.cursor]) suffix
    .aFwd ctx ((g1FrameScanner_validPath _ _).mpr hpath)
    (by rw [hlen]; exact hsafe)
  simpa only [hlist, hlen, g1AlignedFrame_eq, g1FrameScanner_advanceList, hfold]
    using hscan

theorem g1CS_aWalk_turn (n k : Nat) (hsafe : k + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (k + 4) hsafe tape .aTurn .p0 false false false ctx) 4 =
      g1AlignedConfig n k (by omega) tape
        (g1ARestoreMode ctx.vB) .p0 false false false ctx :=
  Phased.holdWalk4 g1CS g1CS.startPhase n k hsafe tape _ _ _ _ _
    (fun scan => g1Transition_aTurn g1CS.startPhase .p0 _ _ _ scan ctx)
    (fun scan => g1Transition_aTurn g1CS.startPhase .p1 _ _ _ scan ctx)
    (fun scan => g1Transition_aTurn g1CS.startPhase .p2 _ _ _ scan ctx)
    (fun scan => g1Transition_aTurn g1CS.startPhase .p3 _ _ _ scan ctx)

theorem g1CS_aWalk_restore (n : Nat) (pre suffix : List G1Frame) (b : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        (g1ARestoreMode b) .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data b :: suffix).flatMap G1Frame.bits))
        .aProbe .p0 false false false ctx :=
  (g1ARestoreWriter b).writeFrameOnList n pre suffix .cursor ctx hsafe

/-! ## Caller-supplied terminal macros -/

/-- From the local exhaustion boundary, re-read the opening `argSep` and scan
right through exactly the normal skip class to the cursor. -/
theorem g1CS_aWalk_exh_to_cursor (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 2)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .aExh .p0 false false false ctx) (4 * (skipped.length + 2)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 2))) hsafe
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .aTurnFin .p0 false false false ctx := by
  have hfix : ∀ f ∈ skipped, g1Advance .aRet f = .aRet :=
    fun f hf => g1Advance_aRet_of_skip (hskip f hf)
  have hlen :
      (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])).length =
        skipped.length + 2 := by simp
  have hlist :
      pre ++ (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) ++ suffix =
        pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor :: suffix := by
    simp [List.append_assoc]
  have hpath : G1ValidPath .aExh
      (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) :=
    ⟨trivial, by decide,
      g1ValidPath_fix (mode := .aRet) trivial [G1Frame.cursor]
        ⟨trivial, by decide, trivial⟩ skipped hfix⟩
  have hfold : g1AdvanceList .aExh
      (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) = .aTurnFin := by
    rw [g1AdvanceList_cons,
      show g1Advance .aExh G1Frame.argSep = .aRet from rfl,
      g1AdvanceList_fix (mode := .aRet) [G1Frame.cursor] skipped hfix]
    rfl
  have hscan := g1FrameScanner_scanFrames n pre
    (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) suffix .aExh ctx
    ((g1FrameScanner_validPath _ _).mpr hpath)
    (by rw [hlen]; exact hsafe)
  simpa only [hlist, hlen, g1AlignedFrame_eq, g1FrameScanner_advanceList, hfold]
    using hscan

/-- Four tape-preserving left steps land on the cursor in the Boolean-selected
terminal writer. -/
theorem g1CS_aWalk_turn_fin (n k : Nat) (hsafe : k + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (k + 4) hsafe tape .aTurnFin .p0 false false false ctx)
        4 =
      g1AlignedConfig n k (by omega) tape
        (g1AFinMode ctx.vB) .p0 false false false ctx :=
  Phased.holdWalk4 g1CS g1CS.startPhase n k hsafe tape _ _ _ _ _
    (fun scan => g1Transition_aTurnFin g1CS.startPhase .p0 _ _ _ scan ctx)
    (fun scan => g1Transition_aTurnFin g1CS.startPhase .p1 _ _ _ scan ctx)
    (fun scan => g1Transition_aTurnFin g1CS.startPhase .p2 _ _ _ scan ctx)
    (fun scan => g1Transition_aTurnFin g1CS.startPhase .p3 _ _ _ scan ctx)

/-- Final restoration removes the cursor, restores the latched Boolean, and
arrives at the stationary A-repair handoff with the context unchanged. -/
theorem g1CS_aWalk_fin_restore (n : Nat) (pre suffix : List G1Frame) (b : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        (g1AFinMode b) .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data b :: suffix).flatMap G1Frame.bits))
        .aRepairStart .p0 false false false ctx :=
  (g1AFinWriter b).writeFrameOnList n pre suffix .cursor ctx hsafe

/-- The complete caller-supplied exhaustion tail: return to the cursor, turn,
remove the cursor, restore `data ctx.vB`, and stop at `aRepairStart`. -/
theorem g1CS_aWalk_terminal_exact (n : Nat)
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 2)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .aExh .p0 false false false ctx) (4 * (skipped.length + 4)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 2))) hsafe
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.data ctx.vB ::
            suffix).flatMap G1Frame.bits))
        .aRepairStart .p0 false false false ctx := by
  have hscan := g1CS_aWalk_exh_to_cursor n pre skipped suffix ctx hskip hsafe
  have hturn := g1CS_aWalk_turn_fin n
    (4 * (pre.length + (skipped.length + 1))) (by omega)
    (g1ListTape
      ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
        suffix).flatMap G1Frame.bits)) ctx
  have hfinSafe :
      4 * (pre ++ G1Frame.argSep :: skipped).length + 4 <
        G1M.tapeLength n := by
    simpa only [List.length_append, List.length_cons] using hsafe
  have hfin := g1CS_aWalk_fin_restore n
    (pre ++ G1Frame.argSep :: skipped) suffix ctx.vB ctx hfinSafe
  have hturn' :
      TM.runConfig (M := G1M)
          (g1AlignedConfig n (4 * (pre.length + (skipped.length + 2))) hsafe
            (g1ListTape
              ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
                suffix).flatMap G1Frame.bits))
            .aTurnFin .p0 false false false ctx) 4 =
        g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
              suffix).flatMap G1Frame.bits))
          (g1AFinMode ctx.vB) .p0 false false false ctx := by
    simpa only [show 4 * (pre.length + (skipped.length + 1)) + 4 =
      4 * (pre.length + (skipped.length + 2)) by omega] using hturn
  have hfin' :
      TM.runConfig (M := G1M)
          (g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) (by omega)
            (g1ListTape
              ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
                suffix).flatMap G1Frame.bits))
            (g1AFinMode ctx.vB) .p0 false false false ctx) 4 =
        g1AlignedConfig n (4 * (pre.length + (skipped.length + 2))) hsafe
          (g1ListTape
            ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.data ctx.vB ::
              suffix).flatMap G1Frame.bits))
          .aRepairStart .p0 false false false ctx := by
    simpa only [List.length_append, List.length_cons, List.append_assoc,
      show 4 * (pre.length + (skipped.length + 1)) + 4 =
        4 * (pre.length + (skipped.length + 2)) by omega] using hfin
  rw [show 4 * (skipped.length + 4) =
      4 * (skipped.length + 2) + (4 + 4) by omega,
    runConfig_add, hscan, runConfig_add, hturn', hfin']

/-- `aRepairStart` is a local stationary handoff for every remaining budget. -/
theorem g1CS_runConfig_aRepairStart_idle (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aRepairStart .p0 false false false ctx) k =
      g1AlignedConfig n h hh tape .aRepairStart .p0 false false false ctx :=
  g1CS_runConfig_stable n h hh tape (g1ARepairStartState ctx)
    (fun phase scan => g1Transition_aRepairStart_idle phase .p0 false false
      false scan ctx) k

end Pnp3.Internal.PsubsetPpoly.TM
