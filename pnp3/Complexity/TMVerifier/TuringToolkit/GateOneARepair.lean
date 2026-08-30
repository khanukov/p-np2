import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernel
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkDriver

/-!
# S8a dormant reject-aware operand-A repair (2026-08-30)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

Five fresh modes implement a caller-supplied reverse repair scan.  The scan
crosses only `G1RepairSkip`, rewrites `spent` to `index`, rejects malformed or
reserved windows, and stops at the stationary local handoff `aRepairDone`.
`aRepairStart` remains stationary: this file does not activate the repair from
the S7 driver, compose a real initial configuration, compute a gate result, or
run combine/output/acceptance.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Reject-aware scanner and rewrite-cycle instances -/

/-- The single reverse-reading mode of the dormant A-repair scan. -/
def G1ARepairScanMode : G1Mode → Prop
  | .aRepairSeek => True
  | _ => False

theorem G1ARepairScanMode.eq {m : G1Mode} (h : G1ARepairScanMode m) :
    m = .aRepairSeek := by
  cases m <;> simp_all [G1ARepairScanMode]

/-- Exact stop set: rewrite handoff, canonical terminal, or reject sink. -/
def G1ARepairStop (mode : G1Mode) : Prop :=
  mode = .aRepairWrite ∨ mode = .aRepairDone ∨ mode = .reject

def g1ARepairStopState (mode : G1Mode) (ctx : G1Ctx) : G1State :=
  match mode with
  | .aRepairWrite => g1ARepairWriteState ctx
  | .aRepairDone => g1ARepairDoneState ctx
  | _ => g1RejectState

theorem g1ARepairStopState_write (ctx : G1Ctx) :
    g1ARepairStopState .aRepairWrite ctx = g1ARepairWriteState ctx := rfl

theorem g1ARepairStopState_done (ctx : G1Ctx) :
    g1ARepairStopState .aRepairDone ctx = g1ARepairDoneState ctx := rfl

theorem g1ARepairStopState_reject (ctx : G1Ctx) :
    g1ARepairStopState .reject ctx = g1RejectState := rfl

/-- Concrete reverse scanner using the same decision function as control. -/
def g1ARepairScanner : ReverseFrameScanner G1State G1Frame G1Mode G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  Stop := G1ARepairStop
  revAdvance := fun _ f => g1ARepairBackAdvance f
  revComplete := fun _ b0 b1 b2 b3 => g1ARepairBackComplete b0 b1 b2 b3
  Reverse := G1ARepairScanMode
  rst3 := fun m ctx => g1State m .p3 false false false ctx
  rst2 := fun m ctx b3 => g1State m .p2 false false b3 ctx
  rst1 := fun m ctx b2 b3 => g1State m .p1 false b2 b3 ctx
  rst0 := fun m ctx b1 b2 b3 => g1State m .p0 b1 b2 b3 ctx
  stopState := g1ARepairStopState
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    exact g1ARepairBackComplete_some h
  rstep_p3 := by
    intro m hm ctx scan
    obtain rfl := hm.eq
    exact g1Transition_aRepairSeek_p3 g1CS.startPhase false false false scan ctx
  rstep_p2 := by
    intro m hm ctx b3 scan
    obtain rfl := hm.eq
    exact g1Transition_aRepairSeek_p2 g1CS.startPhase false false b3 scan ctx
  rstep_p1 := by
    intro m hm ctx b2 b3 scan
    obtain rfl := hm.eq
    exact g1Transition_aRepairSeek_p1 g1CS.startPhase false b2 b3 scan ctx
  rstep_p0 := by
    intro m hm ctx b1 b2 b3 scan hne
    obtain rfl := hm.eq
    cases hd : decodeG1Frame? [scan, b1, b2, b3] with
    | none =>
        exact absurd
          (Or.inr (Or.inr (g1ARepairBackComplete_none hd)) : G1ARepairStop _) hne
    | some f =>
        have hc := g1ARepairBackComplete_some hd
        cases f with
        | spent => exact absurd (Or.inl hc : G1ARepairStop _) hne
        | bof => exact absurd (Or.inr (Or.inl hc) : G1ARepairStop _) hne
        | blank | cursor => exact absurd (Or.inr (Or.inr hc) : G1ARepairStop _) hne
        | tag | index | separator | finish | argSep | data _ | output _ =>
            rw [show g1ARepairBackComplete scan b1 b2 b3 = .aRepairSeek from hc]
            exact g1Transition_aRepairSeek_p0_skip g1CS.startPhase
              b1 b2 b3 scan ctx _ hd trivial
  rstep_p0_stop := by
    intro m hm ctx b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    cases hd : decodeG1Frame? [scan, b1, b2, b3] with
    | none =>
        have hc := g1ARepairBackComplete_none hd
        rw [show g1ARepairBackComplete scan b1 b2 b3 = G1Mode.reject from hc]
        exact g1Transition_aRepairSeek_p0_bad g1CS.startPhase b1 b2 b3 scan ctx hc
    | some f =>
        have hc := g1ARepairBackComplete_some hd
        cases f with
        | spent =>
            rw [show g1ARepairBackComplete scan b1 b2 b3 = .aRepairWrite from hc]
            exact g1Transition_aRepairSeek_p0_spent g1CS.startPhase
              b1 b2 b3 scan ctx hd
        | bof =>
            rw [show g1ARepairBackComplete scan b1 b2 b3 = .aRepairDone from hc]
            exact g1Transition_aRepairSeek_p0_bof g1CS.startPhase
              b1 b2 b3 scan ctx hd
        | blank | cursor =>
            rw [show g1ARepairBackComplete scan b1 b2 b3 = G1Mode.reject from hc]
            exact g1Transition_aRepairSeek_p0_bad g1CS.startPhase
              b1 b2 b3 scan ctx hc
        | tag | index | separator | finish | argSep | data _ | output _ =>
            rw [show g1ARepairBackComplete scan b1 b2 b3 = G1Mode.aRepairSeek
              from hc] at hstop
            rcases hstop with h | h | h <;> exact absurd h (by decide)

@[simp] theorem g1ARepairScanner_machine : g1ARepairScanner.machine = G1M := rfl

/-- The dormant `spent ↦ index` rewrite cycle at the fresh A modes. -/
def g1ARepairCycle : FrameRewriteCycle G1State G1Frame G1Mode G1Ctx where
  scanner := g1ARepairScanner
  seekMode := .aRepairSeek
  stopMode := .aRepairWrite
  marker := .spent
  target := .index
  w0 := false
  w1 := false
  w2 := true
  w3 := true
  wst1 := fun c => g1State .aRepairWrite .p1 false false false c
  wst2 := fun c => g1State .aRepairWrite .p2 false false false c
  wst3 := fun c => g1State .aRepairWrite .p3 false false false c
  bst0 := fun c => g1State .aRepairBack .p0 false false false c
  bst1 := fun c => g1State .aRepairBack .p1 false false false c
  bst2 := fun c => g1State .aRepairBack .p2 false false false c
  bst3 := fun c => g1State .aRepairBack .p3 false false false c
  hopState := fun c => g1State .aRepairHop .p0 false false false c
  seek_reverse := trivial
  seek_nostop := by simp [g1ARepairScanner, G1ARepairStop]
  marker_stop := rfl
  stop_stops := Or.inl rfl
  target_bits := rfl
  wstep_p0 := fun c x =>
    g1Transition_aRepairWrite g1CS.startPhase .p0 false false false x c
  wstep_p1 := fun c x =>
    g1Transition_aRepairWrite g1CS.startPhase .p1 false false false x c
  wstep_p2 := fun c x =>
    g1Transition_aRepairWrite g1CS.startPhase .p2 false false false x c
  wstep_p3 := fun c x =>
    g1Transition_aRepairWrite g1CS.startPhase .p3 false false false x c
  bstep_p0 := fun c x =>
    g1Transition_aRepairBack g1CS.startPhase .p0 false false false x c
  bstep_p1 := fun c x =>
    g1Transition_aRepairBack g1CS.startPhase .p1 false false false x c
  bstep_p2 := fun c x =>
    g1Transition_aRepairBack g1CS.startPhase .p2 false false false x c
  bstep_p3 := fun c x =>
    g1Transition_aRepairBack g1CS.startPhase .p3 false false false x c
  hop_step := fun c x =>
    g1Transition_aRepairHop g1CS.startPhase .p0 false false false x c

/-! ## Exact caller-supplied atoms -/

theorem g1CS_aRepair_cycle_onList (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx) 13 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx :=
  g1ARepairCycle.rewriteCycleOnList n pre suffix ctx hpre hsafe

theorem g1CS_aRepair_seek_and_repair (n : Nat)
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hpre : 0 < pre.length) (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: skipped ++ suffix).flatMap
            G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
        (4 * skipped.length + 13) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx :=
  g1ARepairCycle.seekAndRewrite n pre skipped suffix ctx hpre
    (fun f hf => g1ARepairBackAdvance_of_skip (hskip f hf)) hsafe

theorem g1CS_aRepair_frame_skip (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : G1RepairSkip f) (hbits : physicalBitsAt hsafe tape = f.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n (base - 1) (by omega) tape .aRepairSeek .p3
        false false false ctx := by
  have hnext : ¬ G1ARepairStop (g1ARepairBackAdvance f) := by
    rw [g1ARepairBackAdvance_of_skip hf]
    simp [G1ARepairStop]
  simpa [g1ARepairScanner, g1ARepairBackAdvance_of_skip hf] using
    g1ARepairScanner.revFrameMacrostep n base hpos hsafe tape .aRepairSeek f ctx
      trivial hnext hbits

theorem g1CS_aRepair_frame_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : f = .blank ∨ f = .cursor)
    (hbits : physicalBitsAt hsafe tape = f.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  have hbad : g1ARepairBackAdvance f = .reject := by
    rcases hf with rfl | rfl <;> rfl
  have hstop : G1ARepairStop (g1ARepairBackAdvance f) := by
    rw [hbad]; exact Or.inr (Or.inr rfl)
  have h := g1ARepairScanner.revAnchorStep n base hsafe tape .aRepairSeek f ctx
    trivial hstop hbits
  simpa [g1ARepairScanner, g1ARepairStopState, hbad] using h

theorem g1CS_aRepair_frame_reject_idle (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : f = .blank ∨ f = .cursor)
    (hbits : physicalBitsAt hsafe tape = f.bits) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) (4 + k) =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  rw [runConfig_add,
    g1CS_aRepair_frame_reject n base hsafe tape ctx f hf hbits]
  exact g1CS_runConfig_reject_sink n base (by omega) tape k

/-- Exact raw rejection of the literal reserved window `1101`. -/
theorem g1CS_aRepair_reserved_1101_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  have hw : [tape ⟨base, by omega⟩, tape ⟨base + 1, by omega⟩,
      tape ⟨base + 2, by omega⟩, tape ⟨base + 3, by omega⟩] =
      [true, true, false, true] := by
    simpa [physicalBitsAt] using hbits
  have hc : g1ARepairBackComplete (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩) = .reject := by
    unfold g1ARepairBackComplete
    rw [hw]
    rfl
  have hs : G1ARepairStop (g1ARepairBackComplete (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩)) := by
    rw [hc]; exact Or.inr (Or.inr rfl)
  have h := g1ARepairScanner.revWindowStop n base hsafe tape .aRepairSeek ctx
    trivial hs
  simpa [g1ARepairScanner, g1ARepairStopState, hc] using h

theorem g1CS_aRepair_reserved_1101_reject_idle (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) (4 + k) =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 := by
  rw [runConfig_add,
    g1CS_aRepair_reserved_1101_reject n base hsafe tape ctx hbits]
  exact g1CS_runConfig_reject_sink n base (by omega) tape k

theorem g1CS_aRepair_scan_skip (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) - 1) (by omega)
          (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx) (4 * skipped.length) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx := by
  induction skipped generalizing pre with
  | nil => simp
  | cons f rest ih =>
      have hf : G1RepairSkip f := hskip f (by simp)
      have hr : ∀ g ∈ rest, G1RepairSkip g := fun g hg => hskip g (by simp [hg])
      have hlen : (pre ++ [f]).length = pre.length + 1 := by simp
      have hsafe' : 4 * ((pre ++ [f]).length + rest.length) <
          G1M.tapeLength n := by
        rw [hlen]
        simp only [List.length_cons] at hsafe
        omega
      have hi := ih (pre ++ [f]) (by omega) hr hsafe'
      have hb : 4 * pre.length + 4 < G1M.tapeLength n := by
        simp only [List.length_cons] at hsafe
        omega
      have hbits : physicalBitsAt hb
          (g1ListTape (n := n)
            ((pre ++ f :: (rest ++ suffix)).flatMap G1Frame.bits)) = f.bits :=
        physicalBitsAt_flatMap g1FrameCodec pre (rest ++ suffix) f hb
      have hs := g1CS_aRepair_frame_skip n (4 * pre.length) (by omega) hb
        (g1ListTape (n := n)
          ((pre ++ f :: (rest ++ suffix)).flatMap G1Frame.bits)) ctx f hf hbits
      simp only [hlen,
        show 4 * (pre.length + 1 + rest.length) - 1 =
          4 * (pre.length + (rest.length + 1)) - 1 by omega,
        show 4 * (pre.length + 1) - 1 = 4 * pre.length + 3 by omega,
        List.append_assoc, List.nil_append, List.cons_append] at hi
      rw [show 4 * (f :: rest).length = 4 * rest.length + 4 by simp; omega,
        runConfig_add]
      simp only [List.length_cons, List.append_assoc, List.cons_append]
      rw [hi, hs]

theorem g1CS_aRepair_spent_run (n : Nat) (pre suffix : List G1Frame) (s : Nat)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * (pre.length + s) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + s) - 1) (by omega)
          (g1ListTape ((pre ++ List.replicate s G1Frame.spent ++
            suffix).flatMap G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
        (13 * s) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ List.replicate s G1Frame.index ++
          suffix).flatMap G1Frame.bits)) .aRepairSeek .p3 false false false ctx := by
  induction s generalizing pre with
  | zero => simp
  | succ s ih =>
      have hlen : (pre ++ [G1Frame.spent]).length = pre.length + 1 := by simp
      have hi := ih (pre ++ [G1Frame.spent]) (by omega) (by rw [hlen]; omega)
      have hc := g1CS_aRepair_cycle_onList n pre
        (List.replicate s G1Frame.index ++ suffix) ctx hpre (by omega)
      simp only [hlen,
        show 4 * (pre.length + 1 + s) - 1 =
          4 * (pre.length + (s + 1)) - 1 by omega,
        show 4 * (pre.length + 1) - 1 = 4 * pre.length + 3 by omega,
        List.append_assoc, List.cons_append, List.nil_append] at hi
      rw [show 13 * (s + 1) = 13 * s + 13 by omega, runConfig_add]
      simp only [List.replicate_succ, List.append_assoc, List.cons_append]
        at hi hc ⊢
      rw [hi, hc]

theorem g1CS_aRepair_finish (n : Nat) (suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 3 (by omega)
          (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx) 4 =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .aRepairDone .p0 false false false ctx := by
  have hs : (0 : Nat) + 4 < G1M.tapeLength n := by omega
  have hb : physicalBitsAt hs
      (g1ListTape (n := n) ((G1Frame.bof :: suffix).flatMap G1Frame.bits)) =
      G1Frame.bof.bits := by
    simpa using physicalBitsAt_flatMap g1FrameCodec ([] : List G1Frame) suffix
      G1Frame.bof (by simpa using hs)
  have h := g1ARepairScanner.revAnchorStep n 0 hs
    (g1ListTape (n := n) ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
    .aRepairSeek G1Frame.bof ctx trivial (Or.inr (Or.inl rfl)) hb
  simpa [g1ARepairScanner, g1ARepairStopState] using h

/-- The canonical endpoint stays put for every extra caller-supplied budget. -/
theorem g1CS_runConfig_aRepairDone_idle (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aRepairDone .p0 false false false ctx) k =
      g1AlignedConfig n h hh tape .aRepairDone .p0 false false false ctx :=
  g1CS_runConfig_stable n h hh tape (g1ARepairDoneState ctx)
    (fun phase scan => g1Transition_aRepairDone_idle phase .p0 false false
      false scan ctx) k

/-! ## Generic dependency-closed repair pass -/

def g1ARepairPassSteps (a s m : Nat) : Nat := 4 * m + 13 * s + 4 * a + 4

theorem g1ARepairPassSteps_eq (a s m : Nat) :
    g1ARepairPassSteps a s m + 1 = g1RepairPassSteps a s m := by
  simp [g1ARepairPassSteps, g1RepairPassSteps]

theorem g1CS_aRepair_pass_exact (n s : Nat) (left mid tail : List G1Frame)
    (ctx : G1Ctx) (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hmid : ∀ f ∈ mid, G1RepairSkip f)
    (hsafe : 4 * (1 + left.length + s + mid.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (1 + left.length + s + mid.length) - 1)
          (by omega) (g1ListTape (([G1Frame.bof] ++ left ++
            List.replicate s G1Frame.spent ++ mid ++ tail).flatMap G1Frame.bits))
          .aRepairSeek .p3 false false false ctx)
        (g1ARepairPassSteps left.length s mid.length) =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.index ++ mid ++ tail).flatMap G1Frame.bits))
        .aRepairDone .p0 false false false ctx := by
  have hlenA : ([G1Frame.bof] ++ left ++
      List.replicate s G1Frame.spent).length = 1 + left.length + s := by
    simp only [List.length_append, List.length_replicate, List.length_singleton]
  have hlenB : ([G1Frame.bof] ++ left).length = 1 + left.length := by
    simp only [List.length_append, List.length_singleton]
  have hlenC : ([G1Frame.bof] : List G1Frame).length = 1 := rfl
  have hA := g1CS_aRepair_scan_skip n
    ([G1Frame.bof] ++ left ++ List.replicate s G1Frame.spent) mid tail ctx
    (by simp only [hlenA]; omega) hmid (by simp only [hlenA]; exact hsafe)
  have hB := g1CS_aRepair_spent_run n ([G1Frame.bof] ++ left) (mid ++ tail) s
    ctx (by simp only [hlenB]; omega) (by simp only [hlenB]; omega)
  have hC := g1CS_aRepair_scan_skip n [G1Frame.bof] left
    (List.replicate s G1Frame.index ++ mid ++ tail) ctx (by simp) hleft
    (by simp only [hlenC]; omega)
  have hD := g1CS_aRepair_finish n
    (left ++ List.replicate s G1Frame.index ++ mid ++ tail) ctx (by omega)
  simp only [hlenA] at hA
  simp only [hlenB] at hB
  simp only [hlenC, show 4 * 1 - 1 = 3 from rfl] at hC
  rw [show g1ARepairPassSteps left.length s mid.length =
      4 * mid.length + (13 * s + (4 * left.length + 4)) by
        simp [g1ARepairPassSteps]; omega,
    runConfig_add, runConfig_add, runConfig_add]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
    at hA hB hC hD ⊢
  rw [hA, hB, hC, hD]

/-! ## Canonical terminal-layout instantiation -/

def g1ARepairLeft (r : G1Request) : List G1Frame :=
  List.replicate r.tag.units G1Frame.tag ++ [G1Frame.argSep]

def g1ARepairMid (r : G1Request) : List G1Frame :=
  G1Frame.argSep :: (g1AWalkOperand2 r ++
    G1Frame.separator :: (r.vals.map G1Frame.data).take (r.arg1 + 1))

def g1ARepairTail (r : G1Request) : List G1Frame :=
  (r.vals.map G1Frame.data).drop (r.arg1 + 1) ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

@[simp] theorem g1ARepairLeft_length (r : G1Request) :
    (g1ARepairLeft r).length = r.tag.units + 1 := by
  simp [g1ARepairLeft]

theorem g1ARepairMid_length (r : G1Request) (hm : r.arg1 < r.vals.length) :
    (g1ARepairMid r).length = r.arg1 + r.arg2 + 3 := by
  simp only [g1ARepairMid, List.length_cons, List.length_append,
    g1AWalkOperand2_length, List.length_take, List.length_map]
  omega

theorem g1ARepair_split_of (r : G1Request) (X : List G1Frame) :
    [G1Frame.bof] ++ g1ARepairLeft r ++ X ++ g1ARepairMid r ++
        g1ARepairTail r =
      g1TagRouteFrames r ++ X ++ [G1Frame.argSep] ++ g1AWalkOperand2 r ++
        [G1Frame.separator] ++ r.vals.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] := by
  have hd : r.vals.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] =
      (r.vals.map G1Frame.data).take (r.arg1 + 1) ++
        ((r.vals.map G1Frame.data).drop (r.arg1 + 1) ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) := by
    rw [← List.append_assoc, List.take_append_drop]
  simp only [g1ARepairLeft, g1ARepairMid, g1ARepairTail, g1TagRouteFrames,
    List.append_assoc, List.cons_append, List.nil_append, hd]

/-- The S7 terminal word in the exact five-block spelling consumed by repair. -/
theorem g1AWalkDoneFrames_repair_split (r : G1Request) :
    g1AWalkDoneFrames r =
      [G1Frame.bof] ++ g1ARepairLeft r ++
        List.replicate r.arg1 G1Frame.spent ++ g1ARepairMid r ++
        g1ARepairTail r := by
  rw [g1ARepair_split_of r (List.replicate r.arg1 G1Frame.spent)]
  simp [g1AWalkDoneFrames, g1AWalkOperand1, List.append_assoc]

theorem g1ARepairLeft_skip (r : G1Request) :
    ∀ f ∈ g1ARepairLeft r, G1RepairSkip f := by
  intro f hf
  simp only [g1ARepairLeft, List.mem_append, List.mem_singleton,
    List.mem_replicate] at hf
  rcases hf with ⟨-, rfl⟩ | rfl <;> trivial

theorem g1ARepairMid_skip (r : G1Request) :
    ∀ f ∈ g1ARepairMid r, G1RepairSkip f := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · trivial
  · rcases List.mem_append.1 hf with h2 | hd
    · have hidx : f = G1Frame.index :=
        List.eq_of_mem_replicate (by simpa [g1AWalkOperand2] using h2)
      rw [hidx]
      trivial
    · rcases List.mem_cons.1 hd with rfl | hv
      · trivial
      · obtain ⟨v, -, hfv⟩ := List.mem_map.1 (List.mem_of_mem_take hv)
        rw [← hfv]
        trivial

/-- Canonical restoration with tag, operand B, data and terminal suffix visible. -/
theorem g1ARepairFrames_repaired (r : G1Request) :
    [G1Frame.bof] ++ g1ARepairLeft r ++ List.replicate r.arg1 G1Frame.index ++
        g1ARepairMid r ++ g1ARepairTail r =
      encodeG1Frames r ++ [G1Frame.blank] := by
  rw [g1ARepair_split_of r (List.replicate r.arg1 G1Frame.index)]
  rw [← g1TagRoute_split r]
  simp [g1TagRouteRest, g1AWalkOperand2, List.append_assoc]

/-- Explicit field spelling of the canonical endpoint. -/
theorem g1ARepairCanonical_fields (r : G1Request) :
    encodeG1Frames r ++ [G1Frame.blank] =
      g1TagRouteFrames r ++ List.replicate r.arg1 G1Frame.index ++
        [G1Frame.argSep] ++ g1AWalkOperand2 r ++ [G1Frame.separator] ++
        r.vals.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] := by
  rw [← g1ARepairFrames_repaired r,
    g1ARepair_split_of r (List.replicate r.arg1 G1Frame.index)]

private theorem g1ARepair_count_replicate_ne (f g : G1Frame) (m : Nat)
    (h : f ≠ g) : (List.replicate m g).count f = 0 :=
  List.count_eq_zero.2 (fun hmem => h (List.eq_of_mem_replicate hmem))

@[simp] theorem g1ARepairCanonical_count_spent (r : G1Request) :
    (encodeG1Frames r ++ [G1Frame.blank]).count G1Frame.spent = 0 := by
  have hd : (r.vals.map G1Frame.data).count G1Frame.spent = 0 :=
    List.count_eq_zero.2 (by
      intro h
      obtain ⟨b, -, hb⟩ := List.mem_map.1 h
      exact G1Frame.noConfusion hb)
  simp [encodeG1Frames, List.count_append, hd, g1ARepair_count_replicate_ne]

@[simp] theorem g1ARepairCanonical_count_cursor (r : G1Request) :
    (encodeG1Frames r ++ [G1Frame.blank]).count G1Frame.cursor = 0 := by
  have hd : (r.vals.map G1Frame.data).count G1Frame.cursor = 0 :=
    List.count_eq_zero.2 (by
      intro h
      obtain ⟨b, -, hb⟩ := List.mem_map.1 h
      exact G1Frame.noConfusion hb)
  simp [encodeG1Frames, List.count_append, hd, g1ARepair_count_replicate_ne]

@[simp] theorem g1ARepairCanonical_count_index (r : G1Request) :
    (encodeG1Frames r ++ [G1Frame.blank]).count G1Frame.index =
      r.arg1 + r.arg2 := by
  have hd : (r.vals.map G1Frame.data).count G1Frame.index = 0 :=
    List.count_eq_zero.2 (by
      intro h
      obtain ⟨b, -, hb⟩ := List.mem_map.1 h
      exact G1Frame.noConfusion hb)
  simp [encodeG1Frames, List.count_append, hd, g1ARepair_count_replicate_ne]

def g1ARepairSteps (r : G1Request) : Nat :=
  4 * r.tag.units + 17 * r.arg1 + 4 * r.arg2 + 20

theorem g1ARepairSteps_eq (r : G1Request) (hm : r.arg1 < r.vals.length) :
    g1ARepairSteps r =
      g1ARepairPassSteps (g1ARepairLeft r).length r.arg1
        (g1ARepairMid r).length := by
  rw [g1ARepairPassSteps, g1ARepairLeft_length, g1ARepairMid_length r hm,
    g1ARepairSteps]
  omega

set_option linter.unusedVariables false in
/-- Caller-supplied entry adjacent to, but not reached from, idle `aRepairStart`. -/
def g1ARepairEntryConfig (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length
    (4 * (1 + (g1ARepairLeft r).length + r.arg1 +
      (g1ARepairMid r).length) - 1)
    (by
      have hs := g1AWalkCursor_safe r r.arg1 hm
      rw [g1ARepairLeft_length, g1ARepairMid_length r hm]
      simp only [g1AWalkCursor] at hs
      omega)
    (g1ListTape ((g1AWalkDoneFrames r).flatMap G1Frame.bits))
    .aRepairSeek .p3 false false false (g1AWalkCtx r b v)

def g1ARepairDoneConfig (r : G1Request) (b v : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length 0 (g1_route_lt_tapeLength r 0 (by omega))
    (g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits))
    .aRepairDone .p0 false false false (g1AWalkCtx r b v)

/-- S8a capstone: every operand-A `spent` frame is restored, with exact tape,
head, control and complete carried context.  The run is caller-supplied. -/
theorem g1CS_aRepair_canonical_exact (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
        (g1ARepairSteps r) = g1ARepairDoneConfig r b v := by
  have hs := g1AWalkCursor_safe r r.arg1 hm
  have hp := g1CS_aRepair_pass_exact (encodeG1 r).length r.arg1
    (g1ARepairLeft r) (g1ARepairMid r) (g1ARepairTail r)
    (g1AWalkCtx r b v) (g1ARepairLeft_skip r) (g1ARepairMid_skip r) (by
      rw [g1ARepairLeft_length, g1ARepairMid_length r hm]
      simp only [g1AWalkCursor] at hs
      omega)
  rw [← g1AWalkDoneFrames_repair_split r, g1ARepairFrames_repaired r] at hp
  rw [g1ARepairEntryConfig, g1ARepairDoneConfig, g1ARepairSteps_eq r hm]
  exact hp

theorem g1CS_aRepair_canonical_head (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    ((TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).head : Nat) = 0 := by
  rw [g1CS_aRepair_canonical_exact r b v hm hv]
  rfl

theorem g1CS_aRepair_canonical_tape (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).tape =
      g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits) := by
  rw [g1CS_aRepair_canonical_exact r b v hm hv]
  rfl

theorem g1CS_aRepair_canonical_state (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).state.snd =
      g1ARepairDoneState (g1AWalkCtx r b v) := by
  rw [g1CS_aRepair_canonical_exact r b v hm hv]
  rfl

theorem g1CS_aRepair_canonical_res (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).state.snd.ctx.res = g1Residual r.tag b := by
  rw [g1CS_aRepair_canonical_exact r b v hm hv]
  exact g1AWalkCtx_res r b v

theorem g1CS_aRepair_canonical_vB (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (TM.runConfig (M := G1M) (g1ARepairEntryConfig r b v hm hv)
      (g1ARepairSteps r)).state.snd.ctx.vB = v := by
  rw [g1CS_aRepair_canonical_exact r b v hm hv]
  rfl

/-! ## Literal caller-supplied probes -/

namespace G1ARepairExamples

def reqFalse : G1Request := ⟨.input, 2, 0, [true, true, false]⟩
def reqTrue : G1Request := ⟨.input, 2, 0, [false, false, true]⟩
def reqZero : G1Request := ⟨.input, 0, 0, [true]⟩

theorem literal_steps : g1ARepairSteps reqFalse = 58 ∧
    g1ARepairSteps reqTrue = 58 ∧
    g1ARepairSteps reqZero = 24 := by decide

theorem literal_false_repair_exact :
    TM.runConfig (M := G1M)
        (g1ARepairEntryConfig reqFalse false false (by decide) (by decide)) 58 =
      g1ARepairDoneConfig reqFalse false false := by
  simpa using g1CS_aRepair_canonical_exact reqFalse false false
    (by decide) (by decide)

theorem literal_true_repair_exact :
    TM.runConfig (M := G1M)
        (g1ARepairEntryConfig reqTrue true true (by decide) (by decide)) 58 =
      g1ARepairDoneConfig reqTrue true true := by
  simpa using g1CS_aRepair_canonical_exact reqTrue true true
    (by decide) (by decide)

theorem literal_zero_arg1_repair_exact :
    TM.runConfig (M := G1M)
        (g1ARepairEntryConfig reqZero false true (by decide) (by decide)) 24 =
      g1ARepairDoneConfig reqZero false true := by
  simpa using g1CS_aRepair_canonical_exact reqZero false true
    (by decide) (by decide)

theorem literal_false_endpoint_word :
    encodeG1Frames reqFalse ++ [G1Frame.blank] =
      [.bof, .tag, .argSep, .index, .index, .argSep, .separator,
        .data true, .data true, .data false, .output false, .finish, .blank] :=
  rfl

theorem literal_true_endpoint_word :
    encodeG1Frames reqTrue ++ [G1Frame.blank] =
      [.bof, .tag, .argSep, .index, .index, .argSep, .separator,
        .data false, .data false, .data true, .output false, .finish, .blank] :=
  rfl

theorem literal_zero_endpoint_word :
    encodeG1Frames reqZero ++ [G1Frame.blank] =
      [.bof, .tag, .argSep, .argSep, .separator, .data true,
        .output false, .finish, .blank] := rfl

end G1ARepairExamples

end Pnp3.Internal.PsubsetPpoly.TM
