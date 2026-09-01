import Complexity.TMVerifier.TuringToolkit.GateOneARepair
import Complexity.TMVerifier.TuringToolkit.GateOnePassADriverTraceSafety

/-!
# GN-3B2e3: complete live operand-A repair trace safety (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module follows the merged e2 `aRepairStart` endpoint through the actual
left-moving entry and the existing reject-aware `GateOneARepair` sweep.  The
reverse proof exposes the physical `p3 -> p2 -> p1 -> p0` rows and the exact
`G1ARepairStop` alternatives.  A continued skip requires a positive frame
base; `spent`, `bof`, malformed and reserved windows use stationary stop rows.
In particular, the `bof` row at head zero never appeals to left clamping.

The thirteen-step rewrite proof uses its exact `4 + 4 + 5` physical
decomposition: reverse stop, `spent -> index` writer, then back-walk and hop.
It therefore remains valid for the leftmost legal operand-A frame, where a
coarse thirteen-cell margin would be false.  Exact execution theorems are used
only to transport adjacent `G1RunSafe` segments.

The capstones stop at the exact canonical head-zero `aRepairDone` endpoint.
Malformed/reserved rejection is represented only by the existing repair stop
row; no successful canonical sweep crosses such a window.  There is no
result/combine/output/pass-A successor, full-gate `ShiftRunSafe`, unary/const
route, controller, clock, verdict or acceptance theorem here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private theorem g1ARepair_runSafe_one {W : Nat}
    (c : Configuration (M := G1M) W) (h : G1LocalStepSafe c) :
    G1RunSafe c 1 := by
  simpa using G1RunSafe.succ (G1RunSafe.empty c) h

/-! ## Physical reverse frame -/

/-- Four actual A-repair reverse-buffer rows are safe.  Non-stop completion
may move left only from a positive base; every `G1ARepairStop` completion is
stationary, including write, done and reject at base zero. -/
theorem g1ARepair_reverseFrame_runSafe {W base : Nat}
    (tape : Fin (G1M.tapeLength W) -> Bool) (ctx : G1Ctx)
    (hroom : base + 4 < gnLocalSpan W)
    (hfinal : 0 < base ∨
      G1ARepairStop (g1ARepairBackComplete
        (tape ⟨base, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 1, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 2, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 3, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩))) :
    G1RunSafe
      (g1AlignedConfig W (base + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aRepairSeek .p3 false false false ctx) 4 := by
  let hb0 : base < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb1 : base + 1 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb2 : base + 2 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let hb3 : base + 3 < G1M.tapeLength W :=
    lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  let b3 := tape ⟨base + 3, hb3⟩
  let b2 := tape ⟨base + 2, hb2⟩
  let b1 := tape ⟨base + 1, hb1⟩
  let b0 := tape ⟨base, hb0⟩
  let c3 := g1AlignedConfig W (base + 3) hb3 tape .aRepairSeek .p3
    false false false ctx
  let c2 := g1AlignedConfig W (base + 2) hb2 tape .aRepairSeek .p2
    false false b3 ctx
  let c1 := g1AlignedConfig W (base + 1) hb1 tape .aRepairSeek .p1
    false b2 b3 ctx
  let c0 := g1AlignedConfig W base hb0 tape .aRepairSeek .p0 b1 b2 b3 ctx
  have hs3 : TM.stepConfig (M := G1M) c3 = c2 := by
    have h := g1CS_aligned_step_left W (base + 3) hb3 (by omega) tape
      (g1State .aRepairSeek .p3 false false false ctx)
      (g1State .aRepairSeek .p2 false false b3 ctx) _
      (fun phase =>
        g1Transition_aRepairSeek_p3 phase false false false _ ctx)
    rw [writeCell_self] at h
    simpa [c3, c2, b3] using h
  have hs2 : TM.stepConfig (M := G1M) c2 = c1 := by
    have h := g1CS_aligned_step_left W (base + 2) hb2 (by omega) tape
      (g1State .aRepairSeek .p2 false false b3 ctx)
      (g1State .aRepairSeek .p1 false b2 b3 ctx) _
      (fun phase =>
        g1Transition_aRepairSeek_p2 phase false false b3 _ ctx)
    rw [writeCell_self] at h
    simpa [c2, c1, b2] using h
  have hs1 : TM.stepConfig (M := G1M) c1 = c0 := by
    have h := g1CS_aligned_step_left W (base + 1) hb1 (by omega) tape
      (g1State .aRepairSeek .p1 false b2 b3 ctx)
      (g1State .aRepairSeek .p0 b1 b2 b3 ctx) _
      (fun phase =>
        g1Transition_aRepairSeek_p1 phase false b2 b3 _ ctx)
    rw [writeCell_self] at h
    simpa [c1, c0, b1] using h
  have hl3 : G1LocalStepSafe c3 := by
    apply g1LocalStepSafe_of_interior
    all_goals simp [c3] at hroom ⊢
    all_goals omega
  have hl2 : G1LocalStepSafe c2 := by
    apply g1LocalStepSafe_of_interior
    all_goals simp [c2] at hroom ⊢
    all_goals omega
  have hl1 : G1LocalStepSafe c1 := by
    apply g1LocalStepSafe_of_interior
    all_goals simp [c1] at hroom ⊢
    all_goals omega
  have hl0 : G1LocalStepSafe c0 := by
    simp only [G1LocalStepSafe, c0, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by omega, ?_, ?_⟩
    · intro hleft
      by_cases hstop : G1ARepairStop
          (g1ARepairBackComplete b0 b1 b2 b3)
      · change (g1Transition (0 : Fin 1)
          (g1State .aRepairSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
            Move.left at hleft
        have htr := g1ARepairScanner.rstep_p0_stop (m := .aRepairSeek)
          trivial ctx b1 b2 b3 b0 hstop
        change g1Transition 0
            (g1State .aRepairSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1ARepairStopState
            (g1ARepairBackComplete b0 b1 b2 b3) ctx, b0, Move.stay) at htr
        rw [htr] at hleft
        exact Move.noConfusion hleft
      · rcases hfinal with hpos | hstop'
        · simpa [c0] using hpos
        · exact (hstop (by simpa [b0, b1, b2, b3] using hstop')).elim
    · intro hright
      by_cases hstop : G1ARepairStop
          (g1ARepairBackComplete b0 b1 b2 b3)
      · change (g1Transition (0 : Fin 1)
          (g1State .aRepairSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
            Move.right at hright
        have htr := g1ARepairScanner.rstep_p0_stop (m := .aRepairSeek)
          trivial ctx b1 b2 b3 b0 hstop
        change g1Transition 0
            (g1State .aRepairSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1ARepairStopState
            (g1ARepairBackComplete b0 b1 b2 b3) ctx, b0, Move.stay) at htr
        rw [htr] at hright
        exact Move.noConfusion hright
      · change (g1Transition (0 : Fin 1)
          (g1State .aRepairSeek .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
            Move.right at hright
        have htr := g1ARepairScanner.rstep_p0 (m := .aRepairSeek) trivial ctx
          b1 b2 b3 b0 hstop
        change g1Transition 0
            (g1State .aRepairSeek .p0 b1 b2 b3 ctx) b0 =
          (0, g1State (g1ARepairBackComplete b0 b1 b2 b3) .p3
            false false false ctx, b0, Move.left) at htr
        rw [htr] at hright
        exact Move.noConfusion hright
  have hr1 : TM.runConfig (M := G1M) c3 1 = c2 := by
    simpa only [runConfig_one] using hs3
  have hr2 : TM.runConfig (M := G1M) c3 2 = c1 := by
    rw [show (2 : Nat) = 1 + 1 by omega, runConfig_add, hr1, runConfig_one,
      hs2]
  have hr3 : TM.runConfig (M := G1M) c3 3 = c0 := by
    rw [show (3 : Nat) = 2 + 1 by omega, runConfig_add, hr2, runConfig_one,
      hs1]
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with
    rfl | rfl | rfl | rfl
  · exact hl3
  · rw [hr1]; exact hl2
  · rw [hr2]; exact hl1
  · rw [hr3]; exact hl0

/-! ## Skip and rewrite runs -/

/-- A complete successful `G1RepairSkip` run is safe for four physical steps
per frame. -/
theorem g1CS_aRepair_scan_skip_runSafe {W : Nat}
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hpre : 0 < pre.length) (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hroom : 4 * (pre.length + skipped.length) + 3 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) - 1) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx) (4 * skipped.length) := by
  induction skipped using List.reverseRecOn generalizing suffix with
  | nil => exact G1RunSafe.empty _
  | append_singleton rest frame ih =>
      have hrest : ∀ f ∈ rest, G1RepairSkip f :=
        fun f hf => hskip f (by simp [hf])
      have hlocal : 4 * (pre.length + rest.length) + 4 < gnLocalSpan W := by
        simp only [List.length_append, List.length_singleton] at hroom
        omega
      have hsafe : 4 * (pre.length + rest.length) + 4 <
          G1M.tapeLength W :=
        lt_of_lt_of_le hlocal (gnLocalSpan_le_g1_tapeLength W)
      have hfirst := g1ARepair_reverseFrame_runSafe
        (W := W) (base := 4 * (pre.length + rest.length))
        (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
          G1Frame.bits)) ctx hlocal (Or.inl (by omega))
      have hexact := g1CS_aRepair_frame_skip W
        (4 * (pre.length + rest.length)) (by omega) hsafe
        (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
          G1Frame.bits)) ctx frame (hskip frame (by simp)) (by
          have h := physicalBitsAt_flatMap (L := G1M.tapeLength W)
            g1FrameCodec (pre ++ rest) suffix frame (by simpa using hsafe)
          simpa [List.append_assoc] using h)
      have htail := ih (suffix := frame :: suffix) hrest (by
        simp only [List.length_append, List.length_singleton] at hroom ⊢
        omega)
      have htail' : G1RunSafe
          (TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * (pre.length + (rest ++ [frame]).length) - 1)
              (by
                apply lt_of_lt_of_le (b := gnLocalSpan W)
                · simp only [List.length_append, List.length_singleton]
                    at hroom ⊢
                  omega
                · exact gnLocalSpan_le_g1_tapeLength W)
              (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
                G1Frame.bits)) .aRepairSeek .p3 false false false ctx) 4)
          (4 * rest.length) := by
        have ht : G1RunSafe
            (TM.runConfig (M := G1M)
              (g1AlignedConfig W (4 * (pre.length + rest.length) + 3) (by
                exact lt_of_lt_of_le (by omega)
                  (gnLocalSpan_le_g1_tapeLength W))
                (g1ListTape ((pre ++ (rest ++ [frame]) ++ suffix).flatMap
                  G1Frame.bits)) .aRepairSeek .p3 false false false ctx) 4)
            (4 * rest.length) := by
          apply G1RunSafe.transport hexact.symm
          simpa [List.append_assoc] using htail
        simpa only [List.length_append, List.length_singleton] using ht
      have hadd := G1RunSafe.add (by
        simpa only [List.length_append, List.length_singleton,
          show 4 * (pre.length + (rest.length + 1)) - 1 =
            4 * (pre.length + rest.length) + 3 by omega] using hfirst) htail'
      simpa [Nat.mul_add, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hadd

/-- One exact thirteen-step `spent -> index` cycle is safe with its true local
footprint.  Its actual A route has two preceding frames (`bof` and the
nonempty tag/`argSep` left block), enough for the four-step writer margin. -/
theorem g1CS_aRepair_cycle_runSafe {W : Nat} (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 1 < pre.length)
    (hroom : 4 * pre.length + 9 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * pre.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx) 13 := by
  let base := 4 * pre.length
  let tape := g1ListTape (n := W)
    ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits)
  have hsafe : base + 4 < G1M.tapeLength W := by
    exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)
  have hbits : physicalBitsAt hsafe tape = G1Frame.spent.bits := by
    simpa [base, tape] using physicalBitsAt_flatMap
      (L := G1M.tapeLength W) g1FrameCodec pre suffix G1Frame.spent hsafe
  have hcomplete : g1ARepairBackComplete
      (tape ⟨base, by omega⟩) (tape ⟨base + 1, by omega⟩)
      (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩) =
      .aRepairWrite := by
    have h := g1ARepairScanner.revComplete_of_bits .aRepairSeek .spent hbits
    simpa [g1ARepairScanner] using h
  have hrev := g1ARepair_reverseFrame_runSafe (W := W) (base := base)
    tape ctx (by omega) (Or.inl (by dsimp [base]; omega))
  have hrevExact : TM.runConfig (M := G1M)
      (g1AlignedConfig W (base + 3) (by omega) tape .aRepairSeek .p3
        false false false ctx) 4 =
    g1AlignedConfig W base (by omega) tape .aRepairWrite .p0
      false false false ctx := by
    simpa [g1ARepairScanner, g1ARepairStopState] using
      g1ARepairScanner.revAnchorStep W base hsafe tape .aRepairSeek .spent ctx
        trivial (Or.inl rfl) hbits
  have hwrite0 : G1RunSafe
      (g1AlignedConfig W base (by omega) tape .aRepairWrite .p0
        false false false ctx) 4 := by
    apply g1RunSafe_of_margins
    · simp [base]
      omega
    · simp only [g1AlignedConfig_head_val]
      omega
  have hwrite : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) 4) 4 := by
    rw [hrevExact]
    exact hwrite0
  let tape' := writeFrame4 base false false true true tape
  have hwriteExact : TM.runConfig (M := G1M)
      (g1AlignedConfig W base (by omega) tape .aRepairWrite .p0
        false false false ctx) 4 =
    g1AlignedConfig W (base + 4) hsafe tape' .aRepairBack .p0
      false false false ctx := by
    simpa [g1ARepairCycle, g1ARepairScanner, tape'] using
      g1ARepairCycle.toWriter.writeMacrostep W base hsafe tape ctx
  have hbackHop0 : G1RunSafe
      (g1AlignedConfig W (base + 4) hsafe tape' .aRepairBack .p0
        false false false ctx) 5 := by
    apply g1RunSafe_of_margins
    · simp [base]
      omega
    · simp only [g1AlignedConfig_head_val]
      omega
  have hbackHop : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W (base + 3) (by omega) tape .aRepairSeek .p3
          false false false ctx) (4 + 4)) 5 := by
    rw [runConfig_add, hrevExact, hwriteExact]
    exact hbackHop0
  have hall := G1RunSafe.add (G1RunSafe.add hrev hwrite) hbackHop
  simpa [base, tape] using hall

/-- A contiguous spent run is safe for exactly thirteen steps per rewritten
frame, preserving the already-repaired index suffix after each cycle. -/
theorem g1CS_aRepair_spent_run_runSafe {W : Nat}
    (pre suffix : List G1Frame) (s : Nat) (ctx : G1Ctx)
    (hpre : 1 < pre.length)
    (hroom : 4 * (pre.length + s) + 5 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + s) - 1) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ List.replicate s G1Frame.spent ++ suffix).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx) (13 * s) := by
  induction s generalizing pre with
  | zero => exact G1RunSafe.empty _
  | succ s ih =>
      let start := g1AlignedConfig W
        (4 * ((pre ++ [G1Frame.spent]).length + s) - 1) (by
          apply lt_of_lt_of_le (b := gnLocalSpan W)
          · simp at hroom ⊢
            omega
          · exact gnLocalSpan_le_g1_tapeLength W)
        (g1ListTape (((pre ++ [G1Frame.spent]) ++
          List.replicate s G1Frame.spent ++ suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx
      have hIH : G1RunSafe start (13 * s) := by
        simpa [start] using ih (pre ++ [G1Frame.spent]) (by simp; omega)
          (by simp at hroom ⊢; omega)
      have hIHExact0 := g1CS_aRepair_spent_run W
        (pre ++ [G1Frame.spent]) suffix s ctx (by simp) (by
          exact lt_of_lt_of_le (by simp at hroom ⊢; omega)
            (gnLocalSpan_le_g1_tapeLength W))
      have hIHExact : TM.runConfig (M := G1M) start (13 * s) =
          g1AlignedConfig W (4 * pre.length + 3) (by
            exact lt_of_lt_of_le (by omega)
              (gnLocalSpan_le_g1_tapeLength W))
            (g1ListTape ((pre ++ G1Frame.spent ::
              (List.replicate s G1Frame.index ++ suffix)).flatMap
              G1Frame.bits)) .aRepairSeek .p3 false false false ctx := by
        simpa [start, List.append_assoc] using hIHExact0
      have hcycle := g1CS_aRepair_cycle_runSafe (W := W) pre
        (List.replicate s G1Frame.index ++ suffix) ctx hpre (by omega)
      have hcycle' : G1RunSafe
          (TM.runConfig (M := G1M) start (13 * s)) 13 := by
        rw [hIHExact]
        exact hcycle
      have hadd := G1RunSafe.add hIH hcycle'
      simpa [start, List.replicate_succ, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hadd

/-- The four physical anchor rows are safe.  The `bof` completion dispatches
stationarily to `aRepairDone` at head zero. -/
theorem g1CS_aRepair_finish_runSafe {W : Nat} (suffix : List G1Frame)
    (ctx : G1Ctx) (hroom : 4 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W 3 (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .aRepairSeek .p3 false false false ctx) 4 := by
  let tape := g1ListTape (n := W) ((G1Frame.bof :: suffix).flatMap
    G1Frame.bits)
  have hsafe : 4 < G1M.tapeLength W :=
    lt_of_lt_of_le hroom (gnLocalSpan_le_g1_tapeLength W)
  have hbits : physicalBitsAt hsafe tape = G1Frame.bof.bits := by
    simpa [tape] using physicalBitsAt_flatMap (L := G1M.tapeLength W)
      g1FrameCodec ([] : List G1Frame) suffix G1Frame.bof hsafe
  have hcomplete : g1ARepairBackComplete
      (tape ⟨0, by omega⟩) (tape ⟨1, by omega⟩)
      (tape ⟨2, by omega⟩) (tape ⟨3, by omega⟩) = .aRepairDone := by
    have h := g1ARepairScanner.revComplete_of_bits .aRepairSeek .bof hbits
    simpa [g1ARepairScanner] using h
  have h := g1ARepair_reverseFrame_runSafe (W := W) (base := 0) tape ctx
    (by omega) (Or.inr (by
      rw [hcomplete]
      exact Or.inr (Or.inl rfl)))
  simpa [tape] using h

/-! ## Complete sweep and live entry -/

set_option maxHeartbeats 1000000 in
/-- Generic complete A-repair sweep safety on the exact public decomposition
`4 * mid.length + 13 * s + 4 * left.length + 4`. -/
theorem g1CS_aRepair_pass_runSafe {W s : Nat}
    (left mid tail : List G1Frame) (ctx : G1Ctx)
    (hleftPos : 0 < left.length)
    (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hmid : ∀ f ∈ mid, G1RepairSkip f)
    (hroom : 4 * (1 + left.length + s + mid.length) + 9 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
        (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
      (g1ARepairPassSteps left.length s mid.length) := by
  have hTL : 4 * (1 + left.length + s + mid.length) + 9 <
      G1M.tapeLength W :=
    lt_of_lt_of_le hroom (gnLocalSpan_le_g1_tapeLength W)
  have hmidSafe0 := g1CS_aRepair_scan_skip_runSafe
    (W := W) ([G1Frame.bof] ++ left ++ List.replicate s G1Frame.spent)
    mid tail ctx (by simp) hmid (by
      simp only [List.length_append, List.length_singleton,
        List.length_replicate] at hroom ⊢
      omega)
  have hmidExact := g1CS_aRepair_scan_skip W
    ([G1Frame.bof] ++ left ++ List.replicate s G1Frame.spent) mid tail ctx
    (by simp) hmid (by
      simp only [List.length_append, List.length_singleton,
        List.length_replicate] at hTL ⊢
      omega)
  have hmidSafe : G1RunSafe
      (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
        (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
      (4 * mid.length) := by
    simpa only [List.length_append, List.length_singleton,
      List.length_replicate] using hmidSafe0
  have hmidExact' : TM.runConfig (M := G1M)
      (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
        (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
          G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
      (4 * mid.length) =
    g1AlignedConfig W (4 * (1 + left.length + s) - 1) (by omega)
      (g1ListTape (([G1Frame.bof] ++ left ++
        List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
        G1Frame.bits)) .aRepairSeek .p3 false false false ctx := by
    simpa only [List.length_append, List.length_singleton,
      List.length_replicate] using hmidExact
  have hspent0 := g1CS_aRepair_spent_run_runSafe (W := W)
    ([G1Frame.bof] ++ left) (mid ++ tail) s ctx (by simp; omega) (by
      simp only [List.length_append, List.length_singleton] at hroom ⊢
      omega)
  have hspent : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
          (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          (g1ListTape (([G1Frame.bof] ++ left ++
            List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
            G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
        (4 * mid.length)) (13 * s) := by
    rw [hmidExact']
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hspent0
  have hprefix := G1RunSafe.add hmidSafe hspent
  have hspentExact := g1CS_aRepair_spent_run W ([G1Frame.bof] ++ left)
    (mid ++ tail) s ctx (by simp) (by
      simp only [List.length_append, List.length_singleton] at hTL ⊢
      omega)
  have hafterSpent : TM.runConfig (M := G1M)
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
          (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          (g1ListTape (([G1Frame.bof] ++ left ++
            List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
            G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
        (4 * mid.length)) (13 * s) =
    g1AlignedConfig W (4 * (1 + left.length) - 1) (by omega)
      (g1ListTape (([G1Frame.bof] ++ left ++
        List.replicate s G1Frame.index ++ mid ++ tail).flatMap
        G1Frame.bits)) .aRepairSeek .p3 false false false ctx := by
    rw [hmidExact']
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hspentExact
  have hleft0 := g1CS_aRepair_scan_skip_runSafe (W := W) [G1Frame.bof]
    left (List.replicate s G1Frame.index ++ mid ++ tail) ctx (by simp)
    hleft (by
      simp only [List.length_singleton] at hroom ⊢
      omega)
  have hleftSafe : G1RunSafe
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
            (by
              exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
            (g1ListTape (([G1Frame.bof] ++ left ++
              List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
              G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
          (4 * mid.length)) (13 * s)) (4 * left.length) := by
    rw [hafterSpent]
    simpa [List.append_assoc] using hleft0
  have hprefix2 := G1RunSafe.add hprefix (by
    simpa only [runConfig_add] using hleftSafe)
  have hleftExact := g1CS_aRepair_scan_skip W [G1Frame.bof] left
    (List.replicate s G1Frame.index ++ mid ++ tail) ctx (by simp) hleft (by
      simp only [List.length_singleton] at hTL ⊢
      omega)
  have hafterLeft : TM.runConfig (M := G1M)
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (g1AlignedConfig W (4 * (1 + left.length + s + mid.length) - 1)
            (by
              exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
            (g1ListTape (([G1Frame.bof] ++ left ++
              List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
              G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
          (4 * mid.length)) (13 * s)) (4 * left.length) =
    g1AlignedConfig W 3 (by omega)
      (g1ListTape (([G1Frame.bof] ++ left ++
        List.replicate s G1Frame.index ++ mid ++ tail).flatMap
        G1Frame.bits)) .aRepairSeek .p3 false false false ctx := by
    rw [hafterSpent]
    simpa [List.append_assoc] using hleftExact
  have hfinish0 := g1CS_aRepair_finish_runSafe (W := W)
    (left ++ List.replicate s G1Frame.index ++ mid ++ tail) ctx (by omega)
  have hfinish : G1RunSafe
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (TM.runConfig (M := G1M)
            (g1AlignedConfig W
              (4 * (1 + left.length + s + mid.length) - 1)
              (by
                exact lt_of_lt_of_le (by omega)
                  (gnLocalSpan_le_g1_tapeLength W))
              (g1ListTape (([G1Frame.bof] ++ left ++
                List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
                G1Frame.bits)) .aRepairSeek .p3 false false false ctx)
            (4 * mid.length)) (13 * s)) (4 * left.length)) 4 := by
    rw [hafterLeft]
    simpa [List.append_assoc] using hfinish0
  have hall := G1RunSafe.add hprefix2 (by
    simpa only [runConfig_add, Nat.add_assoc] using hfinish)
  simpa [g1ARepairPassSteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hall

/-- Request-specific aligned repair safety, exactly `g1ARepairSteps r`. -/
theorem g1CS_aRepair_sweep_runSafe (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1ARepairEntryConfig r b v hm hv) (g1ARepairSteps r) := by
  have h := g1CS_aRepair_pass_runSafe (W := (encodeG1 r).length)
    (s := r.arg1) (g1ARepairLeft r) (g1ARepairMid r) (g1ARepairTail r)
    (g1AWalkCtx r b v) (by simp [g1ARepairLeft])
    (g1ARepairLeft_skip r) (g1ARepairMid_skip r) (by
      rw [g1ARepairLeft_length, g1ARepairMid_length r hm]
      simp [gnLocalSpan, encodeG1_length]
      omega)
  rw [← g1AWalkDoneFrames_repair_split r] at h
  simpa [g1ARepairEntryConfig, g1ARepairSteps_eq r hm] using h

/-- The live `aRepairStart` left-entry row is safe because its actual head is
strictly positive and remains strictly inside the local footprint. -/
theorem g1CS_aRepair_activation_runSafe (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkRepairStartConfig r b v hm hv) 1 := by
  apply g1ARepair_runSafe_one
  apply g1LocalStepSafe_of_interior
  · simp [g1AWalkRepairStartConfig, g1AWalkCursor]
  · simp [g1AWalkRepairStartConfig, g1AWalkCursor, gnLocalSpan,
      encodeG1_length]
    omega

/-- Complete live repair safety paired with the exact canonical endpoint. -/
theorem g1CS_aRepair_live_trace_safe (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkRepairStartConfig r b v hm hv)
        (g1ARepairLiveSteps r) ∧
      TM.runConfig (M := G1M) (g1AWalkRepairStartConfig r b v hm hv)
          (g1ARepairLiveSteps r) = g1ARepairDoneConfig r b v := by
  have hentry := g1CS_aRepair_activation_runSafe r b v hm hv
  have hsweep0 := g1CS_aRepair_sweep_runSafe r b v hm hv
  have hsweep : G1RunSafe
      (TM.runConfig (M := G1M) (g1AWalkRepairStartConfig r b v hm hv) 1)
      (g1ARepairSteps r) :=
    G1RunSafe.transport (g1CS_aRepair_activation_exact r b v hm hv).symm
      hsweep0
  exact ⟨by simpa [g1ARepairLiveSteps] using G1RunSafe.add hentry hsweep,
    g1CS_aRepair_live_exact r b v hm hv⟩

/-- Kernel-visible live endpoint: canonical tape at head zero, empty repair
markers, all operand indices restored, and both carried values preserved. -/
theorem g1CS_aRepair_live_structure (r : G1Request) (b v : Bool)
    (hm : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    let out := TM.runConfig (M := G1M)
      (g1AWalkRepairStartConfig r b v hm hv) (g1ARepairLiveSteps r)
    out.tape = g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
        G1Frame.bits) ∧
      (out.head : Nat) = 0 ∧
      out.state.snd = g1ARepairDoneState (g1AWalkCtx r b v) ∧
      out.state.snd.ctx = g1AWalkCtx r b v ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .spent = 0 ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .cursor = 0 ∧
      (encodeG1Frames r ++ [G1Frame.blank]).count .index = r.arg1 + r.arg2 := by
  dsimp only
  rw [g1CS_aRepair_live_exact r b v hm hv]
  exact ⟨rfl, rfl, rfl, rfl, g1AWalkCtx_res r b v, rfl,
    g1ARepairCanonical_count_spent r, g1ARepairCanonical_count_cursor r,
    g1ARepairCanonical_count_index r⟩

/-! ## Merged e2 binary composition -/

/-- Exact public decomposition of the existing binary repair schedule into
the merged e2 prefix and live e3 repair suffix. -/
theorem g1ABinaryRepairSteps_trace_eq (r : G1Request) :
    g1ABinaryRepairSteps r =
      (g1ABinaryCursorSteps r +
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) +
      g1ARepairLiveSteps r := by
  simp [g1ABinaryRepairSteps, g1AWalkRepairSteps]
  omega

/-- Successful binary real-initial safety through the exact existing binary
schedule, ending at canonical `aRepairDone`. -/
theorem g1CS_aRepair_binary_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (v : Nat -> Bool) (hv : ∀ j, j ≤ r.arg1 -> r.vals[j]? = some (v j))
    (hvals : r.vals = bA :: rest) (hv0 : v 0 = bA) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryRepairSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryRepairSteps r) =
        g1ARepairDoneConfig r bB (v r.arg1) := by
  have hlen : r.arg1 < r.vals.length := by
    exact (List.getElem?_eq_some_iff.1 (hv r.arg1 (Nat.le_refl _))).1
  have hprefix := g1CS_readA_binary_full_driver_from_initial_trace_safe r hc ht
    bA bB rest hB v hv hvals hv0
  have hlive0 := g1CS_aRepair_live_trace_safe r bB (v r.arg1) hlen
    (hv r.arg1 (Nat.le_refl _))
  have hlive : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r +
          (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)))
      (g1ARepairLiveSteps r) :=
    G1RunSafe.transport hprefix.2.symm hlive0.1
  rw [g1ABinaryRepairSteps_trace_eq]
  exact ⟨G1RunSafe.add hprefix.1 hlive, by
    rw [runConfig_add, hprefix.2, hlive0.2]⟩

/-! ## Literal schedule pins -/

namespace G1ARepairTraceProbes

open G1ARepairExamples
open G1PassATraceProbes

theorem literal_false_local_trace_safe :
    G1RunSafe
        (g1ARepairEntryConfig reqFalse false false (by decide) (by decide)) 58 ∧
      TM.runConfig (M := G1M)
          (g1ARepairEntryConfig reqFalse false false (by decide) (by decide)) 58 =
        g1ARepairDoneConfig reqFalse false false := by
  exact ⟨by simpa [reqFalse] using
      g1CS_aRepair_sweep_runSafe reqFalse false false (by decide) (by decide),
    literal_false_repair_exact⟩

theorem literal_true_local_trace_safe :
    G1RunSafe
        (g1ARepairEntryConfig reqTrue true true (by decide) (by decide)) 58 ∧
      TM.runConfig (M := G1M)
          (g1ARepairEntryConfig reqTrue true true (by decide) (by decide)) 58 =
        g1ARepairDoneConfig reqTrue true true := by
  exact ⟨by simpa [reqTrue] using
      g1CS_aRepair_sweep_runSafe reqTrue true true (by decide) (by decide),
    literal_true_repair_exact⟩

theorem literal_zero_local_trace_safe :
    G1RunSafe
        (g1ARepairEntryConfig reqZero false true (by decide) (by decide)) 24 ∧
      TM.runConfig (M := G1M)
          (g1ARepairEntryConfig reqZero false true (by decide) (by decide)) 24 =
        g1ARepairDoneConfig reqZero false true := by
  exact ⟨by simpa [reqZero] using
      g1CS_aRepair_sweep_runSafe reqZero false true (by decide) (by decide),
    literal_zero_arg1_repair_exact⟩

theorem literal_binary_steps : g1ABinaryRepairSteps reqA = 541 := by decide

/-- The existing binary e1/e2 request completes repair in 541 genuine steps;
this total is binary and is not one of the unary 404/192 totals. -/
theorem literal_binary_initial_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 541 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 541 =
        g1ARepairDoneConfig reqA true true := by
  have h := g1CS_aRepair_binary_initial_trace_safe reqA (by decide)
    (Or.inl rfl) true true [true, false] (by decide)
    (fun j => [true, true, false][j]!) (by decide) rfl (by decide)
  rw [literal_binary_steps] at h
  simpa [reqA] using h

end G1ARepairTraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
