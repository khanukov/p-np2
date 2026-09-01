import Complexity.TMVerifier.TuringToolkit.GateOnePassATraceSafety
import Complexity.TMVerifier.TuringToolkit.GateOneAWalkRound

/-!
# GN-3B2e1b: one-round pass-A trace safety (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module extends the merged e1a binary installation endpoint `SigmaA(0)`
through exactly one successful operand-A round.  Its reverse safety layer is
structural: it follows the actual four buffered cells, `g1ASeekRevComplete`,
`g1ASeekRevAdvance`, `G1ASeekStop`, physical head positions, tape and context.
It contains no reachability, run-index or target-safety fields.

The unique mixed seek crosses `inner ++ argSep ++ outer` right-to-left, changing
from `aSeekOut` to `aSeekIn`, with the exact schedule of
`ReverseFrameScanner.revSeekAcrossBoundary`.  All bounds are strict local-span
bounds, so no clamped head movement is used.  Exact execution endpoints are
used only to transport adjacent `G1RunSafe` segments and compose them with
`G1RunSafe.add`.

Successor-data OOB and operand-index exhaustion remain the separate endpoints
of `GateOneAWalkRound`.  There is no driver induction, terminal cleanup,
A-repair, unary/constant route, result/output/full-gate shifted safety,
controller, clock or acceptance theorem here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

private theorem g1ASeek_not_stop_of_mode {mode : G1Mode}
    (hmode : G1ASeekMode mode) : ¬ G1ASeekStop mode := by
  rcases hmode.eq with rfl | rfl <;> simp [G1ASeekStop]

private theorem g1AAlignedConfig_congr (W h h' : Nat)
    (hh : h < G1M.tapeLength W) (hh' : h' < G1M.tapeLength W)
    (heq : h = h') (tape : Fin (G1M.tapeLength W) -> Bool)
    (mode : G1Mode) (pos : G1FramePosition) (b0 b1 b2 : Bool) (ctx : G1Ctx) :
    g1AlignedConfig W h hh tape mode pos b0 b1 b2 ctx =
      g1AlignedConfig W h' hh' tape mode pos b0 b1 b2 ctx := by
  subst h'
  rfl

/-! ## The physical four-cell reverse frame -/

/-- Four actual A-seek buffer steps are locally safe on one physical frame.
The final row may move left only when `base > 0`; otherwise the decoded A table
must stop.  The statement carries the real tape bits and context verbatim. -/
theorem g1ASeek_reverseFrame_runSafe {W base : Nat}
    (tape : Fin (G1M.tapeLength W) -> Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : G1ASeekMode mode) (hroom : base + 4 < gnLocalSpan W)
    (hfinal : 0 < base ∨
      G1ASeekStop (g1ASeekRevComplete mode (tape ⟨base, by
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
        mode .p3 false false false ctx) 4 := by
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
  let c3 := g1AlignedConfig W (base + 3) hb3 tape mode .p3 false false false ctx
  let c2 := g1AlignedConfig W (base + 2) hb2 tape mode .p2 false false b3 ctx
  let c1 := g1AlignedConfig W (base + 1) hb1 tape mode .p1 false b2 b3 ctx
  let c0 := g1AlignedConfig W base hb0 tape mode .p0 b1 b2 b3 ctx
  have hs3 : TM.stepConfig (M := G1M) c3 = c2 := by
    have h := g1CS_aligned_step_left W (base + 3) hb3 (by omega) tape
      (g1State mode .p3 false false false ctx)
      (g1State mode .p2 false false b3 ctx) _ (by
        intro phase
        rcases hmode.eq with rfl | rfl
        · exact g1Transition_aSeekOut_p3 phase _ _ _ _ _
        · exact g1Transition_aSeekIn_p3 phase _ _ _ _ _)
    rw [writeCell_self] at h
    simpa [c3, c2, b3] using h
  have hs2 : TM.stepConfig (M := G1M) c2 = c1 := by
    have h := g1CS_aligned_step_left W (base + 2) hb2 (by omega) tape
      (g1State mode .p2 false false b3 ctx)
      (g1State mode .p1 false b2 b3 ctx) _ (by
        intro phase
        rcases hmode.eq with rfl | rfl
        · exact g1Transition_aSeekOut_p2 phase _ _ _ _ _
        · exact g1Transition_aSeekIn_p2 phase _ _ _ _ _)
    rw [writeCell_self] at h
    simpa [c2, c1, b2] using h
  have hs1 : TM.stepConfig (M := G1M) c1 = c0 := by
    have h := g1CS_aligned_step_left W (base + 1) hb1 (by omega) tape
      (g1State mode .p1 false b2 b3 ctx)
      (g1State mode .p0 b1 b2 b3 ctx) _ (by
        intro phase
        rcases hmode.eq with rfl | rfl
        · exact g1Transition_aSeekOut_p1 phase _ _ _ _ _
        · exact g1Transition_aSeekIn_p1 phase _ _ _ _ _)
    rw [writeCell_self] at h
    simpa [c1, c0, b1] using h
  have hlocal3 : G1LocalStepSafe c3 := by
    apply g1LocalStepSafe_of_interior
    · simp [c3]
    · simp [c3, gnLocalSpan] at hroom ⊢
      omega
  have hlocal2 : G1LocalStepSafe c2 := by
    apply g1LocalStepSafe_of_interior
    · simp [c2]
    · simp [c2, gnLocalSpan] at hroom ⊢
      omega
  have hlocal1 : G1LocalStepSafe c1 := by
    apply g1LocalStepSafe_of_interior
    · simp [c1]
    · simp [c1, gnLocalSpan] at hroom ⊢
      omega
  have hlocal0 : G1LocalStepSafe c0 := by
    simp only [G1LocalStepSafe, c0, g1AlignedConfig_head_val,
      g1AlignedConfig_state, g1AlignedConfig_tape]
    refine ⟨by simpa [gnLocalSpan] using (show base < gnLocalSpan W by omega),
      ?_, ?_⟩
    · intro hleft
      by_cases hstop : G1ASeekStop (g1ASeekRevComplete mode b0 b1 b2 b3)
      · have htr := g1AWalkScanner.rstep_p0_stop hmode ctx b1 b2 b3 b0 hstop
        change g1Transition 0 (g1State mode .p0 b1 b2 b3 ctx) b0 =
          (0, g1ASeekStopState (g1ASeekRevComplete mode b0 b1 b2 b3) ctx,
            b0, Move.stay) at htr
        change (g1Transition 0 (g1State mode .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
          Move.left at hleft
        rw [htr] at hleft
        exact Move.noConfusion hleft
      · rcases hfinal with hpos | hstop'
        · simpa [c0] using hpos
        · exact (hstop hstop').elim
    · intro hright
      by_cases hstop : G1ASeekStop (g1ASeekRevComplete mode b0 b1 b2 b3)
      · have htr := g1AWalkScanner.rstep_p0_stop hmode ctx b1 b2 b3 b0 hstop
        change g1Transition 0 (g1State mode .p0 b1 b2 b3 ctx) b0 =
          (0, g1ASeekStopState (g1ASeekRevComplete mode b0 b1 b2 b3) ctx,
            b0, Move.stay) at htr
        change (g1Transition 0 (g1State mode .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
          Move.right at hright
        rw [htr] at hright
        exact Move.noConfusion hright
      · have htr := g1AWalkScanner.rstep_p0 hmode ctx b1 b2 b3 b0 hstop
        change g1Transition 0 (g1State mode .p0 b1 b2 b3 ctx) b0 =
          (0, g1State (g1ASeekRevComplete mode b0 b1 b2 b3) .p3 false false
            false ctx, b0, Move.left) at htr
        change (g1Transition 0 (g1State mode .p0 b1 b2 b3 ctx) b0).snd.snd.snd =
          Move.right at hright
        rw [htr] at hright
        exact Move.noConfusion hright
  have hr1 : TM.runConfig (M := G1M) c3 1 = c2 := by
    simpa only [runConfig_one] using hs3
  have hr2 : TM.runConfig (M := G1M) c3 2 = c1 := by
    rw [show (2 : Nat) = 1 + 1 by omega, runConfig_add, hr1, runConfig_one, hs2]
  have hr3 : TM.runConfig (M := G1M) c3 3 = c0 := by
    rw [show (3 : Nat) = 2 + 1 by omega, runConfig_add, hr2, runConfig_one, hs1]
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with
    rfl | rfl | rfl | rfl
  · exact hlocal3
  · rw [hr1]; exact hlocal2
  · rw [hr2]; exact hlocal1
  · rw [hr3]; exact hlocal0

/-! ## Homogeneous reverse runs -/

/-- A homogeneous A-seek run is safe for exactly four steps per frame. -/
theorem g1ASeek_revSkip_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (mode : G1Mode)
    (ctx : G1Ctx) (hmode : G1ASeekMode mode)
    (hskip : ∀ f, f ∈ skipped -> g1ASeekRevAdvance mode f = mode)
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) mode .p3 false false false ctx)
      (4 * skipped.length) := by
  induction skipped using List.reverseRecOn generalizing suffix with
  | nil => exact G1RunSafe.empty _
  | append_singleton rest frame ih =>
      have hframe : g1ASeekRevAdvance mode frame = mode :=
        hskip frame (by simp)
      have hrest : ∀ f, f ∈ rest -> g1ASeekRevAdvance mode f = mode := by
        intro f hf
        exact hskip f (by simp [hf])
      have hword' : 4 * (pre.length + rest.length + 1) + 8 <
          gnLocalSpan W := by
        simpa using hword
      let tape := g1ListTape (n := W)
        ((pre ++ marker :: (rest ++ [frame]) ++ suffix).flatMap G1Frame.bits)
      have hframeSafe : G1RunSafe
          (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3) (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
            tape mode .p3 false false false ctx) 4 :=
        g1ASeek_reverseFrame_runSafe tape mode ctx hmode (by omega)
          (Or.inl (by omega))
      have hphysical : 4 * (pre ++ marker :: rest).length + 4 <
          G1M.tapeLength W := by
        apply lt_of_lt_of_le (b := gnLocalSpan W)
        · simp only [List.length_append, List.length_cons]
          omega
        · exact gnLocalSpan_le_g1_tapeLength W
      have hmacro := g1AWalkScanner.revFrameMacrostepAt W
        (4 * (pre.length + rest.length + 1))
        (4 * (pre.length + rest.length) + 3) (by omega)
        (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape mode
        frame ctx hmode (by
          change ¬ G1ASeekStop (g1ASeekRevAdvance mode frame)
          rw [hframe]
          exact g1ASeek_not_stop_of_mode hmode)
        (by
          have hbits := physicalBitsAt_flatMap (L := G1M.tapeLength W)
            g1FrameCodec (pre ++ marker :: rest) suffix frame hphysical
          simpa [tape, List.append_assoc] using hbits)
      have htail := ih (suffix := frame :: suffix) hrest (by omega)
      have hmacro' : TM.runConfig (M := G1M)
          (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3) (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
            tape mode .p3 false false false ctx) 4 =
        g1AlignedConfig W (4 * (pre.length + rest.length) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape mode .p3 false false false ctx := by
        change TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3) _
              tape mode .p3 false false false ctx) 4 =
          g1AlignedConfig W (4 * (pre.length + rest.length) + 3) _ tape
            (g1ASeekRevAdvance mode frame) .p3 false false false ctx at hmacro
        rw [hframe] at hmacro
        exact hmacro
      have htail' : G1RunSafe
          (TM.runConfig (M := G1M)
            (g1AlignedConfig W (4 * (pre.length + rest.length + 1) + 3) (by
              exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
              tape mode .p3 false false false ctx) 4)
          (4 * rest.length) := by
        rw [hmacro']
        simpa [tape, List.append_assoc] using htail
      have hadd := G1RunSafe.add hframeSafe htail'
      simpa [tape, Nat.mul_add, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hadd

/-- Homogeneous `aSeekOut` frames are safe for their exact reverse schedule. -/
theorem g1ASeekOut_revSkip_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1ASeekOutSkip f)
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) .aSeekOut .p3 false false false ctx)
      (4 * skipped.length) :=
  g1ASeek_revSkip_runSafe pre marker skipped suffix .aSeekOut ctx trivial
    (fun f hf => g1ASeekRevAdvance_out_of_skip (hskip f hf)) hword

/-- Homogeneous `aSeekIn` frames are safe for their exact reverse schedule. -/
theorem g1ASeekIn_revSkip_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1ASeekInSkip f)
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) .aSeekIn .p3 false false false ctx)
      (4 * skipped.length) :=
  g1ASeek_revSkip_runSafe pre marker skipped suffix .aSeekIn ctx trivial
    (fun f hf => g1ASeekRevAdvance_in_of_skip (hskip f hf)) hword

/-! ## The single mixed `aSeekOut` to `aSeekIn` boundary -/

private theorem g1ASeekIn_seekToMarker_runSafe {W : Nat}
    (pre : List G1Frame) (marker : G1Frame) (inner suffix : List G1Frame)
    (ctx : G1Ctx) (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hstop : G1ASeekStop (g1ASeekRevAdvance .aSeekIn marker))
    (hword : 4 * (pre.length + inner.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + inner.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: inner ++ suffix).flatMap G1Frame.bits))
        .aSeekIn .p3 false false false ctx) (4 * inner.length + 4) := by
  let tape := g1ListTape (n := W)
    ((pre ++ marker :: inner ++ suffix).flatMap G1Frame.bits)
  have hscan := g1ASeekIn_revSkip_runSafe pre marker inner suffix ctx hinner hword
  have hscanExact := g1AWalkScanner.revSkipRun W pre marker inner suffix .aSeekIn
    ctx trivial (g1ASeek_not_stop_of_mode
      (show G1ASeekMode .aSeekIn from trivial))
    (fun f hf => g1ASeekRevAdvance_in_of_skip (hinner f hf))
    (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
  have hmarker : G1RunSafe
      (g1AlignedConfig W (4 * pre.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aSeekIn .p3 false false false ctx) 4 := by
    apply g1ASeek_reverseFrame_runSafe tape .aSeekIn ctx trivial (by omega)
    right
    have hbits := physicalBitsAt_flatMap (L := G1M.tapeLength W) g1FrameCodec
      pre (inner ++ suffix) marker
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
    have hc := g1AWalkScanner.revComplete_of_bits .aSeekIn marker
      (by simpa [physicalBitsAt] using hbits)
    have hc' : g1ASeekRevComplete .aSeekIn
        (tape ⟨4 * pre.length, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨4 * pre.length + 1, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨4 * pre.length + 2, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨4 * pre.length + 3, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩) =
      g1ASeekRevAdvance .aSeekIn marker := by
      simpa [tape, List.append_assoc] using hc
    exact hc'.symm ▸ hstop
  have hmarker' : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W (4 * (pre.length + inner.length) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .aSeekIn .p3 false false false ctx) (4 * inner.length)) 4 := by
    have hscanExact' : TM.runConfig (M := G1M)
        (g1AlignedConfig W (4 * (pre.length + inner.length) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .aSeekIn .p3 false false false ctx) (4 * inner.length) =
      g1AlignedConfig W (4 * pre.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aSeekIn .p3 false false false ctx := by
      simpa [tape, g1AWalkScanner, ReverseFrameScanner.revAligned] using hscanExact
    rw [hscanExact']
    exact hmarker
  exact G1RunSafe.add hscan hmarker'

/-- The unique A mixed-boundary seek is safe on the exact
`revSeekAcrossBoundary` schedule.  It crosses `outer` in `aSeekOut`, reads the
single `argSep` mode switch, crosses `inner` in `aSeekIn`, and stops on
`marker`; the tape and context are unchanged by the structural reverse scan. -/
theorem g1ASeek_acrossBoundary_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (inner outer suffix : List G1Frame) (ctx : G1Ctx)
    (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hstop : G1ASeekStop (g1ASeekRevAdvance .aSeekIn marker))
    (hword : 4 * (pre.length + (inner.length + outer.length + 1)) + 8 <
      gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W
        (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: inner ++ .argSep :: outer ++ suffix).flatMap
          G1Frame.bits)) .aSeekOut .p3 false false false ctx)
      (4 * (inner.length + outer.length + 1) + 4) := by
  let preOut := pre ++ marker :: inner
  let tape := g1ListTape (n := W)
    ((pre ++ marker :: inner ++ .argSep :: outer ++ suffix).flatMap
      G1Frame.bits)
  have hpreOutLen : preOut.length = pre.length + inner.length + 1 := by
    simp [preOut]
    omega
  have houterSafe0 := g1ASeekOut_revSkip_runSafe (W := W) preOut .argSep outer
    suffix ctx houter (by rw [hpreOutLen]; omega)
  have houterSafe : G1RunSafe
      (g1AlignedConfig W
        (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        tape .aSeekOut .p3 false false false ctx) (4 * outer.length) := by
    simpa [preOut, tape, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using houterSafe0
  have hboundary : G1RunSafe
      (g1AlignedConfig W (4 * preOut.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aSeekOut .p3 false false false ctx) 4 := by
    apply g1ASeek_reverseFrame_runSafe tape .aSeekOut ctx trivial
      (by rw [hpreOutLen]; omega)
    left
    rw [hpreOutLen]
    omega
  have houterExact := g1AWalkScanner.revSkipRun W preOut .argSep outer suffix
    .aSeekOut ctx trivial (g1ASeek_not_stop_of_mode
      (show G1ASeekMode .aSeekOut from trivial))
    (fun f hf => g1ASeekRevAdvance_out_of_skip (houter f hf))
    (lt_of_lt_of_le (by rw [hpreOutLen]; omega)
      (gnLocalSpan_le_g1_tapeLength W))
  have hboundary' : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .aSeekOut .p3 false false false ctx) (4 * outer.length)) 4 := by
    have houterExact' : TM.runConfig (M := G1M)
        (g1AlignedConfig W
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .aSeekOut .p3 false false false ctx) (4 * outer.length) =
      g1AlignedConfig W (4 * preOut.length + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aSeekOut .p3 false false false ctx := by
      change TM.runConfig (M := G1M)
          (g1AlignedConfig W (4 * (preOut.length + outer.length) + 3) _ tape
            .aSeekOut .p3 false false false ctx) (4 * outer.length) =
        g1AlignedConfig W (4 * preOut.length + 3) _ tape .aSeekOut .p3 false
          false false ctx at houterExact
      rw [g1AAlignedConfig_congr W
        (4 * (pre.length + (inner.length + outer.length + 1)) + 3)
        (4 * (preOut.length + outer.length) + 3) _ _ (by
          rw [hpreOutLen]
          omega) tape .aSeekOut .p3 false false false ctx]
      exact houterExact
    rw [houterExact']
    exact hboundary
  have houtBoundary := G1RunSafe.add houterSafe hboundary'
  have hin0 := g1ASeekIn_seekToMarker_runSafe (W := W) pre marker inner
    ((.argSep :: outer) ++ suffix) ctx hinner hstop (by omega)
  have hin : G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + inner.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aSeekIn .p3 false false false ctx) (4 * inner.length + 4) := by
    simpa [tape, List.append_assoc] using hin0
  have hswitchExact := g1AWalkScanner.revSkipToBoundary W preOut .argSep outer
    suffix .aSeekOut .aSeekIn ctx trivial
    (g1ASeek_not_stop_of_mode (show G1ASeekMode .aSeekOut from trivial))
    (fun f hf => g1ASeekRevAdvance_out_of_skip (houter f hf)) rfl
    (g1ASeek_not_stop_of_mode (show G1ASeekMode .aSeekIn from trivial))
    (by rw [hpreOutLen]; omega)
    (lt_of_lt_of_le (by rw [hpreOutLen]; omega)
      (gnLocalSpan_le_g1_tapeLength W))
  have hin' : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AlignedConfig W
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .aSeekOut .p3 false false false ctx)
        (4 * outer.length + 4)) (4 * inner.length + 4) := by
    have hswitchExact' : TM.runConfig (M := G1M)
        (g1AlignedConfig W
          (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
            exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
          tape .aSeekOut .p3 false false false ctx)
        (4 * outer.length + 4) =
      g1AlignedConfig W (4 * (pre.length + inner.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        .aSeekIn .p3 false false false ctx := by
      change TM.runConfig (M := G1M)
          (g1AlignedConfig W (4 * (preOut.length + outer.length) + 3) _ tape
            .aSeekOut .p3 false false false ctx) (4 * outer.length + 4) =
        g1AlignedConfig W (4 * preOut.length - 1) _ tape .aSeekIn .p3 false
          false false ctx at hswitchExact
      rw [g1AAlignedConfig_congr W
        (4 * (pre.length + (inner.length + outer.length + 1)) + 3)
        (4 * (preOut.length + outer.length) + 3) _ _ (by
          rw [hpreOutLen]
          omega) tape .aSeekOut .p3 false false false ctx,
        g1AAlignedConfig_congr W (4 * (pre.length + inner.length) + 3)
          (4 * preOut.length - 1) _ _ (by
            rw [hpreOutLen]
            omega) tape .aSeekIn .p3 false false false ctx]
      exact hswitchExact
    rw [hswitchExact']
    exact hin
  have hall := G1RunSafe.add houtBoundary hin'
  simpa only [tape, show (4 * outer.length + 4) +
    (4 * inner.length + 4) = 4 * (inner.length + outer.length + 1) + 4 by
      omega] using hall

/-- The successful index-seek specialization uses the same schedule and word
shape as `g1CS_aWalk_seek_index`. -/
theorem g1CS_aWalk_seek_index_runSafe {W : Nat} (pre inner outer suffix : List G1Frame)
    (ctx : G1Ctx) (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hword : 4 * (pre.length + (inner.length + outer.length + 1)) + 8 <
      gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W
        (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ .index :: inner ++ .argSep :: outer ++ suffix).flatMap
          G1Frame.bits)) .aSeekOut .p3 false false false ctx)
      (4 * (inner.length + outer.length + 1) + 4) :=
  g1ASeek_acrossBoundary_runSafe pre .index inner outer suffix ctx houter hinner
    trivial hword

/-! ## Exactly one successful A round -/

/-- The A forward return crosses its homogeneous skip run and the unique cursor
in exactly four steps per frame. -/
theorem g1CS_aWalk_fwd_to_cursor_runSafe {W : Nat}
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hroom : 4 * (pre.length + skipped.length + 1) < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * pre.length) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aFwd .p0 false false false ctx) (4 * (skipped.length + 1)) := by
  have hfix : ∀ f ∈ skipped, g1Advance .aFwd f = .aFwd :=
    fun f hf => g1Advance_aFwd_of_skip (hskip f hf)
  have hpath : G1ValidPath .aFwd (skipped ++ [.cursor]) :=
    g1ValidPath_fix (mode := .aFwd) trivial [.cursor]
      ⟨trivial, by decide, trivial⟩ skipped hfix
  have hlist : pre ++ (skipped ++ [.cursor]) ++ suffix =
      pre ++ skipped ++ .cursor :: suffix := by simp [List.append_assoc]
  have hs := g1Forward_scanFrom_runSafe pre (skipped ++ [.cursor]) suffix
    .aFwd ctx hpath (by simpa using hroom)
  rw [hlist] at hs
  simpa using hs

set_option maxHeartbeats 1000000 in
/-- One successful A round is safe for precisely the schedule and premises of
`g1CS_aWalk_round_exact`: `16*j + 8*arg2 + 45` steps from `SigmaA(j)`. -/
theorem g1CS_aWalk_round_runSafe (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    G1RunSafe
      (g1AWalkConfig r b j (by omega) (by omega) v hv)
      (g1AWalkRoundSteps r j) := by
  let markPre := g1TagRouteFrames r ++
    List.replicate (r.arg1 - j - 1) G1Frame.index
  let inner := g1AWalkInnerRun j
  let outer := g1AWalkOuterRun r j
  let tail := G1Frame.cursor :: g1AWalkTail r j
  have hj : j < r.vals.length := by omega
  have hsafe := g1AWalkCursor_safe r j hj
  have hmarkLen : markPre.length = r.tag.units + 2 + (r.arg1 - j - 1) := by
    simp [markPre]
  have hinnerLen : inner.length = j := by
    simpa [inner] using g1AWalkInnerRun_length j
  have houterLen : outer.length = r.arg2 + j + 1 := by
    simpa [outer] using g1AWalkOuterRun_length r j (by omega)
  have hseekRoom : 4 * (markPre.length +
      (inner.length + outer.length + 1)) + 8 <
      gnLocalSpan (encodeG1 r).length := by
    rw [hmarkLen, hinnerLen, houterLen]
    simp [gnLocalSpan, encodeG1_length]
    omega
  have hseek0 := g1CS_aWalk_seek_index_runSafe
    (W := (encodeG1 r).length) markPre inner outer tail (g1AWalkCtx r b v)
    (by simpa [outer] using g1AWalkOuterRun_skip r j)
    (by simpa [inner] using g1AWalkInnerRun_skip j) hseekRoom
  have hseek : G1RunSafe
      (g1AWalkConfig r b j (by omega) hj v hv) (g1AWalkSeekSteps r j) := by
    rw [show markPre ++ .index :: inner ++ .argSep :: outer ++ tail =
      g1AWalkFrames r j by
        simpa [markPre, inner, outer, tail] using g1AWalkSplit_seek r j hj1]
      at hseek0
    simpa only [g1AWalkConfig, hmarkLen, hinnerLen, houterLen,
      g1AWalkSeekSteps, g1AWalkCursor,
      show 4 * (r.tag.units + 2 + (r.arg1 - j - 1) +
          (j + (r.arg2 + j + 1) + 1)) + 3 =
        4 * (r.tag.units + r.arg1 + r.arg2 + j + 4) - 1 by omega,
      show 4 * (j + (r.arg2 + j + 1) + 1) + 4 =
        8 * j + 4 * r.arg2 + 12 by omega] using hseek0
  have hseekExact : TM.runConfig (M := G1M)
      (g1AWalkConfig r b j (by omega) hj v hv) (g1AWalkSeekSteps r j) =
    g1AlignedConfig (encodeG1 r).length (4 * markPre.length) (by
      exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength _))
      (g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits))
      .aDec .p0 false false false (g1AWalkCtx r b v) := by
    have h := g1CS_aWalk_seek_index (encodeG1 r).length markPre inner outer tail
      (g1AWalkCtx r b v)
      (by simpa [outer] using g1AWalkOuterRun_skip r j)
      (by simpa [inner] using g1AWalkInnerRun_skip j)
      (lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength _))
    rw [show markPre ++ .index :: inner ++ .argSep :: outer ++ tail =
      g1AWalkFrames r j by
        simpa [markPre, inner, outer, tail] using g1AWalkSplit_seek r j hj1]
      at h
    simpa only [g1AWalkConfig, hmarkLen, hinnerLen, houterLen,
      g1AWalkSeekSteps, g1AWalkCursor,
      show 4 * (r.tag.units + 2 + (r.arg1 - j - 1) +
          (j + (r.arg2 + j + 1) + 1)) + 3 =
        4 * (r.tag.units + r.arg1 + r.arg2 + j + 4) - 1 by omega,
      show 4 * (j + (r.arg2 + j + 1) + 1) + 4 =
        8 * j + 4 * r.arg2 + 12 by omega]
      using h
  have hmark0 : G1RunSafe
      (g1AlignedConfig (encodeG1 r).length (4 * markPre.length) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength _))
        (g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits))
        .aDec .p0 false false false (g1AWalkCtx r b v)) 4 := by
    apply g1RunSafe_of_margins
    · simp only [g1AlignedConfig_head_val]
      rw [hmarkLen]
      omega
    · simp only [g1AlignedConfig_head_val]
      rw [hmarkLen]
      simp [gnLocalSpan, encodeG1_length]
      omega
  have hmark : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) hj v hv) (g1AWalkSeekSteps r j)) 4 :=
    G1RunSafe.transport hseekExact.symm hmark0
  have hseekMark := G1RunSafe.add hseek hmark
  let fwdPre := markPre ++ [.spent]
  let fwdRun := g1AWalkFwdRun r j
  have hfwdPreLen : fwdPre.length = r.tag.units + 3 + (r.arg1 - j - 1) := by
    simpa [fwdPre, markPre] using g1AWalkFwdPre_length r j
  have hfwdRunLen : fwdRun.length = 2 * j + r.arg2 + 2 := by
    simpa [fwdRun] using g1AWalkFwdRun_length r j (by omega)
  have hmarkExact0 := g1CS_aWalk_mark (encodeG1 r).length markPre
    (inner ++ .argSep :: (outer ++ tail)) (g1AWalkCtx r b v)
    (lt_of_lt_of_le (by rw [hmarkLen]; omega)
      (gnLocalSpan_le_g1_tapeLength _))
  have hmarkExact : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * markPre.length) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength _))
        (g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits))
        .aDec .p0 false false false (g1AWalkCtx r b v)) 4 =
    g1AlignedConfig (encodeG1 r).length (4 * fwdPre.length) (by
      exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength _))
      (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
      .aFwd .p0 false false false (g1AWalkCtx r b v) := by
    rw [show markPre ++ .index :: (inner ++ .argSep :: (outer ++ tail)) =
        g1AWalkFrames r j by
          simpa [markPre, inner, outer, tail] using g1AWalkSplit_mark r j hj1,
      show markPre ++ .spent :: (inner ++ .argSep :: (outer ++ tail)) =
        g1AWalkFramesMarked r j by
          simpa [markPre, inner, outer, tail] using g1AWalkSplit_marked r j]
      at hmarkExact0
    simpa only [show fwdPre.length = markPre.length + 1 by simp [fwdPre]] using
      hmarkExact0
  have hseekMarkExact : TM.runConfig (M := G1M)
      (g1AWalkConfig r b j (by omega) hj v hv) (g1AWalkSeekSteps r j + 4) =
    g1AlignedConfig (encodeG1 r).length (4 * fwdPre.length) (by
      exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength _))
      (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
      .aFwd .p0 false false false (g1AWalkCtx r b v) := by
    rw [runConfig_add, hseekExact, hmarkExact]
  have hfwdRoom : 4 * (fwdPre.length + fwdRun.length + 1) <
      gnLocalSpan (encodeG1 r).length := by
    rw [hfwdPreLen, hfwdRunLen]
    simp [gnLocalSpan, encodeG1_length]
    omega
  have hfwd0 := g1CS_aWalk_fwd_to_cursor_runSafe
    (W := (encodeG1 r).length) fwdPre fwdRun (g1AWalkTail r j)
    (g1AWalkCtx r b v)
    (by simpa [fwdRun] using g1AWalkFwdRun_skip r j) hfwdRoom
  rw [show fwdPre ++ fwdRun ++ .cursor :: g1AWalkTail r j =
      g1AWalkFramesMarked r j by
        simpa [fwdPre, fwdRun, markPre] using g1AWalkSplit_marked_fwd r j]
    at hfwd0
  have hfwd : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) hj v hv)
        (g1AWalkSeekSteps r j + 4)) (8 * j + 4 * r.arg2 + 12) := by
    apply G1RunSafe.transport hseekMarkExact.symm
    simpa only [hfwdRunLen,
      show 4 * (2 * j + r.arg2 + 2 + 1) =
        8 * j + 4 * r.arg2 + 12 by omega] using hfwd0
  have hthroughFwd := G1RunSafe.add hseekMark hfwd
  have hfwdExact0 := g1CS_aWalk_fwd_to_cursor (encodeG1 r).length fwdPre fwdRun
    (g1AWalkTail r j) (g1AWalkCtx r b v)
    (by simpa [fwdRun] using g1AWalkFwdRun_skip r j)
    (lt_of_lt_of_le hfwdRoom (gnLocalSpan_le_g1_tapeLength _))
  rw [show fwdPre ++ fwdRun ++ .cursor :: g1AWalkTail r j =
      g1AWalkFramesMarked r j by
        simpa [fwdPre, fwdRun, markPre] using g1AWalkSplit_marked_fwd r j]
    at hfwdExact0
  have hbeforeTurnExact : TM.runConfig (M := G1M)
      (g1AWalkConfig r b j (by omega) hj v hv)
      (16 * j + 8 * r.arg2 + 28) =
    g1AlignedConfig (encodeG1 r).length (4 * (g1AWalkCursor r j + 1)) (by
      omega)
      (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
      .aTurn .p0 false false false (g1AWalkCtx r b v) := by
    rw [show 16 * j + 8 * r.arg2 + 28 =
        (g1AWalkSeekSteps r j + 4) + (8 * j + 4 * r.arg2 + 12) by
          simp [g1AWalkSeekSteps]
          omega,
      runConfig_add, hseekMarkExact]
    simpa only [hfwdRunLen, hfwdPreLen, g1AWalkCursor,
      show 4 * (2 * j + r.arg2 + 2 + 1) =
        8 * j + 4 * r.arg2 + 12 by omega,
      show r.tag.units + 3 + (r.arg1 - j - 1) +
          (2 * j + r.arg2 + 2 + 1) =
        r.tag.units + r.arg1 + r.arg2 + j + 4 + 1 by omega]
      using hfwdExact0
  have hturnRestore : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) hj v hv)
        (16 * j + 8 * r.arg2 + 28)) 8 := by
    rw [hbeforeTurnExact]
    apply g1RunSafe_of_margins
    · simp [g1AWalkCursor]
      omega
    · simp [g1AWalkCursor, gnLocalSpan, encodeG1_length]
      omega
  have hthroughFwd' : G1RunSafe
      (g1AWalkConfig r b j (by omega) hj v hv)
      (16 * j + 8 * r.arg2 + 28) := by
    simpa only [show g1AWalkSeekSteps r j + 4 +
      (8 * j + 4 * r.arg2 + 12) = 16 * j + 8 * r.arg2 + 28 by
        simp [g1AWalkSeekSteps]
        omega] using hthroughFwd
  have hprefix0 := G1RunSafe.add hthroughFwd' hturnRestore
  have hprefix : G1RunSafe
      (g1AWalkConfig r b j (by omega) hj v hv)
      (g1AWalkRoundPrefixSteps r j) := by
    simpa [g1AWalkSeekSteps, g1AWalkRoundPrefixSteps] using hprefix0
  have hprefixExact := g1CS_aWalk_round_prefix_exact r b j hj1 hj v hv
  have hprobe : G1RunSafe
      (TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) hj v hv)
        (g1AWalkRoundPrefixSteps r j)) 5 := by
    rw [hprefixExact]
    apply g1RunSafe_of_margins
    · simp [g1AWalkCursor]
      omega
    · simp [g1AWalkCursor, gnLocalSpan, encodeG1_length]
      omega
  have hdv' : r.vals[j + 1] = v' := g1AGetn hv' hnext
  have hprobeLen := g1AWalkProbePre_length r j hj1 (by omega)
  have hprobeExact0 := g1CS_aProbe_latch (encodeG1 r).length
    (g1AWalkProbePre r j)
    ((r.vals.drop (j + 2)).map G1Frame.data ++
      [.output false, .finish, .blank]) v' (g1AWalkCtx r b v)
    (by rw [hprobeLen]; omega)
  rw [g1AWalkSplit_restored_probe r j v' hnext hdv'] at hprobeExact0
  have hprobeExact : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1)) (by
          omega)
        (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
        .aProbe .p0 false false false (g1AWalkCtx r b v)) 5 =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1AWalkCursor r j + 1) + 3) (by
        omega)
      (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
      .aIns .p3 false false false (g1AWalkCtx r b v') := by
    simpa only [hprobeLen, g1AWalkCtx_withVB] using hprobeExact0
  have hinstall0 : G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1) + 3) (by
          omega)
        (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
        .aIns .p3 false false false (g1AWalkCtx r b v')) 4 := by
    apply g1RunSafe_of_margins
    · simp [g1AWalkCursor]
      omega
    · simp [g1AWalkCursor, gnLocalSpan, encodeG1_length]
      omega
  have hinstall : G1RunSafe
      (TM.runConfig (M := G1M)
        (TM.runConfig (M := G1M)
          (g1AWalkConfig r b j (by omega) hj v hv)
          (g1AWalkRoundPrefixSteps r j)) 5) 4 := by
    rw [hprefixExact, hprobeExact]
    exact hinstall0
  have htailSafe := G1RunSafe.add hprobe hinstall
  have hall := G1RunSafe.add hprefix htailSafe
  simpa [g1AWalkRoundSteps, g1AWalkRoundPrefixSteps] using hall

/-- Safety paired with the already-established exact `SigmaA(j+1)` endpoint. -/
theorem g1CS_aWalk_round_trace_safe (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    G1RunSafe
        (g1AWalkConfig r b j (by omega) (by omega) v hv)
        (g1AWalkRoundSteps r j) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b j (by omega) (by omega) v hv)
          (g1AWalkRoundSteps r j) =
        g1AWalkConfig r b (j + 1) (by omega) hnext v' hv' :=
  ⟨g1CS_aWalk_round_runSafe r b j hj1 hnext v v' hv hv',
    g1CS_aWalk_round_exact r b j hj1 hnext v v' hv hv'⟩

/-! ## Binary real-initial and literal capstones -/

/-- The merged e1a binary `SigmaA(0)` safety composes with one successful A
round and reaches the exact `SigmaA(1)` endpoint, with no later driver step. -/
theorem g1CS_readA_binary_one_round_from_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bA' bB : Bool) (rest : List Bool) (harg : 0 < r.arg1)
    (hB : r.vals[r.arg2]? = some bB) (hv : r.vals = bA :: rest)
    (hv' : r.vals[1]? = some bA') :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r + g1AWalkRoundSteps r 0) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryCursorSteps r + g1AWalkRoundSteps r 0) =
        g1AWalkConfig r bB 1 (by omega) (g1ALength_pos_of_get hv') bA' hv' := by
  have hinstall := g1CS_readA_binary_install_from_initial_trace_safe r hc ht
    bA bB rest hB hv
  have hv0 : r.vals[0]? = some bA := by rw [hv]; simp
  have hround0 := g1CS_aWalk_round_trace_safe r bB 0 harg
    (g1ALength_pos_of_get hv') bA bA' hv0 hv'
  have hround : G1RunSafe
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r)) (g1AWalkRoundSteps r 0) :=
    G1RunSafe.transport hinstall.2.2.symm hround0.1
  exact ⟨G1RunSafe.add hinstall.1 hround, by
    rw [runConfig_add, hinstall.2.2, hround0.2]⟩

namespace G1PassATraceProbes

/-- The requested literal has the exact local A-round cost `53`. -/
theorem literal_round_trace_safe :
    G1RunSafe
        (g1AWalkConfig reqA true 0 (by decide) (by decide) true (by decide)) 53 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig reqA true 0 (by decide) (by decide) true (by decide)) 53 =
        g1AWalkConfig reqA true 1 (by decide) (by decide) true (by decide) := by
  simpa [reqA, g1AWalkRoundSteps] using
    g1CS_aWalk_round_trace_safe reqA true 0 (by decide) (by decide)
      true true (by decide) (by decide)

/-- The requested real-initial binary execution is safe for exactly `423`
steps and stops at the exact `SigmaA(1)` endpoint (`370 + 53`). -/
theorem literal_one_round_from_initial_trace_safe :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqA))) 423 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqA))) 423 =
        g1AWalkConfig reqA true 1 (by decide) (by decide) true (by decide) := by
  have h := g1CS_readA_binary_one_round_from_initial_trace_safe reqA (by decide)
    (Or.inl rfl) true true true [true, false] (by decide) (by decide) rfl
    (by decide)
  simpa [reqA, g1ABinaryCursorSteps, g1BActivatedSteps, g1BPassASteps,
    g1BReadSteps, g1InstallScanSteps, g1RepairSteps, g1ReadBHandoffSteps,
    g1ALiveInstallSteps, g1AWalkRoundSteps, G1Tag.units] using h

end G1PassATraceProbes

end Pnp3.Internal.PsubsetPpoly.TM
