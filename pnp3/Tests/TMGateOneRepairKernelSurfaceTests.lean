import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernelExamples

/-!
# G1 operand-2 repair kernel: surface tests

Theorem-style exact wrappers for the Repair-1 surface: the two generic kernel
instances (`g1RepairScanner`, `g1RepairCycle`), the reverse repair table, the
five arbitrary-frame-list macros (the thirteen-step cycle, seek-and-repair, the
single frame skip, the multi-frame skip and the `13 * s` run), the terminal
dispatch and the anchor finish, the closed cost `g1RepairPassSteps` and the
capstone `g1CS_repair_pass_exact`, plus the three all-literal probes.

Three facts the wrappers pin deliberately.  **Nothing routes into the sweep**:
`check_repair_unreachable` pins that no `g1Advance` row produces a repair mode
and that all five are stuck, and `check_repair_endpoint_idle` pins that the
sweep's endpoint `readAStart` is the same idle handoff it always was.  **Every
run is caller-supplied**: every wrapper below takes the caller's `n`, safety
bound, frame list and `G1Ctx`, and none mentions `G1M.initialConfig`.  And the
pass endpoint is **exact**: the tape changes in exactly the `s` repaired frames
and the carried context comes out untouched.

**Absent from this surface**: the request-specific repair driver, any
composition of a read with a repair, any pass-A read, combine step, output
write, and any `TM.accepts`, verdict, full-clock, gate-semantics,
acceptance-gate, multi-gate, specification-bridge or padded-tape surface.  It
pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneRepairKernelSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- No mode/frame pair completes into a repair mode, and all five repair modes
are stuck at the frame table. -/
theorem check_repair_unreachable (mode : G1Mode) (frame : G1Frame) :
    (g1Advance mode frame ≠ .bRepairSeek ∧
        g1Advance mode frame ≠ .bRepairWrite ∧
        g1Advance mode frame ≠ .bRepairBack ∧
        g1Advance mode frame ≠ .bRepairHop ∧
        g1Advance mode frame ≠ .bRepairDone) ∧
      (G1Stuck .bRepairSeek ∧ G1Stuck .bRepairWrite ∧ G1Stuck .bRepairBack ∧
        G1Stuck .bRepairHop ∧ G1Stuck .bRepairDone) :=
  ⟨g1_repair_unreachable_forward mode frame, g1_repair_modes_stuck⟩

/-- The sweep's endpoint is the **existing** idle `readAStart`: it holds its
state, head and tape for the whole remaining budget, so nothing continues from
the repaired configuration in this slice. -/
theorem check_repair_endpoint_idle (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .readAStart .p0 false false false ctx) k =
      g1AlignedConfig n h hh tape .readAStart .p0 false false false ctx :=
  g1CS_runConfig_readA_idle n h hh tape ctx k

/-- The skip predicate, the reverse table and its two stop targets: a `spent`
unit is the write handoff, the `bof` anchor the terminal handoff, everything
else continues the scan. -/
theorem check_g1RepairRevAdvance (m : G1Mode) (f : G1Frame) :
    g1RepairRevAdvance m .spent = .bRepairWrite ∧
      g1RepairRevAdvance m .bof = .bRepairDone ∧
      (G1RepairSkip f → g1RepairRevAdvance m f = .bRepairSeek) ∧
      ¬ G1RepairSkip G1Frame.spent ∧ ¬ G1RepairSkip G1Frame.bof :=
  ⟨rfl, rfl, fun h => g1RepairRevAdvance_of_skip h, id, id⟩

/-- The reverse mode of the sweep is exactly `bRepairSeek`, and the stop
predicate is exactly the two handoffs. -/
theorem check_G1RepairMode (m : G1Mode) :
    (G1RepairMode m → m = .bRepairSeek) ∧
      (G1RepairStop m ↔ (m = .bRepairWrite ∨ m = .bRepairDone)) :=
  ⟨fun h => G1RepairMode.eq h, Iff.rfl⟩

/-- The scanner is a genuine `ReverseFrameScanner` of the **fixed** program
`g1CS` at the G1 codec, and its compiled machine is literally `G1M`. -/
theorem check_g1RepairScanner :
    g1RepairScanner.program = g1CS ∧
      g1RepairScanner.codec = g1FrameCodec ∧
      g1RepairScanner.machine = G1M ∧
      g1RepairScanner.Reverse = G1RepairMode ∧
      g1RepairScanner.Stop = G1RepairStop ∧
      g1RepairScanner.revAdvance = g1RepairRevAdvance ∧
      g1RepairScanner.revComplete = g1RepairRevComplete :=
  ⟨rfl, rfl, g1RepairScanner_machine, rfl, rfl, rfl, rfl⟩

/-- The cycle is a genuine `FrameRewriteCycle` over that scanner, in the
direction `spent ↦ index`, whose four written cells are literally
`G1Frame.index.bits`. -/
theorem check_g1RepairCycle :
    g1RepairCycle.scanner = g1RepairScanner ∧
      g1RepairCycle.marker = G1Frame.spent ∧
      g1RepairCycle.target = G1Frame.index ∧
      g1RepairCycle.seekMode = G1Mode.bRepairSeek ∧
      g1RepairCycle.stopMode = G1Mode.bRepairWrite ∧
      [g1RepairCycle.w0, g1RepairCycle.w1, g1RepairCycle.w2,
        g1RepairCycle.w3] = G1Frame.index.bits :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The thirteen-step `spent ↦ index` cycle.** -/
theorem check_g1CS_repair_cycle_onList (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx) 13 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx :=
  g1CS_repair_cycle_onList n pre suffix ctx hpre hsafe

/-- **Seek, then repair**, in `4 * skipped.length + 13` steps. -/
theorem check_g1CS_repair_seek_and_repair (n : Nat)
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape ((pre ++ G1Frame.spent :: skipped ++ suffix).flatMap
            G1Frame.bits))
          .bRepairSeek .p3 false false false ctx)
        (4 * skipped.length + 13) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap
          G1Frame.bits))
        .bRepairSeek .p3 false false false ctx :=
  g1CS_repair_seek_and_repair n pre skipped suffix ctx hpre hskip hsafe

/-- **One skipped frame**, four steps, tape and context untouched. -/
theorem check_g1CS_repair_frame_skip (n base : Nat) (hpos : 0 < base)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : G1RepairSkip f) (hbits : physicalBitsAt hsafe tape = f.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .bRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n (base - 1) (by omega) tape .bRepairSeek .p3
        false false false ctx :=
  g1CS_repair_frame_skip n base hpos hsafe tape ctx f hf hbits

/-- **A whole skipped run**, four steps per frame, tape and context
untouched. -/
theorem check_g1CS_repair_scan_skip (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hskip : ∀ f ∈ skipped, G1RepairSkip f)
    (hsafe : 4 * (pre.length + skipped.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) - 1) (by omega)
          (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx)
        (4 * skipped.length) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ skipped ++ suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx :=
  g1CS_repair_scan_skip n pre skipped suffix ctx hpre hskip hsafe

/-- **The repair induction**: `s` consumed units become `s` `index` frames in
exactly `13 * s` steps, and nothing else on the tape moves. -/
theorem check_g1CS_repair_spent_run (n : Nat) (pre suffix : List G1Frame)
    (s : Nat) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * (pre.length + s) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + s) - 1) (by omega)
          (g1ListTape ((pre ++ List.replicate s G1Frame.spent ++
            suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx) (13 * s) =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ List.replicate s G1Frame.index ++
          suffix).flatMap G1Frame.bits))
        .bRepairSeek .p3 false false false ctx :=
  g1CS_repair_spent_run n pre suffix s ctx hpre hsafe

/-- **The terminal dispatch, executed**: one stationary step into
`readAStart`. -/
theorem check_g1CS_step_repairDone (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .bRepairDone .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .readAStart .p0 false false false ctx :=
  g1CS_step_repairDone n h hh tape ctx

/-- **The end of the sweep**: the anchor read stays on cell zero and the
dispatch follows, five steps in all, tape and context unchanged. -/
theorem check_g1CS_repair_finish (n : Nat) (suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 3 (by omega)
          (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false ctx) 5 =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape ((G1Frame.bof :: suffix).flatMap G1Frame.bits))
        .readAStart .p0 false false false ctx :=
  g1CS_repair_finish n suffix ctx hsafe

/-- The closed cost `4m + 13s + 4a + 5`, T1's `t1RepairSteps`. -/
theorem check_g1RepairPassSteps (a s m : Nat) :
    g1RepairPassSteps a s m = 4 * m + 13 * s + 4 * a + 5 := rfl

/-- **The capstone.**  On the caller's frame list, exactly
`g1RepairPassSteps left.length s mid.length` genuine steps rewrite every
designated `spent` frame to `index`, preserve `left`, `mid` and `tail`
bit-for-bit, preserve the whole carried `G1Ctx`, and stop at head `0` in
`readAStart` through `bRepairDone`. -/
theorem check_g1CS_repair_pass_exact (n s : Nat) (left mid tail : List G1Frame)
    (ctx : G1Ctx) (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hmid : ∀ f ∈ mid, G1RepairSkip f)
    (hsafe : 4 * (1 + left.length + s + mid.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (1 + left.length + s + mid.length) - 1)
          (by omega)
          (g1ListTape (([G1Frame.bof] ++ left ++
            List.replicate s G1Frame.spent ++ mid ++ tail).flatMap
            G1Frame.bits))
          .bRepairSeek .p3 false false false ctx)
        (g1RepairPassSteps left.length s mid.length) =
      g1AlignedConfig n 0 (by omega)
        (g1ListTape (([G1Frame.bof] ++ left ++
          List.replicate s G1Frame.index ++ mid ++ tail).flatMap G1Frame.bits))
        .readAStart .p0 false false false ctx :=
  g1CS_repair_pass_exact n s left mid tail ctx hleft hmid hsafe

open G1RepairKernelExamples

/-- The literal word, its split and its nonvacuity: the repaired word is
literally `encodeG1Frames ⟨and, 0, 2, [false, true, true]⟩ ++ [blank]`, the
three words are pairwise different, the consumed units go `2 ↦ 1 ↦ 0`, and
physical cell `32` genuinely flips. -/
theorem check_probe_words :
    probeIndexFrames = encodeG1Frames G1InstallScanExamples.g1WalkExample ++
        [G1Frame.blank] ∧
      probeSpentFrames ≠ probeIndexFrames ∧
      probeSpentFrames.count G1Frame.spent = 2 ∧
      probeHalfFrames.count G1Frame.spent = 1 ∧
      probeIndexFrames.count G1Frame.spent = 0 ∧
      probeIndexFrames.count G1Frame.index = 2 ∧
      g1ListTape (n := probeLen) (probeSpentFrames.flatMap G1Frame.bits)
          ⟨32, probe_safe (by omega)⟩ = true ∧
      g1ListTape (n := probeLen) (probeIndexFrames.flatMap G1Frame.bits)
          ⟨32, probe_safe (by omega)⟩ = false :=
  ⟨probeIndex_eq_encoded, probe_words_distinct.2.2, probe_counts.1,
    probe_counts.2.1, probe_counts.2.2.1, probe_counts.2.2.2.2.1,
    probe_cell32.1, probe_cell32.2⟩

/-- **`13` genuine steps repair the rightmost consumed unit**, head `35 ↦ 31`,
context preserved. -/
theorem check_cycle_probe :
    TM.runConfig (M := G1M)
          (g1AlignedConfig probeLen 35 (probe_safe (by omega))
            (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
            .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 13 =
        g1AlignedConfig probeLen 31 (probe_safe (by omega))
          (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (g1AlignedConfig probeLen 35 (probe_safe (by omega))
            (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
            .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
          13).state.snd.ctx = g1Ctx0.withVB true :=
  ⟨cycle_probe, cycle_probe_ctx⟩

/-- **`26 = 13 * 2` genuine steps repair the whole two-unit run**, head
`35 ↦ 27`, on the exact repaired word. -/
theorem check_run_probe :
    TM.runConfig (M := G1M)
          (g1AlignedConfig probeLen 59 (probe_safe (by omega))
            (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
            .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 37 =
        g1AlignedConfig probeLen 31 (probe_safe (by omega))
          (g1ListTape (probeHalfFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true) ∧
      TM.runConfig (M := G1M)
          (g1AlignedConfig probeLen 35 (probe_safe (by omega))
            (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
            .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 26 =
        g1AlignedConfig probeLen 27 (probe_safe (by omega))
          (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (g1AlignedConfig probeLen 35 (probe_safe (by omega))
            (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
            .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
          26).tape = g1ListTape (probeIndexFrames.flatMap G1Frame.bits) :=
  ⟨seek_repair_probe, run_probe, run_probe_tape⟩

/-- **`79 = 4 * 6 + 13 * 2 + 4 * 6 + 5` genuine steps run the whole pass**:
head `59 ↦ 0`, control `readAStart`, tape exactly the repaired word. -/
theorem check_pass_probe :
    g1RepairPassSteps 6 2 6 = 79 ∧
      TM.runConfig (M := G1M)
          (g1AlignedConfig probeLen 59 (probe_safe (by omega))
            (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
            .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) 79 =
        g1AlignedConfig probeLen 0 (probe_safe (by omega))
          (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
          .readAStart .p0 false false false (g1Ctx0.withVB true) :=
  ⟨probe_passSteps, pass_probe⟩

/-- The endpoint head is `0`. -/
theorem check_pass_probe_head :
    ((TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).head : Nat) = 0 := by
  rw [pass_probe]; rfl

/-- The endpoint tape is bit-for-bit the canonical encoded word of a real
request plus the trailing blank frame: no consumed unit survives. -/
theorem check_pass_probe_tape :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).tape =
      g1ListTape
        ((encodeG1Frames G1InstallScanExamples.g1WalkExample ++
          [G1Frame.blank]).flatMap G1Frame.bits) := by
  rw [pass_probe, ← probeIndex_eq_encoded]; rfl

/-- The carried context comes out untouched, latch included. -/
theorem check_pass_probe_ctx :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true))
        79).state.snd.ctx = g1Ctx0.withVB true := by
  rw [pass_probe]; rfl

/-- The endpoint is a **handoff**: it holds for the whole remaining budget, so
nothing in this slice continues from the repaired configuration. -/
theorem check_pass_probe_idle (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig probeLen 59 (probe_safe (by omega))
          (g1ListTape (probeSpentFrames.flatMap G1Frame.bits))
          .bRepairSeek .p3 false false false (g1Ctx0.withVB true)) (79 + k) =
      g1AlignedConfig probeLen 0 (probe_safe (by omega))
        (g1ListTape (probeIndexFrames.flatMap G1Frame.bits))
        .readAStart .p0 false false false (g1Ctx0.withVB true) :=
  pass_probe_idle k

end Pnp3.Tests.TMGateOneRepairKernelSurface
