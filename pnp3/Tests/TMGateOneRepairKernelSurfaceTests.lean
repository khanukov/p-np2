import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernel

/-!
# G1 operand-2 repair kernel: surface tests

Theorem-style exact wrappers for the Repair-1 surface: the two generic kernel
instances (`g1RepairScanner`, `g1RepairCycle`), the reverse repair table with all
**four** of its outcomes and its three stop states, the seven
arbitrary-frame-list macros (the thirteen-step cycle, seek-and-repair, the
single frame skip, the four-step rejection of a frame the scan may not cross
and its sink-stable form, the multi-frame skip and the `13 * s` run), the
terminal
dispatch and the anchor finish, the closed cost `g1RepairPassSteps` and the
capstone `g1CS_repair_pass_exact`, which is the concrete endpoint of the slice.

**The sweep does not cross corrupted tape.**  `check_g1RepairRevAdvance` pins
`G1RepairSkip` in both directions — every canonical interior frame kind is
crossable, and `spent`, `bof`, `blank` and `cursor` are not —
`check_g1RepairRevComplete` pins that the three reserved codes reject at the bit
level, and `check_g1CS_repair_frame_reject` runs the
rejection as four genuine `G1M` steps into the stable `reject` sink.  The skip
hypotheses of the macros are therefore real constraints on the caller's frame
list, not decoration.

Three further facts the wrappers pin deliberately.  **Nothing routes into the
sweep**:
`check_repair_unreachable` pins that no `g1Advance` row produces a repair mode
and that all five are stuck, and `check_repair_endpoint_idle` pins that the
sweep's endpoint `readAStart` is the same idle handoff it always was.  **Every
run is caller-supplied**: every wrapper below takes the caller's `n`, safety
bound, frame list and `G1Ctx`, and none mentions `G1M.initialConfig`.  And the
pass endpoint is **exact**: the tape changes in exactly the `s` repaired frames
and the carried context comes out untouched.

**Absent from this surface**: the all-literal probes of the kernel, which live
with their module in **Repair-1b** and are pinned by
`TMGateOneRepairKernelExamplesSurfaceTests`; the request-specific repair driver;
any
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

/-- The skip predicate, the reverse table and its **three** stop targets: a
`spent` unit is the write handoff, the `bof` anchor the terminal handoff, a
crossable interior frame continues the scan, and a `blank` or a leftover
`cursor` — neither of which is crossable — rejects.  The predicate is pinned
both ways: every canonical interior frame kind is crossable, and the four frames
that end the pass are not. -/
theorem check_g1RepairRevAdvance (m : G1Mode) (f : G1Frame) :
    g1RepairRevAdvance m .spent = .bRepairWrite ∧
      g1RepairRevAdvance m .bof = .bRepairDone ∧
      g1RepairRevAdvance m .blank = .reject ∧
      g1RepairRevAdvance m .cursor = .reject ∧
      (G1RepairSkip f → g1RepairRevAdvance m f = .bRepairSeek) ∧
      (G1RepairSkip .tag ∧ G1RepairSkip .index ∧ G1RepairSkip .separator ∧
        (∀ v, G1RepairSkip (.data v)) ∧ (∀ v, G1RepairSkip (.output v)) ∧
        G1RepairSkip .finish ∧ G1RepairSkip .argSep) ∧
      ¬ G1RepairSkip G1Frame.spent ∧ ¬ G1RepairSkip G1Frame.bof ∧
      ¬ G1RepairSkip G1Frame.blank ∧ ¬ G1RepairSkip G1Frame.cursor :=
  ⟨rfl, rfl, rfl, rfl, fun h => g1RepairRevAdvance_of_skip (m := m) h,
    ⟨trivial, trivial, trivial, fun _ => trivial, fun _ => trivial, trivial,
      trivial⟩,
    id, id, id, id⟩

/-- The bit-level reverse table agrees with the frame table on every decodable
window and **rejects** every window that decodes to nothing — in particular the
three reserved codes, which have no `G1Frame` and therefore no frame-level
run. -/
theorem check_g1RepairRevComplete (m : G1Mode) (b0 b1 b2 b3 : Bool)
    (f : G1Frame) :
    (decodeG1Frame? [b0, b1, b2, b3] = some f →
        g1RepairRevComplete m b0 b1 b2 b3 = g1RepairRevAdvance m f) ∧
      (decodeG1Frame? [b0, b1, b2, b3] = none →
        g1RepairRevComplete m b0 b1 b2 b3 = .reject) ∧
      (g1RepairRevComplete m true true false true = .reject ∧
        g1RepairRevComplete m true true true false = .reject ∧
        g1RepairRevComplete m true true true true = .reject) ∧
      (g1RepairRevComplete m false false false false = .reject ∧
        g1RepairRevComplete m false true true true = .reject) :=
  ⟨fun h => g1RepairBackComplete_some h, fun h => g1RepairBackComplete_none h,
    g1RepairBackComplete_reserved, g1RepairBackComplete_forbidden⟩

/-- The reverse mode of the sweep is exactly `bRepairSeek`, and the stop
predicate is exactly the two handoffs plus the `reject` sink. -/
theorem check_G1RepairMode (m : G1Mode) :
    (G1RepairMode m → m = .bRepairSeek) ∧
      (G1RepairStop m ↔
        (m = .bRepairWrite ∨ m = .bRepairDone ∨ m = .reject)) ∧
      ¬ G1RepairStop .bRepairSeek :=
  ⟨fun h => G1RepairMode.eq h, Iff.rfl, by simp [G1RepairStop]⟩

/-- The scan's three stop states, pinned exactly: the write handoff and the
terminal handoff carry the caller's `G1Ctx` through, and the sink is literally
`g1RejectState`, which drops it. -/
theorem check_g1RepairStopState (ctx : G1Ctx) :
    g1RepairStopState .bRepairWrite ctx = g1RepairWriteState ctx ∧
      g1RepairStopState .bRepairDone ctx = g1RepairDoneState ctx ∧
      g1RepairStopState .reject ctx = g1RejectState ∧
      g1RejectState = g1State .reject .p0 false false false g1Ctx0 :=
  ⟨g1RepairStopState_write ctx, g1RepairStopState_done ctx,
    g1RepairStopState_reject ctx, rfl⟩

/-- The scanner is a genuine `ReverseFrameScanner` of the **fixed** program
`g1CS` at the G1 codec, and its compiled machine is literally `G1M`. -/
theorem check_g1RepairScanner :
    g1RepairScanner.program = g1CS ∧
      g1RepairScanner.codec = g1FrameCodec ∧
      g1RepairScanner.machine = G1M ∧
      g1RepairScanner.Reverse = G1RepairMode ∧
      g1RepairScanner.Stop = G1RepairStop ∧
      g1RepairScanner.revAdvance = g1RepairRevAdvance ∧
      g1RepairScanner.revComplete = g1RepairRevComplete ∧
      g1RepairScanner.stopState = g1RepairStopState :=
  ⟨rfl, rfl, g1RepairScanner_machine, rfl, rfl, rfl, rfl, rfl⟩

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

/-- **One frame the scan may not cross**, four steps, into the `reject` sink at
the frame's first cell: the tape is untouched, the carried context is dropped,
and the sweep does not continue left — so no `spent` unit behind a `blank` or a
leftover `cursor` is ever rewritten. -/
theorem check_g1CS_repair_frame_reject (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : f = .blank ∨ f = .cursor)
    (hbits : physicalBitsAt hsafe tape = f.bits) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .bRepairSeek .p3
          false false false ctx) 4 =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 :=
  g1CS_repair_frame_reject n base hsafe tape ctx f hf hbits

/-- The rejection is **final**: the sink holds for the whole remaining budget. -/
theorem check_g1CS_repair_frame_reject_idle (n base : Nat)
    (hsafe : base + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (f : G1Frame)
    (hf : f = .blank ∨ f = .cursor)
    (hbits : physicalBitsAt hsafe tape = f.bits) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (base + 3) (by omega) tape .bRepairSeek .p3
          false false false ctx) (4 + k) =
      g1AlignedConfig n base (by omega) tape .reject .p0 false false false
        g1Ctx0 :=
  g1CS_repair_frame_reject_idle n base hsafe tape ctx f hf hbits k

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

end Pnp3.Tests.TMGateOneRepairKernelSurface
