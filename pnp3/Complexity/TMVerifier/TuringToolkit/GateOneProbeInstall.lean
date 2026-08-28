import Complexity.TMVerifier.TuringToolkit.FrameScannerWriteLeft
import Complexity.TMVerifier.TuringToolkit.GateOneInstallScan

/-!
# G1 cursor walk: the probe, the latch and the cursor install

**Progress classification: Infrastructure.**

The immediate successor of the merged installation-scan endpoint `bProbe2`, and
nothing else.  `GateOneControl` supplies the three probe rows and the five tuple
lemmas of `bLatchFalse`/`bLatchTrue`/`bIns`; this module turns them into

* `g1CS_walk_probe_latch` — five steps read a data frame and store its bit in
  `G1Ctx.vB`, head on that frame's *last* cell;
* `g1CS_walk_probe_oob` — four steps read the `output` destination frame instead
  and enter the stable `bOOB` boundary;
* `g1CursorWriter`, one `ReverseFrameWriter` instance, and
  `g1CS_walk_install_cursor` — four leftward steps replace that frame by
  `cursor`, head on the last cell of its predecessor, control in the
  reverse-seek entry shape `bSeek .p3`.

Each is an exact `TM.runConfig` equality — steps, head, control state, carried
context and the complete list-backed tape all pinned — on an **arbitrary**
surrounding frame list, with the tape length and the safety bound supplied by
the caller.  The probe reuses the existing forward `g1FrameScanner`; only the
leftward writer needs a new kernel instance.

The installation scan is **not** restated: `G1InstallSkip`,
`g1Advance_bInsSeek_of_skip`, `g1ValidPath_fix`, `g1AdvanceList_fix`,
`g1CS_walk_install_scan` and the real-initial-configuration route
`g1CS_readB_install_scan_exact` come unchanged from `GateOneInstallScan`, and
nothing here composes with them.

**Explicit deferrals.**  The install exits at `bSeek .p3`, head on the last cell
of the frame preceding the cursor; the reverse seek itself, the `index ↦ spent`
writer, the forward scan back to the cursor, the two turns, the four restore
writers and the exhaustion path are `GateOneWalkKernel`, and nothing here
composes with them.  Every theorem below takes the caller's configuration; none
starts from `G1M.initialConfig`, so there is no installation driver here.  No
walk invariant, no iteration or loop clock, no out-of-range aggregation, no
addressing, no `TM.accepts`, no gate-semantics correctness, no full-clock
theorem and no padded-tape claim.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- **The leftward cursor writer.**  Four fixed cells of `cursor`, walking
*left* from the last cell of the data frame, into the reverse seek. -/
def g1CursorWriter : ReverseFrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := fun _ => .cursor
  w0 := fun _ => false
  w1 := fun _ => true
  w2 := fun _ => true
  w3 := fun _ => true
  lst3 := fun ctx => g1InsState ctx
  lst2 := fun ctx => g1State .bIns .p2 false false false ctx
  lst1 := fun ctx => g1State .bIns .p1 false false false ctx
  lst0 := fun ctx => g1State .bIns .p0 false false false ctx
  exitState := fun ctx => g1SeekState ctx
  target_bits := fun _ => rfl
  lstep_p3 := fun ctx scan =>
    g1Transition_bIns_p3 g1CS.startPhase false false false scan ctx
  lstep_p2 := fun ctx scan =>
    g1Transition_bIns_p2 g1CS.startPhase false false false scan ctx
  lstep_p1 := fun ctx scan =>
    g1Transition_bIns_p1 g1CS.startPhase false false false scan ctx
  lstep_p0 := fun ctx scan =>
    g1Transition_bIns_p0 g1CS.startPhase false false false scan ctx

@[simp] theorem g1CursorWriter_machine : g1CursorWriter.machine = G1M := rfl

/-- The probe's two successful rows, as one table fact. -/
theorem g1Advance_bProbe2_data (v : Bool) :
    g1Advance .bProbe2 (.data v) = g1LatchMode v := by cases v <;> rfl

/-! ## The atomic macros, on an **arbitrary** surrounding frame list -/

/-- **Probe and latch.**  Five read-only steps (four for the frame, one for the
dispatch) store the bit of the data frame at ordinal `pre.length` in
`G1Ctx.vB` and leave the head on that frame's *last* cell. -/
theorem g1CS_walk_probe_latch (n : Nat) (pre suffix : List G1Frame) (v : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx) 5 =
      g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .bIns .p3 false false false (ctx.withVB v) := by
  have hbits : physicalBitsAt (h := 4 * pre.length) hsafe
      (g1ListTape (n := n)
        ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits)) =
      (G1Frame.data v).bits :=
    physicalBitsAt_flatMap g1FrameCodec pre suffix (.data v) hsafe
  have hmacro : TM.runConfig (M := G1M)
      (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        (g1LatchMode v) .p0 false false false ctx := by
    have h := g1FrameScanner_frameMacrostep n (4 * pre.length) hsafe
      (g1ListTape (n := n)
        ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
      .bProbe2 (.data v) ctx trivial (by cases v <;> decide) hbits
    rw [g1Advance_bProbe2_data v] at h
    exact h
  have hlatch : TM.runConfig (M := G1M)
      (g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        (g1LatchMode v) .p0 false false false ctx) 1 =
      g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .bIns .p3 false false false (ctx.withVB v) := by
    rw [runConfig_one]
    have hstep := g1CS_aligned_step_left n (4 * pre.length + 4) hsafe
      (by omega)
      (g1ListTape (n := n)
        ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
      (g1State (g1LatchMode v) .p0 false false false ctx)
      (g1InsState (ctx.withVB v)) _
      (fun phase => g1Transition_bLatch phase v .p0 false false false _ ctx)
    rw [writeCell_self] at hstep
    simpa [show 4 * pre.length + 4 - 1 = 4 * pre.length + 3 from by omega]
      using hstep
  refine Eq.trans (runConfig_add _ 4 1) ?_
  exact Eq.trans (congrArg (fun c => TM.runConfig (M := G1M) c 1) hmacro) hlatch

/-- **The out-of-range probe.**  Four steps read the `output` destination frame
instead of a data frame and enter the stable `bOOB` boundary. -/
theorem g1CS_walk_probe_oob (n : Nat) (pre suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .bOOB .p0 false false false ctx := by
  have hbits : physicalBitsAt (h := 4 * pre.length) hsafe
      (g1ListTape (n := n)
        ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits)) =
      (G1Frame.output false).bits :=
    physicalBitsAt_flatMap g1FrameCodec pre suffix (.output false) hsafe
  exact g1FrameScanner_frameMacrostep n (4 * pre.length) hsafe
    (g1ListTape (n := n)
      ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
    .bProbe2 (.output false) ctx trivial (by decide) hbits

/-- **The cursor install.**  Four leftward steps replace the frame at ordinal
`pre.length` by `cursor`, head on the last cell of its predecessor, control in
the reverse-seek entry shape `bSeek .p3`. -/
theorem g1CS_walk_install_cursor (n : Nat) (pre suffix : List G1Frame)
    (old : G1Frame) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ old :: suffix).flatMap G1Frame.bits))
        .bIns .p3 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .bSeek .p3 false false false ctx :=
  g1CursorWriter.writeFrameOnListLeft n pre suffix old ctx hpre hsafe

end Pnp3.Internal.PsubsetPpoly.TM
