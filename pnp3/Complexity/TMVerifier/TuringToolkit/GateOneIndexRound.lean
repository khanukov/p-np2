import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleInstances
import Complexity.TMVerifier.TuringToolkit.GateOneReadB

/-!
# G1: one destructive index round, as an arbitrary-configuration regression

**Progress classification: Infrastructure.**

The earlier T2b-2 slice put `bWalk`/`bMark`/`bBack`/`bHop` on top of the generic
thirteen-step rewrite cycle (`FrameRewriteCycleInstances.g1IndexCycle`) with the
one-step bridge `bRoundStart` in front: from `bRoundStart` at head `4p + 4`, one
bridge step reaches `bWalk .p3` at `4p + 3` and thirteen round steps reach
`bWalk .p3` at `4p - 1`, replacing the frame at ordinal `p` — an `index` — by
`spent`, every other cell bit-for-bit unchanged.

**This is no longer a route of a real run.**  The cursor-walk slice re-points the
forward table's positive-index row to the installation scan `bInsSeek`
(`GateOneRouting.g1_bScan_index_install`), and `bRoundStart` is not a target of
`g1Advance` at all (`GateOneRouting.g1_bRoundStart_unreachable`).  What follows
is therefore an **arbitrary-configuration regression** of the generic rewrite
kernel at the G1 control — the caller supplies the configuration, the frame list
and the safety bound — and nothing composes it from `G1M.initialConfig`.  In
particular nothing claims that *repeating* this cycle addresses an operand-2
value: `bWalk` stops on **any** `index`, so once the operand-2 field empties the
walk would cross the opening `argSep` and consume operand-1 units.  That is
exactly why the cursor walk exists; its live, re-pointed route is
`GateOneInstallScan.g1CS_readB_install_scan_exact`.

Retained here: the fourteen-step composition `g1CS_round_from_bridge` and its
provider chain (`g1CS_step_round_bridge` in `GateOneReadB`,
`g1CS_index_round_onList` in `FrameRewriteCycleInstances`), plus one literal
frame-list probe.  Removed with the re-point: the first-round step count, the
initial-configuration bridge boundary, the composed first round and the concrete
`151`-step projections — every one of them asserted a live route the table no
longer has.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- **Fourteen genuine steps from the bridge boundary.**  On a tape backed by an
arbitrary frame list `pre ++ index :: suffix`, with the head on the first cell of
the frame *after* the `index` and the control in `bRoundStart`, the bridge and
the thirteen-step round replace that `index` by `spent` — nothing else on the
tape changes — and leave the head on the last cell of the frame *before* it, in
the reverse-read entry shape `bWalk .p3`, with the whole `G1Ctx` preserved.

The configuration is the **caller's**: the forward table never produces
`bRoundStart`, so no execution of `G1M` from a real initial configuration
reaches this hypothesis. -/
theorem g1CS_round_from_bridge (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length + 4) hsafe
          (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
          .bRoundStart .p0 false false false ctx) 14 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .bWalk .p3 false false false ctx := by
  have hb := g1CS_step_round_bridge n (4 * pre.length + 4) hsafe (by omega)
    (g1ListTape (n := n)
      ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits)) ctx
  have hc := g1CS_index_round_onList n pre suffix ctx hpre hsafe
  show TM.runConfig (M := G1M) _ (1 + 13) = _
  rw [runConfig_add, hb]
  simpa [show 4 * pre.length + 4 - 1 = 4 * pre.length + 3 from by omega] using hc

/-! ## A concrete frame list

Every number below is a literal.  The configuration is supplied by the caller —
it is *not* reached from `G1M.initialConfig` — so this is a regression, not a
route. -/

/-- A thirteen-frame word with one `index` frame at ordinal `7`. -/
def g1RoundProbeFramesIn : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .separator,
    .data true, .output false, .finish, .blank]

/-- The same word after the round: the frame at ordinal `7` is `spent`. -/
def g1RoundProbeFramesOut : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .separator,
    .data true, .output false, .finish, .blank]

/-- **The composed round on a literal frame list.**  Fourteen genuine steps from
head `32` in `bRoundStart` leave the head at `27` in `bWalk .p3` and change
exactly the four cells `28 … 31`.  Both the tape length `n` and the numeric
safety bound are the caller's. -/
theorem g1CS_round_probe (n : Nat) (ctx : G1Ctx) (hsafe : 32 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 32 hsafe
          (g1ListTape (g1RoundProbeFramesIn.flatMap G1Frame.bits))
          .bRoundStart .p0 false false false ctx) 14 =
      g1AlignedConfig n 27 (by omega)
        (g1ListTape (g1RoundProbeFramesOut.flatMap G1Frame.bits))
        .bWalk .p3 false false false ctx := by
  have h := g1CS_round_from_bridge n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep]
    [.separator, .data true, .output false, .finish, .blank] ctx
    (by simp) (by simpa using hsafe)
  simpa [g1RoundProbeFramesIn, g1RoundProbeFramesOut] using h

end Pnp3.Internal.PsubsetPpoly.TM
