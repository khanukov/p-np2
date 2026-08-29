import Complexity.TMVerifier.TuringToolkit.GateOneIndexRound
import Complexity.TMVerifier.TuringToolkit.GateOneInstallScanExamples
import Complexity.TMVerifier.TuringToolkit.GateOneReadBExamples

/-!
# G1 one-gate interpreter, pass-B execution layer: surface tests

Import-side contracts for the T2b pass-B *execution* surface: exact
`TM.runConfig` route capstones from the real initial configuration
`G1M.initialConfig (g1Point (encodeG1 r))`, the `const` literal decode, the
zero-index operand-2 read, the stable out-of-range boundary, the three remaining
idle handoffs, the executed `readAResetStart` bridge into the repair sweep,
named per-route examples, the **installation scan** that the re-pointed
positive-index row opens, and the thirteen-step rewrite cycle kept as an
arbitrary-configuration regression.

The initial-configuration capstones are scoped to the exact tape `encodeG1 r`.
Local adapters intentionally use arbitrary aligned tapes; post-boundary
stability pins have no public-clock bound.  There is **no** `TM.run`,
`TM.accepts`, output-write, combine, pass-A or `spec`-correctness surface, and
for `arg2 > 0` the only endpoint pinned here from a **real** initial
configuration is the read-only installation scan, which stops at `bProbe2` and
is unchanged by this slice.  The probe, latch and cursor install behind it are
pinned by `TMGateOneProbeInstallSurfaceTests`, and the seek, mark, scan, turn
and restore of one normal round — plus the terminal exhaustion path behind the
`bExh` handoff — by `TMGateOneWalkSurfaceTests`,
on caller-supplied configurations only.  Nothing here pins a latch, a cursor
install, a round, an iteration, runtime addressing, a positive-index
operand-value read, or acceptance.  This is an audit surface: it pins public
signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneReadBSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

/-! ## The positive-index route, at frame level -/

#check @g1InstallRouteFrames
#check @g1InstallRouteRest
#check @g1InstallRouteFrames_length
#check @g1InstallRoute_split
#check @g1InstallRoute_advance
#check @g1InstallRoute_validPath
#check @g1_bScan_index_install
#check @g1_insSeek_advance
#check @g1_insSeek_validPath
#check @g1_bProbe2_rows
#check @g1_bFwd_rows
#check @g1_bRet_rows
#check @g1_bRoundStart_stuck
#check @g1_bRoundStart_unreachable

/-! ## Budget: the routes fit the tape and the unchanged public clock -/

#check @g1_route_le
#check @g1_route_lt_tapeLength
#check @g1_readB_steps_le_clock
#check @g1ReadARouteSteps
#check @g1FieldRouteSteps
#check @g1ConstRouteSteps
#check @g1ReadBSteps
#check @g1ReadBOOBSteps
#check @g1InstallScanSteps
#check @g1ReadARouteSteps_le_clock
#check @g1FieldRouteSteps_le_clock
#check @g1ConstRouteSteps_le_clock
#check @g1ReadBSteps_le_clock
#check @g1ReadBOOBSteps_le_clock
#check @g1InstallScanSteps_eq
#check @g1InstallScanSteps_le_clock

/-! ## Exact execution: the generic pass-B scan and the stationary dispatches -/

#check @g1CS_readB_scan
#check @g1CS_runConfig_stable
#check @g1CS_step_constLit
#check @g1CS_step_store

-- The three remaining idle handoffs, and the executed `readAResetStart` bridge
-- that replaces the former `g1CS_runConfig_readAReset_idle`.
#check @g1CS_runConfig_readA_idle
#check @g1CS_runConfig_combine_idle
#check @g1CS_runConfig_oob_sink
#check @g1CS_step_readAReset_bridge

/-! ## The exact route capstones from the real initial configuration -/

#check @g1CS_readB_route_unary_exact
#check @g1CS_readB_route_binary_exact
#check @g1_const_fields_of_spec
#check @g1CS_readB_route_const_exact
#check @g1CS_readB_zero_exact
#check @g1CS_readB_zero_oob_exact
#check @g1CS_readB_zero_oob_stable

/-! ## The installation scan: the re-pointed positive-index endpoint -/

#check @G1InstallSkip
#check @g1Advance_bInsSeek_of_skip
#check @g1ValidPath_fix
#check @g1AdvanceList_fix
#check @g1CS_walk_install_scan
#check @g1CS_readB_install_scan_exact
#check @g1CS_readB_install_scan_head
#check @g1CS_readB_install_scan_tape
#check @g1CS_readB_install_scan_state

/-! ## The components of the capstones -/

#check @g1CS_readB_route_unary_head
#check @g1CS_readB_route_unary_state
#check @g1CS_readB_route_unary_tape
#check @g1CS_readB_route_const_vB
#check @g1CS_readB_route_const_tape
#check @g1CS_readB_route_binary_head
#check @g1CS_readB_zero_head
#check @g1CS_readB_zero_vB
#check @g1CS_readB_zero_tape
#check @g1CS_readB_zero_state
#check @g1CS_readB_zero_phase
#check @g1CS_readB_zero_oob_state
#check @g1CS_readB_zero_oob_tape
#check @g1CS_readB_zero_oob_ne_success
#check @g1CS_readB_oob_ne_reject

/-! ## Named examples -/

#check @G1Examples.reqNotRoute_canonical
#check @G1Examples.reqConstFalse_canonical
#check @G1Examples.reqConstTrue_canonical
#check @G1Examples.reqAndTrueB_canonical
#check @G1Examples.reqAndFalseB_canonical
#check @G1Examples.reqOrTrueB_canonical
#check @G1Examples.reqAndOOB_canonical
#check @G1Examples.readB_route_input
#check @G1Examples.readB_route_not
#check @G1Examples.readB_route_input_head
#check @G1Examples.readB_route_not_head
#check @G1Examples.readB_route_input_steps
#check @G1Examples.readB_route_input_clock
#check @G1Examples.readB_const_false
#check @G1Examples.readB_const_true
#check @G1Examples.readB_const_true_vB
#check @G1Examples.readB_const_true_steps
#check @G1Examples.readB_const_true_clock
#check @G1Examples.readB_field_route_and
#check @G1Examples.readB_field_route_or
#check @G1Examples.readB_install_at_index
#check @G1Examples.readB_and_true
#check @G1Examples.readB_and_false
#check @G1Examples.readB_or_true
#check @G1Examples.readB_and_true_vB
#check @G1Examples.readB_and_true_tape
#check @G1Examples.readB_and_true_steps
#check @G1Examples.readB_and_true_clock
#check @G1Examples.readB_and_oob
#check @G1Examples.readB_and_oob_stable
#check @G1Examples.readB_and_oob_state
#check @G1Examples.readB_and_oob_tape
#check @G1Examples.readB_and_oob_steps
#check @G1Examples.readB_and_oob_clock
#check @G1Examples.readB_oob_ne_success
#check @G1Examples.readB_oob_ne_reject

/-! ## Exact theorem-contract pins

Each wrapper restates the endpoint verbatim, so a later slice cannot silently
weaken a hypothesis, drop the tape equation, move a head, or turn a boundary
into an acceptance. -/

theorem check_g1CS_readB_scan (r : G1Request) (hc : r.Canonical)
    (route suffix : List G1Frame)
    (hsplit : route ++ suffix = encodeG1Frames r ++ [.blank])
    (hpath : G1ValidPath .readBStart route)
    (hsafe : 4 * route.length < G1M.tapeLength (encodeG1 r).length) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * route.length) =
      g1AlignedConfig (encodeG1 r).length (4 * route.length) hsafe
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1AdvanceList .readBStart route) .p0 false false false g1Ctx0 :=
  g1CS_readB_scan r hc route suffix hsplit hpath hsafe

theorem check_g1_readB_steps_le_clock (r : G1Request) (k : Nat)
    (hk : k ≤ r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :
    g1ReadBHandoffSteps r + 4 * k + 1 ≤ g1Clock (encodeG1 r).length :=
  g1_readB_steps_le_clock r k hk

/-- **The `input`/`not` handoff.**  Exact steps, exact head on the first cell of
the operand-1 field, `g1Ctx0` untouched, tape bit-for-bit the initial tape. -/
theorem check_g1CS_readB_route_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * (r.tag.units + 2)) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + 2))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAStart .p0 false false false g1Ctx0 :=
  g1CS_readB_route_unary_exact r hc ht

/-- **The `const` literal decode.**  The stored bit is the value of the pure
`spec` of the request that is actually encoded, not a supplied parameter. -/
theorem check_g1CS_readB_route_const_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 3) + 1) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 3))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .combineStart .p0 false false false (g1Ctx0.withVB b) :=
  g1CS_readB_route_const_exact r hc ht b hs

theorem check_g1_const_fields_of_spec {r : G1Request} (ht : r.tag = .const)
    {b : Bool} (hs : r.spec = some b) :
    r.arg1 = (if b then 1 else 0) ∧ r.arg2 = 0 :=
  g1_const_fields_of_spec ht hs

/-- **The `and`/`or` dispatch to the operand-2 field**, for every `arg2`. -/
theorem check_g1CS_readB_route_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 3)) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 3))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bScan .p0 false false false g1Ctx0 :=
  g1CS_readB_route_binary_exact r hc ht

/-- **The zero-index operand-2 read.**  The hypothesis is the pure selector on
the encoded request; the value is resolved off the tape and the tape is
unchanged. -/
theorem check_g1CS_readB_zero_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 5) + 1) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false (g1Ctx0.withVB b) :=
  g1CS_readB_zero_exact r hc ht h2 b hb

/-- **The `readAResetStart` handoff is no longer idle.**  One genuine step is the
repair sweep's bridge: the head moves one cell **left**, the tape is *unchanged*
(the row writes back what it scans), the whole `G1Ctx` — latch included — is
carried through, and the control enters the reverse-read entry shape
`bRepairSeek .p3`.  The configuration is the caller's; the request-specific head
is supplied by `TMGateOneRepairDriverSurfaceTests`. -/
theorem check_g1CS_step_readAReset_bridge (n h : Nat)
    (hh : h < G1M.tapeLength n) (hpos : 0 < h)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .readAResetStart .p0 false false false ctx)
        1 =
      g1AlignedConfig n (h - 1) (by omega) tape .bRepairSeek .p3
        false false false ctx :=
  g1CS_step_readAReset_bridge n h hh hpos tape ctx

/-- **The empty-data boundary is `bOOB`, and it is stable.**  Not an
acceptance, not a rejection: the budget is universally quantified. -/
theorem check_g1CS_readB_zero_oob_stable (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0)
    (hb : r.vals[r.arg2]? = none) (k : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 5) + k) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bOOB .p0 false false false g1Ctx0 :=
  g1CS_readB_zero_oob_stable r hc ht h2 hb k

theorem check_g1CS_readB_oob_ne_reject : g1OOBState g1Ctx0 ≠ g1RejectState :=
  g1CS_readB_oob_ne_reject

theorem check_g1CS_readB_zero_oob_ne_success (ctx : G1Ctx) :
    g1OOBState g1Ctx0 ≠ g1ReadAResetState ctx :=
  g1CS_readB_zero_oob_ne_success ctx

/-- The `const` boundary is idle: nothing combines, writes or accepts. -/
theorem check_g1CS_runConfig_combine_idle (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .combineStart .p0 false false false ctx)
        k =
      g1AlignedConfig n h hh tape .combineStart .p0 false false false ctx :=
  g1CS_runConfig_combine_idle n h hh tape ctx k

theorem check_g1InstallRoute_split (r : G1Request) :
    g1InstallRouteFrames r ++ g1InstallRouteRest r =
      encodeG1Frames r ++ [.blank] :=
  g1InstallRoute_split r

/-! ## The installation scan, pinned exactly

The one executed positive-index endpoint.  Each wrapper restates it verbatim, so
a later slice cannot silently weaken a hypothesis, drop the tape equation, move
the head, or turn the probe into a value read. -/

/-- **The re-pointed positive-index route, exactly.**  Steps, head, control
state, context and the complete tape are all pinned, and the tape is
bit-for-bit the initial tape. -/
theorem check_g1CS_readB_install_scan_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + r.arg2 + 4)) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + 4))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bProbe2 .p0 false false false g1Ctx0 :=
  g1CS_readB_install_scan_exact r hc ht k h2

theorem check_g1CS_readB_install_scan_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r)).head : Nat) =
      4 * (r.tag.units + r.arg1 + r.arg2 + 4) :=
  g1CS_readB_install_scan_head r hc ht k h2

/-- **The installation-scan endpoint tape equals the initial tape.** -/
theorem check_g1CS_readB_install_scan_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1CS_readB_install_scan_tape r hc ht k h2

theorem check_g1CS_readB_install_scan_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1InstallScanSteps r)).state.snd = g1Probe2State g1Ctx0 :=
  g1CS_readB_install_scan_state r hc ht k h2

theorem check_g1InstallScanSteps_le_clock (r : G1Request) :
    g1InstallScanSteps r ≤ g1Clock (encodeG1 r).length :=
  g1InstallScanSteps_le_clock r

/-! ## The concrete installation-scan probe

`⟨and, 0, 2, [false, true, true]⟩`: fifteen encoded frames and `60` input cells;
the explicit list-backed layout appends one `blank`, so it has sixteen frames
and `64` bits. -/

#check @G1InstallScanExamples.g1WalkExample
#check @G1InstallScanExamples.g1WalkExample_canonical
#check @G1InstallScanExamples.g1WalkExample_length
#check @G1InstallScanExamples.g1WalkInitFrames
#check @G1InstallScanExamples.g1WalkExample_initial_tape
#check @G1InstallScanExamples.walk_install_scan_steps
#check @G1InstallScanExamples.walk_install_scan
#check @G1InstallScanExamples.walk_install_scan_head
#check @G1InstallScanExamples.walk_install_scan_state
#check @G1InstallScanExamples.walk_install_scan_tape
#check @G1InstallScanExamples.walk_install_scan_clock

open G1InstallScanExamples in
/-- **Exactly `169` genuine steps** from the real initial configuration reach
`bProbe2` at head `40`, tape bit-for-bit the initial tape. -/
theorem check_walk_install_scan :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 169 =
      g1AlignedConfig (encodeG1 g1WalkExample).length 40
        (g1_route_lt_tapeLength g1WalkExample 10 (by decide))
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))).tape
        .bProbe2 .p0 false false false g1Ctx0 :=
  walk_install_scan

open G1InstallScanExamples in
theorem check_walk_install_scan_head :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 169).head : Nat) =
      40 :=
  walk_install_scan_head

open G1InstallScanExamples in
/-- The literal run leaves the sixteen-frame initial word untouched. -/
theorem check_walk_install_scan_tape :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 169).tape =
      g1ListTape (n := (encodeG1 g1WalkExample).length)
        (g1WalkInitFrames.flatMap G1Frame.bits) :=
  walk_install_scan_tape

open G1InstallScanExamples in
theorem check_walk_install_scan_clock :
    169 ≤ g1Clock (encodeG1 g1WalkExample).length :=
  walk_install_scan_clock

/-! ## The thirteen-step rewrite cycle, as an arbitrary-configuration regression

The forward table never produces `bRoundStart` (`g1_bRoundStart_unreachable`),
so the caller supplies the configuration, the frame list and the safety bound.
Nothing here reaches the bridge from `G1M.initialConfig`, and no iteration,
addressing or `arg2 > 0` value-read surface is pinned. -/

#check @g1CS_step_round_bridge
#check @g1CS_round_from_bridge
#check @g1RoundProbeFramesIn
#check @g1RoundProbeFramesOut
#check @g1CS_round_probe

theorem check_g1CS_round_from_bridge (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length + 4) hsafe
          (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
          .bRoundStart .p0 false false false ctx) 14 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .bWalk .p3 false false false ctx :=
  g1CS_round_from_bridge n pre suffix ctx hpre hsafe

theorem check_g1CS_round_probe (n : Nat) (ctx : G1Ctx)
    (hsafe : 32 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n 32 hsafe
          (g1ListTape (g1RoundProbeFramesIn.flatMap G1Frame.bits))
          .bRoundStart .p0 false false false ctx) 14 =
      g1AlignedConfig n 27 (by omega)
        (g1ListTape (g1RoundProbeFramesOut.flatMap G1Frame.bits))
        .bWalk .p3 false false false ctx :=
  g1CS_round_probe n ctx hsafe

end Pnp3.Tests.TMGateOneReadBSurface
