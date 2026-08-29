import Complexity.TMVerifier.TuringToolkit.GateOneRouting
import Complexity.TMVerifier.TuringToolkit.GateOneSemantics
import Complexity.TMVerifier.TuringToolkit.GateOneValidation

/-!
# G1 exact execution: the pass-B rescan, routing and the zero-index operand read

**Progress classification: Infrastructure.**

The executable layer of the T2b pass-B slice.  The five named arrival capstones
below start from the *real* initial configuration
`G1M.initialConfig (g1Point (encodeG1 r))` of the one fixed zero-parameter
machine, compose the exact T2a validation/rewind prefix, and run the
`readBStart` handoff for a further exact, literal number of steps.  Their named
arrival counts are closed expressions in the encoded length and are proved to
fit `g1Clock`.  Local step adapters intentionally quantify over arbitrary
aligned tapes.  The stable `bOOB` `+ k` theorem allows an arbitrary extra
budget and makes no public-clock claim.

**The tag is physically rescanned.**  At the T2a handoff the context is
`g1Ctx0` and no gate tag is retained anywhere: `G1State` has no `Nat`, index,
width, offset, data length or request-dependent field at all.  The route is
selected by reading `bof · tag^units · argSep` off the tape a second time,
through the *generic* frame-scanner kernel; the tag never enters a theorem as a
hypothesis about the machine's state, only as a fact about the encoded request.

Five exact endpoints are proved, from `initialConfig`, for a canonical `r`:

| tag | endpoint | head | extra steps after the T2a prefix |
|-----|----------|------|----------------------------------|
| `input`, `not` | `readAResetStart` | `4 * (units + 2)` | `4 * (units + 2)` |
| `const` | `readAResetStart`, `g1ResultCtx b` | `4 * (units + arg1 + 3)` | `4 * (units + arg1 + 3) + 1` |
| `and`, `or` | `bScan` at the operand-2 field | `4 * (units + arg1 + 3)` | `4 * (units + arg1 + 3)` |
| `and`, `or`, `arg2 = 0` | `readAResetStart`, `vB = b` | `4 * (units + arg1 + 5)` | `4 * (units + arg1 + 5) + 1` |
| `and`, `or`, `arg2 = 0`, empty data | `bOOB` (stable) | `4 * (units + arg1 + 5)` | `4 * (units + arg1 + 5)` |

The `arg2 > 0` branch leaves this module at `bScan` (row three): its continuation
is the installation scan of `GateOneInstallScan`.

In **every** case the tape is bit-for-bit the initial tape: the whole pass-B
rescan is read-only, so no `spent`/`cursor` marker is left behind and no data
cursor needs restoring.  The head of the `input`/`not` endpoint is the first
cell of the operand-1 field, and the head of the binary field endpoint is the
first cell of the operand-2 field — in both cases the cell of the
`argSep`/`separator` that closes the field when the field is empty — so pass A
and the operand-2 walk both continue from a physically addressed cell, with no
producer annotation anywhere.

**Which value is read, and why it is not advice.**  The `const` literal is
pinned to the pure semantics through `r.spec = some b`, which for `const`
*determines* the encoded operand-1 field (`g1_const_fields_of_spec`), so the
machine decodes the very run the encoder wrote.  The operand-2 value is pinned
to the pure selector `r.vals[r.arg2]? = some b` on the request that is actually
encoded, and `arg2 = 0` turns that into a hypothesis about the head of the
encoded data region.  No value is supplied to the machine, and no target,
cursor or index annotation is added to `encodeG1`.

**Scope and deferrals.**  The operand-2 value is resolved *physically*, out of
the unannotated data region, exactly for `arg2 = 0`: the walk meets the
`separator` with no unspent `index` unit left, and the probe reads the frame
behind it.  For `arg2 > 0` the fixed control enters `bInsSeek`, the installation
scan of the positive-index branch; the exact route to its endpoint is
`GateOneInstallScan.g1CS_readB_install_scan_exact`, and that endpoint is where
every statement **of this module** from a real initial configuration stops.
The walk continuing from it is `GateOneWalkInvariant`/`GateOneWalkDriver`
(PR3a–PR3c): `g1CS_readB_positive_exact` is the exact `arg2 > 0` counterpart of
the `arg2 = 0` row above, so the machine *does* resolve the selected data frame
for a positive index — but on a tape whose operand-2 field the walk leaves
consumed.  The `spent ↦ index` repair sweep that restores it is
`GateOneRepairKernel`/`GateOneRepairDriver` (Repair-1/Repair-2a), entered through
the `g1CS_step_readAReset_bridge` boundary below; no theorem *of this module*
composes it.

`g1CS_step_round_bridge` below is the exact one-step execution of the older
bridge `bRoundStart`, which is **no longer a target of the forward table**
(`g1_bRoundStart_unreachable`) and survives only as an arbitrary-configuration
regression composed in `GateOneIndexRound`.

`bOOB` is likewise a **stable boundary of the read**, not a rejection:
`g1RejectState` is a different state and no acceptance or rejection semantics
is attached to either.  There is no `TM.run`, `TM.accepts`, output write,
combine step, operand-1 read, `spec`-correctness claim or full-clock theorem.
`readAStart` is the live pass-A dispatch; `combineStart` and `bOOB` remain
stationary boundaries, and `readAResetStart` is the repair sweep's bridge.  Clock lemmas
bound only the proved arrival prefixes against the **unchanged** clock
`g1Clock`.

S1b2a changes only the unary and constant endpoints in the table above.  Their
pure rewinds to head-zero `readAStart` are composed in
`GateOneRepairDriver`; this module deliberately stops at `readAResetStart`.

The five initial-configuration capstones are scoped to the exact tape
`encodeG1 r`; reusable local adapters state their arbitrary aligned tapes
explicitly, and post-boundary stability budgets carry no public-clock bound.
No capstone claim is made about physically padded tapes.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## Budget arithmetic

Every named arrival route reads a prefix of the canonical word, so its physical
length is at most `(encodeG1 r).length`, far inside both the tape and the public
clock.  `g1Clock` is **unchanged**: the arrival lemmas below prove their named
prefix counts fit the existing quadratic clock.  Arbitrary stability budgets
are not included in that claim. -/

/-- A frame count inside the canonical word costs at most the whole word. -/
theorem g1_route_le (r : G1Request) (k : Nat)
    (hk : k ≤ r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :
    4 * k ≤ (encodeG1 r).length := by
  rw [encodeG1_length]; omega

/-- Every frame boundary of a route is far inside the tape. -/
theorem g1_route_lt_tapeLength (r : G1Request) (k : Nat)
    (hk : k ≤ r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :
    4 * k < G1M.tapeLength (encodeG1 r).length :=
  g1_lt_tapeLength (by have := g1_route_le r k hk; omega)

/-- **The whole proved prefix fits the unchanged public clock**, with the
dispatch step included.  Every clock claim of this slice is a corollary. -/
theorem g1_readB_steps_le_clock (r : G1Request) (k : Nat)
    (hk : k ≤ r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :
    g1ReadBHandoffSteps r + 4 * k + 1 ≤ g1Clock (encodeG1 r).length := by
  have hle := g1_route_le r k hk
  have hmul : 512 * ((encodeG1 r).length + 1) ≤
      512 * ((encodeG1 r).length + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)
  simp only [g1ReadBHandoffSteps, g1Clock]
  omega

/-! ## The pass-B scan, generically

One composition lemma does all the execution work: it glues the exact T2a
prefix to the *generic* frame-scanner kernel, instantiated at the G1 machine.
No transition table is unfolded here, and no T1 theorem is transported. -/

/-- **From the real initial configuration through any valid pass-B route.**
Reading a grammar-valid prefix `route` of the canonical word from the T2a
handoff costs exactly four steps per frame, leaves the tape bit-for-bit the
initial tape, and lands at the frame boundary in the folded mode with the
context still `g1Ctx0`. -/
theorem g1CS_readB_scan (r : G1Request) (hc : r.Canonical)
    (route suffix : List G1Frame)
    (hsplit : route ++ suffix = encodeG1Frames r ++ [.blank])
    (hpath : G1ValidPath .readBStart route)
    (hsafe : 4 * route.length < G1M.tapeLength (encodeG1 r).length) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * route.length) =
      g1AlignedConfig (encodeG1 r).length (4 * route.length) hsafe
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        (g1AdvanceList .readBStart route) .p0 false false false g1Ctx0 := by
  rw [runConfig_add, g1CS_validate_rewind_readB_exact r hc]
  have htape : frameListTape (L := G1M.tapeLength (encodeG1 r).length)
      (([] ++ route ++ suffix).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [List.nil_append, hsplit]
    exact g1ListTape_validation_eq_initial r
  have hscan := g1FrameScanner_scanFrames (encodeG1 r).length [] route suffix
    .readBStart g1Ctx0 ((g1FrameScanner_validPath _ _).mpr hpath)
    (by simpa using hsafe)
  rw [htape] at hscan
  simpa [g1AlignedFrame_eq, g1FrameScanner_advanceList] using hscan

/-! ## The stationary dispatch and handoff steps

Each is one generic aligned-step adapter applied to one standalone tuple lemma
of `GateOneControl`; `g1Transition` is never unfolded. -/

/-- **A stationary self-looping state is stable for the whole remaining
budget.**  The three idle handoffs and the two sinks are all of this shape. -/
theorem g1CS_runConfig_stable (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (q : G1State)
    (hq : ∀ (phase : Fin 1) (scan : Bool),
      g1Transition phase q scan = (0, q, scan, .stay)) (k : Nat) :
    TM.runConfig (M := G1M) (g1AlignedConfigQ n h hh tape q) k =
      g1AlignedConfigQ n h hh tape q := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show k + 1 = 1 + k from Nat.add_comm k 1, runConfig_add, runConfig_one]
      have hstep := g1CS_aligned_step_stay n h hh tape q q (tape ⟨h, hh⟩)
        (fun phase => hq phase _)
      rw [writeCell_self] at hstep
      rw [hstep]
      exact ih

/-- **The out-of-range boundary is stable.**  This is a boundary of the operand
read, not a rejection: `bOOB` is its own state and the machine never leaves
it. -/
theorem g1CS_runConfig_oob_sink (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .bOOB .p0 false false false ctx) k =
      g1AlignedConfig n h hh tape .bOOB .p0 false false false ctx :=
  g1CS_runConfig_stable n h hh tape (g1OOBState ctx)
    (fun phase scan => g1Transition_bOOB_stable phase .p0 false false false
      scan ctx) k

/-- The executed entry branch of the live `readAStart` dispatch. -/
theorem g1CS_step_readAStart_entry (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx)
    (hpass : ctx.pass = false) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .readAStart .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .aBof .p0 false false false ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape (g1ReadAState ctx)
    (g1ABofState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_readAStart_entry phase .p0 false false false _
      ctx hpass)
  rwa [writeCell_self] at hstep

/-- The executed result branch of the live `readAStart` dispatch. -/
theorem g1CS_step_readAStart_result (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx)
    (hpass : ctx.pass = true) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .readAStart .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .combineStart .p0 false false false ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape (g1ReadAState ctx)
    (g1CombineState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_readAStart_result phase .p0 false false false _
      ctx hpass)
  rwa [writeCell_self] at hstep

/-- A successful operand-B context always takes the entry branch; its `vB`
cannot be treated as the final gate result. -/
theorem g1CS_step_readAStart_operandB_not_result (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (b : Bool) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .readAStart .p0 false false false
          (g1Ctx0.withVB b)) 1 =
      g1AlignedConfig n h hh tape .aBof .p0 false false false
        (g1Ctx0.withVB b) ∧
      (TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .readAStart .p0 false false false
          (g1Ctx0.withVB b)) 1).state.snd.mode ≠ .combineStart := by
  rw [g1CS_step_readAStart_entry n h hh tape (g1Ctx0.withVB b) rfl]
  exact ⟨rfl, fun h => G1Mode.noConfusion h⟩

/-- **The combine handoff is idle in this slice.**  A result-ready `readAStart`
now reaches it in one step.  Nothing combines, writes or accepts. -/
theorem g1CS_runConfig_combine_idle (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .combineStart .p0 false false false ctx)
        k =
      g1AlignedConfig n h hh tape .combineStart .p0 false false false ctx :=
  g1CS_runConfig_stable n h hh tape (g1CombineState ctx)
    (fun phase scan => g1Transition_combineStart_idle phase .p0 false false
      false scan ctx) k

/-- **The bridge into the operand-2 repair sweep, executed.**  `readAResetStart`
is *not* idle: one genuine TM step moves the head one cell to the **left** —
from the frame boundary a successful operand-2 read stops on back onto the last
cell of the frame in front of it — writes back the cell it scanned, so **not one
tape cell changes**, keeps the whole `G1Ctx` (in particular the latched `vB`),
and enters the reverse-read entry shape `bRepairSeek .p3` with an empty frame
buffer.

This is the exact one-step boundary the repair sweep of `GateOneRepairKernel`
starts from.  The theorem it replaces, `g1CS_runConfig_readAReset_idle`, is gone
with the idle row: the handoff now does work.  The head position is the
caller's; the *request-specific* head is supplied by
`GateOneRepairDriver`. -/
theorem g1CS_step_readAReset_bridge (n h : Nat) (hh : h < G1M.tapeLength n)
    (hpos : 0 < h) (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .readAResetStart .p0 false false false ctx)
        1 =
      g1AlignedConfig n (h - 1) (by omega) tape .bRepairSeek .p3
        false false false ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_left n h hh hpos tape (g1ReadAResetState ctx)
    (g1RepairSeekState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_readAResetStart_bridge phase .p0 false false
      false _ ctx)
  rwa [writeCell_self] at hstep

/-- **The bridge into the destructive index round, executed.**  `bRoundStart` is
not idle: one genuine TM step moves the head one cell to the *left* — from the
first cell of the frame after an `index` back onto the last cell of that
`index` — writes back the cell it scanned, so **not one tape cell changes**,
keeps the whole `G1Ctx`, and enters the reverse-read entry shape `bWalk .p3`
with an empty frame buffer.  The head position is the caller's; nothing in this
module puts the machine there.

This is the exact one-step boundary the thirteen-step `index ↦ spent` round of
`FrameRewriteCycleInstances` starts from; `GateOneIndexRound`'s
`g1CS_round_from_bridge` composes the two.  The forward table no longer enters
this mode (`g1_bRoundStart_unreachable`), so the configuration is the caller's:
this is an arbitrary-configuration regression, not a route. -/
theorem g1CS_step_round_bridge (n h : Nat) (hh : h < G1M.tapeLength n)
    (hpos : 0 < h) (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .bRoundStart .p0 false false false ctx) 1 =
      g1AlignedConfig n (h - 1) (by omega) tape .bWalk .p3 false false false
        ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_left n h hh hpos tape (g1RoundState ctx)
    (g1WalkState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_bRoundStart_bridge phase .p0 false false false _
      ctx)
  rwa [writeCell_self] at hstep

/-- **The `const` literal dispatch, executed.**  One stationary step carries the
decoded literal as `g1ResultCtx b` into the canonical rewind. -/
theorem g1CS_step_constLit (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (b : Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape (g1ConstMode b) .p0 false false false ctx)
        1 =
      g1AlignedConfig n h hh tape .readAResetStart .p0 false false false
        (g1ResultCtx b) := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape
    (g1State (g1ConstMode b) .p0 false false false ctx)
    (g1ReadAResetState (g1ResultCtx b)) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_constLit phase b .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-- **The operand-2 store dispatch, executed.**  One stationary step writes the
value just read out of the data region into `vB`. -/
theorem g1CS_step_store (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (b : Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape (g1StoreMode b) .p0 false false false ctx)
        1 =
      g1AlignedConfig n h hh tape .readAResetStart .p0 false false false
        (ctx.withVB b) := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape
    (g1State (g1StoreMode b) .p0 false false false ctx)
    (g1ReadAResetState (ctx.withVB b)) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_store phase b .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-! ## Step counts

Each is the exact T2a prefix plus four steps per rescanned frame, plus the one
stationary dispatch step where a Boolean is stored. -/

/-- Steps from `initialConfig` to the rewind boundary of `input`/`not`. -/
def g1ReadARouteSteps (r : G1Request) : Nat :=
  g1ReadBHandoffSteps r + 4 * (r.tag.units + 2)

/-- Steps from `initialConfig` to the operand-2 field of `and`/`or`. -/
def g1FieldRouteSteps (r : G1Request) : Nat :=
  g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 3)

/-- Steps from `initialConfig` to the `const` result-context rewind boundary. -/
def g1ConstRouteSteps (r : G1Request) : Nat := g1FieldRouteSteps r + 1

/-- Steps from `initialConfig` to the pass-A reset boundary of a zero-index
operand-2 read. -/
def g1ReadBSteps (r : G1Request) : Nat :=
  g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 5) + 1

/-- Steps from `initialConfig` to the stable out-of-range boundary. -/
def g1ReadBOOBSteps (r : G1Request) : Nat :=
  g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 5)

theorem g1ReadARouteSteps_le_clock (r : G1Request) :
    g1ReadARouteSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + 2) (by omega)
  simp only [g1ReadARouteSteps]
  omega

theorem g1FieldRouteSteps_le_clock (r : G1Request) :
    g1FieldRouteSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + r.arg1 + 3) (by omega)
  simp only [g1FieldRouteSteps]
  omega

theorem g1ConstRouteSteps_le_clock (r : G1Request) :
    g1ConstRouteSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + r.arg1 + 3) (by omega)
  simp only [g1ConstRouteSteps, g1FieldRouteSteps]
  omega

theorem g1ReadBSteps_le_clock (r : G1Request) :
    g1ReadBSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + r.arg1 + 5) (by omega)
  simp only [g1ReadBSteps]
  omega

theorem g1ReadBOOBSteps_le_clock (r : G1Request) :
    g1ReadBOOBSteps r ≤ g1Clock (encodeG1 r).length := by
  have h := g1_readB_steps_le_clock r (r.tag.units + r.arg1 + 5) (by omega)
  simp only [g1ReadBOOBSteps]
  omega

/-! ## The three exact routing capstones -/

/-- **`input` and `not`: exact dispatch to the rewind boundary.**  From the real
initial configuration, exactly `g1ReadARouteSteps r` genuine steps validate the
word, rewind, physically rescan the unary tag and stop at `readAResetStart` with the
head on the **first cell of the operand-1 field** (the closing `argSep` when
`arg1 = 0`), the context still `g1Ctx0`, and the tape bit-for-bit the initial
tape.  `GateOneRepairDriver` composes the pure rewind to `readAStart`. -/
theorem g1CS_readB_route_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadARouteSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + 2))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false g1Ctx0 := by
  have hsafe : 4 * (g1TagRouteFrames r).length <
      G1M.tapeLength (encodeG1 r).length := by
    rw [g1TagRouteFrames_length]
    exact g1_route_lt_tapeLength r _ (by omega)
  have h := g1CS_readB_scan r hc (g1TagRouteFrames r) (g1TagRouteRest r)
    (g1TagRoute_split r) (g1TagRoute_validPath r) hsafe
  rw [g1TagRoute_advance_unary r ht] at h
  simpa [g1ReadARouteSteps] using h

/-- **`and` and `or`: exact dispatch to the operand-2 field.**  The head stops
on the **first cell of `index^arg2`** (the `separator` closing that field when
`arg2 = 0`), the tape is unchanged, and the mode is the operand-2 walk
`bScan`.  This endpoint holds for every `arg2`. -/
theorem g1CS_readB_route_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1FieldRouteSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 3))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bScan .p0 false false false g1Ctx0 := by
  have hsafe : 4 * (g1FieldRouteFrames r).length <
      G1M.tapeLength (encodeG1 r).length := by
    rw [g1FieldRouteFrames_length]
    exact g1_route_lt_tapeLength r _ (by omega)
  have h := g1CS_readB_scan r hc (g1FieldRouteFrames r) (g1FieldRouteRest r)
    (g1FieldRoute_split r) (g1FieldRoute_validPath_binary r ht) hsafe
  rw [g1FieldRoute_advance_binary r ht] at h
  simpa [g1FieldRouteSteps] using h

/-- The canonical `const` field is the unary literal of its `spec` value: the
literal the machine decodes is exactly the one the encoder wrote. -/
theorem g1_const_fields_of_spec {r : G1Request} (ht : r.tag = .const)
    {b : Bool} (hs : r.spec = some b) :
    r.arg1 = (if b then 1 else 0) ∧ r.arg2 = 0 := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht
  subst ht
  simp only [G1Request.spec] at hs
  split_ifs at hs with h2 h0 h1
  · have hb : b = false := by simpa using hs.symm
    subst hb
    exact ⟨by simp [h0], h2⟩
  · have hb : b = true := by simpa using hs.symm
    subst hb
    exact ⟨by simp [h1], h2⟩

/-- **`const`: exact dispatch to the rewind boundary, with the literal in a
result context.**  From the real initial configuration, exactly
`g1ConstRouteSteps r` genuine steps physically rescan the tag, physically
decode the canonical unary literal field, and store it in `G1Ctx.vB`.  The
literal is pinned to the pure semantics: `b` is the value of `r.spec`, which
for `const` determines the encoded operand-1 run.  The route ends after the
operand-1 field and is therefore independent of the unused `arg2` field.  The
result marker is carried without evaluating the `const` filler of `g1Residual`. -/
theorem g1CS_readB_route_const_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstRouteSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 3))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false (g1ResultCtx b) := by
  obtain ⟨harg, -⟩ := g1_const_fields_of_spec ht hs
  have hsafe : 4 * (g1FieldRouteFrames r).length <
      G1M.tapeLength (encodeG1 r).length := by
    rw [g1FieldRouteFrames_length]
    exact g1_route_lt_tapeLength r _ (by omega)
  have h := g1CS_readB_scan r hc (g1FieldRouteFrames r) (g1FieldRouteRest r)
    (g1FieldRoute_split r) (g1FieldRoute_validPath_const r ht b harg) hsafe
  rw [g1FieldRoute_advance_const r ht b harg] at h
  have hstep := g1CS_step_constLit (encodeG1 r).length
    (4 * (g1FieldRouteFrames r).length) hsafe
    (G1M.initialConfig (g1Point (encodeG1 r))).tape b g1Ctx0
  have hall : TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBHandoffSteps r + 4 * (g1FieldRouteFrames r).length + 1) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1FieldRouteFrames r).length) hsafe
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false (g1ResultCtx b) := by
    rw [runConfig_add, h, hstep]
  simpa [g1ConstRouteSteps, g1FieldRouteSteps] using hall

/-! ## The zero-index operand-2 read

The operand-2 value is resolved out of the **unannotated** data region: `bScan`
stops at the `separator` and the probe reads the frame behind it.  With
`arg2 = 0` there is no unspent `index` unit, so the walk terminates at once and
that frame is `vals[0]` — the value the pure selector `r.vals[r.arg2]?` returns
on the request actually encoded.  Nothing is written, so the data region is
intact and no cursor has to be restored. -/

private theorem g1_head_cons {v : List Bool} {b : Bool} (hb : v[0]? = some b) :
    ∃ rest : List Bool, v = b :: rest := by
  cases v with
  | nil => exact absurd hb (by simp)
  | cons c cs =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      exact ⟨cs, by rw [hb]⟩

private theorem g1_head_nil {v : List Bool} (hb : v[0]? = none) : v = [] := by
  cases v with
  | nil => rfl
  | cons c cs => exact absurd hb (by simp)

private theorem g1_vals_cons_of_zero {r : G1Request} (h2 : r.arg2 = 0)
    {b : Bool} (hb : r.vals[r.arg2]? = some b) :
    ∃ rest : List Bool, r.vals = b :: rest :=
  g1_head_cons (h2 ▸ hb)

private theorem g1_vals_nil_of_zero {r : G1Request} (h2 : r.arg2 = 0)
    (hb : r.vals[r.arg2]? = none) : r.vals = [] :=
  g1_head_nil (h2 ▸ hb)

/-- **The zero-index operand-2 read, exactly.**  For a canonical `and`/`or`
request with `arg2 = 0` whose pure selector gives `r.vals[r.arg2]? = some b`,
exactly `g1ReadBSteps r` genuine steps from the real initial configuration
resolve `b` **off the tape** and leave the machine at the named pass-A reset
boundary `readAResetStart`, with `vB = b`, the head exactly at
`4 * (units + arg1 + 5)` — the frame boundary just past the selected data
frame — and the tape **bit-for-bit the initial tape**: the read is
non-destructive, so no marker remains and no data cursor needs restoring. -/
theorem g1CS_readB_zero_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false (g1Ctx0.withVB b) := by
  obtain ⟨rest, hv⟩ := g1_vals_cons_of_zero h2 hb
  have hsafe : 4 * (g1ReadBRouteFrames r b).length <
      G1M.tapeLength (encodeG1 r).length := by
    rw [g1ReadBRouteFrames_length]
    exact g1_route_lt_tapeLength r _ (by omega)
  have h := g1CS_readB_scan r hc (g1ReadBRouteFrames r b)
    (rest.map .data ++ [.output false, .finish, .blank])
    (g1ReadBRoute_split r h2 b rest hv) (g1ReadBRoute_validPath r ht b) hsafe
  rw [g1ReadBRoute_advance r ht b] at h
  have hstep := g1CS_step_store (encodeG1 r).length
    (4 * (g1ReadBRouteFrames r b).length) hsafe
    (G1M.initialConfig (g1Point (encodeG1 r))).tape b g1Ctx0
  have hall : TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBHandoffSteps r + 4 * (g1ReadBRouteFrames r b).length + 1) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1ReadBRouteFrames r b).length) hsafe
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false (g1Ctx0.withVB b) := by
    rw [runConfig_add, h, hstep]
  simpa [g1ReadBSteps] using hall

/-- **The zero-index out-of-range boundary, exactly.**  For a canonical
`and`/`or` request with `arg2 = 0` and `r.vals[r.arg2]? = none` — that is, an
empty encoded data region — the probe meets the `output` destination frame
instead of a data frame and the machine stops at the explicit, **stable**
out-of-range boundary `bOOB` after exactly `g1ReadBOOBSteps r` steps, head
`4 * (units + arg1 + 5)`, tape bit-for-bit the initial tape.  This is a
boundary, **not** a rejection: nothing is stored in `vB`, the machine never
leaves `bOOB`, and `g1RejectState` is a different state. -/
theorem g1CS_readB_zero_oob_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0)
    (hb : r.vals[r.arg2]? = none) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bOOB .p0 false false false g1Ctx0 := by
  have hv := g1_vals_nil_of_zero h2 hb
  have hsafe : 4 * (g1ReadBOOBFrames r).length <
      G1M.tapeLength (encodeG1 r).length := by
    rw [g1ReadBOOBFrames_length]
    exact g1_route_lt_tapeLength r _ (by omega)
  have h := g1CS_readB_scan r hc (g1ReadBOOBFrames r) [.finish, .blank]
    (g1ReadBOOB_split r h2 hv) (g1ReadBOOB_validPath r ht) hsafe
  rw [g1ReadBOOB_advance r ht] at h
  simpa [g1ReadBOOBSteps] using h

/-- **The out-of-range boundary is stable for the whole remaining budget.** -/
theorem g1CS_readB_zero_oob_stable (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0)
    (hb : r.vals[r.arg2]? = none) (k : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBOOBSteps r + k) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bOOB .p0 false false false g1Ctx0 := by
  rw [runConfig_add, g1CS_readB_zero_oob_exact r hc ht h2 hb]
  exact g1CS_runConfig_oob_sink _ _ _ _ _ k

/-! ## The components of the capstones, separately -/

theorem g1CS_readB_zero_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBSteps r)).head : Nat) = 4 * (r.tag.units + r.arg1 + 5) := by
  rw [g1CS_readB_zero_exact r hc ht h2 b hb]; rfl

/-- **The resolved operand-2 value really is in the fixed Boolean field.** -/
theorem g1CS_readB_zero_vB (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBSteps r)).state.snd.ctx.vB = b := by
  rw [g1CS_readB_zero_exact r hc ht h2 b hb]; rfl

/-- **The zero-index operand read is non-destructive.**  Not a single tape cell
changes, so the data region is intact and pass A needs no repair. -/
theorem g1CS_readB_zero_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_readB_zero_exact r hc ht h2 b hb]; rfl

theorem g1CS_readB_zero_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBSteps r)).state.snd = g1ReadAResetState (g1Ctx0.withVB b) := by
  rw [g1CS_readB_zero_exact r hc ht h2 b hb]; rfl

/-- The pass-B execution stays in the machine's unique public start phase. -/
theorem g1CS_readB_zero_phase (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBSteps r)).state.fst = g1CS.toPhased.startPhase := by
  rw [g1CS_readB_zero_exact r hc ht h2 b hb]; rfl

theorem g1CS_readB_zero_oob_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0)
    (hb : r.vals[r.arg2]? = none) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBOOBSteps r)).state.snd = g1OOBState g1Ctx0 := by
  rw [g1CS_readB_zero_oob_exact r hc ht h2 hb]; rfl

theorem g1CS_readB_zero_oob_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0)
    (hb : r.vals[r.arg2]? = none) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBOOBSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_readB_zero_oob_exact r hc ht h2 hb]; rfl

/-- **Success and out-of-range are different boundaries.**  The two endpoints
are literally distinct states, so neither branch can be mistaken for the
other. -/
theorem g1CS_readB_zero_oob_ne_success (ctx : G1Ctx) :
    g1OOBState g1Ctx0 ≠ g1ReadAResetState ctx :=
  g1OOBState_ne_readAReset g1Ctx0 ctx

/-- **The out-of-range boundary is not the reject sink.**  `bOOB` records that
the operand index selects nothing; it carries no rejection semantics. -/
theorem g1CS_readB_oob_ne_reject : g1OOBState g1Ctx0 ≠ g1RejectState := by
  intro h
  have hmode : G1Mode.bOOB = G1Mode.reject := congrArg G1State.mode h
  exact G1Mode.noConfusion hmode

theorem g1CS_readB_route_unary_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadARouteSteps r)).head : Nat) = 4 * (r.tag.units + 2) := by
  rw [g1CS_readB_route_unary_exact r hc ht]; rfl

theorem g1CS_readB_route_unary_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadARouteSteps r)).state.snd = g1ReadAResetState g1Ctx0 := by
  rw [g1CS_readB_route_unary_exact r hc ht]; rfl

theorem g1CS_readB_route_unary_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadARouteSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_readB_route_unary_exact r hc ht]; rfl

theorem g1CS_readB_route_const_vB (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstRouteSteps r)).state.snd.ctx.vB = b := by
  rw [g1CS_readB_route_const_exact r hc ht b hs]; rfl

theorem g1CS_readB_route_const_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstRouteSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_readB_route_const_exact r hc ht b hs]; rfl

theorem g1CS_readB_route_binary_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1FieldRouteSteps r)).head : Nat) =
      4 * (r.tag.units + r.arg1 + 3) := by
  rw [g1CS_readB_route_binary_exact r hc ht]; rfl

end Pnp3.Internal.PsubsetPpoly.TM
