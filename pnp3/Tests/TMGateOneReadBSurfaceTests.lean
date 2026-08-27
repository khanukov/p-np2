import Complexity.TMVerifier.TuringToolkit.GateOneReadBExamples

/-!
# G1 one-gate interpreter, pass-B execution layer: surface tests

Import-side contracts for the T2b pass-B *execution* surface: the exact
`TM.runConfig` route capstones from the real initial configuration
`G1M.initialConfig (g1Point (encodeG1 r))`, the `const` literal decode, the
zero-index operand-2 read, the stable out-of-range boundary, the deferred
positive-index boundary, the idleness of the five handoffs, and the named
per-route examples.  The frame-level routing itself is pinned by
`Tests.TMGateOneRoutingSurface`; only the newly added deferred route is
re-pinned here.

Every theorem pinned here is scoped to `encodeG1 r`, and none of them runs the
machine past a handoff.  In particular there is **no** `TM.run`, `TM.accepts`,
output-write, combine, pass-A or `spec`-correctness surface, and the `arg2 > 0`
operand-2 walk is pinned only *up to* the deferred `bRoundStart` boundary,
together with the fact that the machine never leaves it.  This is an audit
surface: it pins public signatures, it does not prove anything new.
-/

namespace Pnp3.Tests.TMGateOneReadBSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

/-! ## The deferred positive-index route, at frame level -/

#check @g1RoundRouteFrames
#check @g1RoundRouteFrames_length
#check @g1RoundRoute_split
#check @g1RoundRoute_advance
#check @g1RoundRoute_validPath

/-! ## Budget: the routes fit the tape and the unchanged public clock -/

#check @g1_route_le
#check @g1_route_lt_tapeLength
#check @g1_readB_steps_le_clock
#check @g1ReadARouteSteps
#check @g1FieldRouteSteps
#check @g1ConstRouteSteps
#check @g1ReadBSteps
#check @g1ReadBOOBSteps
#check @g1RoundRouteSteps
#check @g1ReadARouteSteps_le_clock
#check @g1FieldRouteSteps_le_clock
#check @g1ConstRouteSteps_le_clock
#check @g1ReadBSteps_le_clock
#check @g1ReadBOOBSteps_le_clock
#check @g1RoundRouteSteps_le_clock

/-! ## Exact execution: the generic pass-B scan and the stationary dispatches -/

#check @g1CS_readB_scan
#check @g1CS_runConfig_stable
#check @g1CS_step_constLit
#check @g1CS_step_store

/-! ## The five handoffs, all idle in this slice -/

#check @g1CS_runConfig_readA_idle
#check @g1CS_runConfig_combine_idle
#check @g1CS_runConfig_readAReset_idle
#check @g1CS_runConfig_round_idle
#check @g1CS_runConfig_oob_sink

/-! ## The exact route capstones from the real initial configuration -/

#check @g1CS_readB_route_unary_exact
#check @g1CS_readB_route_binary_exact
#check @g1_const_fields_of_spec
#check @g1CS_readB_route_const_exact
#check @g1CS_readB_zero_exact
#check @g1CS_readB_zero_oob_exact
#check @g1CS_readB_zero_oob_stable
#check @g1CS_readB_round_deferred_exact
#check @g1CS_readB_round_deferred_stable

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
#check @g1CS_readB_round_deferred_state

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
#check @G1Examples.readB_round_and
#check @G1Examples.readB_round_or
#check @G1Examples.readB_round_and_stable
#check @G1Examples.readB_deferred_at_index
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

/-- **The deferred positive-index boundary, and the fact that nothing passes
it.**  For `arg2 > 0` the machine stops at `bRoundStart` and stays there for
every further budget, so no runtime-index addressing is claimed. -/
theorem check_g1CS_readB_round_deferred_stable (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (k : Nat)
    (h2 : r.arg2 = k + 1) (m : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 4) + m) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 4))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bRoundStart .p0 false false false g1Ctx0 :=
  g1CS_readB_round_deferred_stable r hc ht k h2 m

/-- The `const` boundary is idle: nothing combines, writes or accepts. -/
theorem check_g1CS_runConfig_combine_idle (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .combineStart .p0 false false false ctx)
        k =
      g1AlignedConfig n h hh tape .combineStart .p0 false false false ctx :=
  g1CS_runConfig_combine_idle n h hh tape ctx k

theorem check_g1RoundRoute_split (r : G1Request) (k : Nat)
    (h2 : r.arg2 = k + 1) :
    g1RoundRouteFrames r ++
        (List.replicate k .index ++ .separator ::
          (r.vals.map .data ++ [.output false, .finish, .blank])) =
      encodeG1Frames r ++ [.blank] :=
  g1RoundRoute_split r k h2

end Pnp3.Tests.TMGateOneReadBSurface
