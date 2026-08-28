import Complexity.TMVerifier.TuringToolkit.GateOneRouting

/-!
# G1 pass-B frame-routing surface tests

Exact import-side contracts for the fixed control's frame-level pass-B routing.
This module pins the physical tag rescan, canonical-word prefix splits,
context-bit preservation, const/store dispatches, zero-index success/OOB, and
the explicit nonzero-index deferral.  It proves no `TM.runConfig`, acceptance,
output, or gate-semantics claim.
-/

namespace Pnp3.Tests.TMGateOneRoutingSurface

open Pnp3.Internal.PsubsetPpoly.TM

#check @g1RouteMode
#check @g1TagRouteFrames
#check @g1FieldRouteFrames
#check @g1ReadBRouteFrames
#check @g1ReadBOOBFrames
#check @g1_tagRescan_advance
#check @g1_tagRescan_validPath
#check @g1TagRoute_split
#check @g1FieldRoute_split
#check @g1ReadBRoute_split
#check @g1ReadBOOB_split
#check @g1TagRoute_advance_unary
#check @g1TagRoute_advance
#check @g1TagRoute_validPath
#check @g1FieldRoute_advance_const
#check @g1FieldRoute_advance_binary
#check @g1ReadBRoute_advance
#check @g1ReadBRoute_validPath
#check @g1ReadBOOB_advance
#check @g1ReadBOOB_validPath
#check @g1_bScan_index_bridge
#check @g1_bRoundStart_stuck
#check @g1Advance_ne_sink
#check @G1ForwardMode.readBStart
#check @g1OOBState_ne_readAReset
#check @G1Ctx.withVB_vB
#check @G1Ctx.withVB_pass
#check @G1Ctx.withVB_crossed
#check @g1Transition_constLit
#check @g1Transition_store
#check @g1Transition_bRoundStart_bridge
#check @g1Transition_bOOB_stable

/-! ## Exact theorem-contract pins -/

theorem check_withVB_vB (ctx : G1Ctx) (b : Bool) :
    (ctx.withVB b).vB = b := G1Ctx.withVB_vB ctx b

theorem check_withVB_pass (ctx : G1Ctx) (b : Bool) :
    (ctx.withVB b).pass = ctx.pass := G1Ctx.withVB_pass ctx b

theorem check_withVB_crossed (ctx : G1Ctx) (b : Bool) :
    (ctx.withVB b).crossed = ctx.crossed := G1Ctx.withVB_crossed ctx b

theorem check_g1Advance_ne_sink (mode : G1Mode) (frame : G1Frame) :
    g1Advance mode frame ≠ .accept ∧ g1Advance mode frame ≠ .rewind :=
  g1Advance_ne_sink mode frame

theorem check_G1ForwardMode_readBStart : G1ForwardMode .readBStart :=
  G1ForwardMode.readBStart

theorem check_g1OOBState_ne_readAReset (ctx ctx' : G1Ctx) :
    g1OOBState ctx ≠ g1ReadAResetState ctx' :=
  g1OOBState_ne_readAReset ctx ctx'

theorem check_g1Transition_constLit (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1ConstMode b) position b0 b1 b2 ctx) scan =
      (0, g1CombineState (ctx.withVB b), scan, .stay) :=
  g1Transition_constLit phase b position b0 b1 b2 scan ctx

theorem check_g1Transition_store (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1StoreMode b) position b0 b1 b2 ctx) scan =
      (0, g1ReadAResetState (ctx.withVB b), scan, .stay) :=
  g1Transition_store phase b position b0 b1 b2 scan ctx

theorem check_g1Transition_bRoundStart_bridge (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .bRoundStart position b0 b1 b2 ctx) scan =
      (0, g1WalkState ctx, scan, .left) :=
  g1Transition_bRoundStart_bridge phase position b0 b1 b2 scan ctx

theorem check_g1Transition_bOOB_stable (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .bOOB position b0 b1 b2 ctx) scan =
      (0, g1OOBState ctx, scan, .stay) :=
  g1Transition_bOOB_stable phase position b0 b1 b2 scan ctx

theorem check_g1ReadBRoute_split (r : G1Request) (h2 : r.arg2 = 0)
    (b : Bool) (rest : List Bool) (hv : r.vals = b :: rest) :
    g1ReadBRouteFrames r b ++
        (rest.map .data ++ [.output false, .finish, .blank]) =
      encodeG1Frames r ++ [.blank] :=
  g1ReadBRoute_split r h2 b rest hv

theorem check_g1ReadBOOB_split (r : G1Request) (h2 : r.arg2 = 0)
    (hv : r.vals = []) :
    g1ReadBOOBFrames r ++ [.finish, .blank] =
      encodeG1Frames r ++ [.blank] :=
  g1ReadBOOB_split r h2 hv

theorem check_g1TagRoute_advance_unary (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1AdvanceList .readBStart (g1TagRouteFrames r) = .readAStart :=
  g1TagRoute_advance_unary r ht

theorem check_g1_tagRescan_advance (t : G1Tag) (rest : List G1Frame) :
    g1AdvanceList .readBStart
        (.bof :: (List.replicate t.units .tag ++ .argSep :: rest)) =
      g1AdvanceList (g1RouteMode t) rest :=
  g1_tagRescan_advance t rest

theorem check_g1_tagRescan_validPath (t : G1Tag) (rest : List G1Frame)
    (hrest : G1ValidPath (g1RouteMode t) rest) :
    G1ValidPath .readBStart
      (.bof :: (List.replicate t.units .tag ++ .argSep :: rest)) :=
  g1_tagRescan_validPath t rest hrest

theorem check_g1TagRoute_advance (r : G1Request) :
    g1AdvanceList .readBStart (g1TagRouteFrames r) = g1RouteMode r.tag :=
  g1TagRoute_advance r

theorem check_g1TagRoute_validPath (r : G1Request) :
    G1ValidPath .readBStart (g1TagRouteFrames r) :=
  g1TagRoute_validPath r

theorem check_g1FieldRoute_advance_const (r : G1Request)
    (ht : r.tag = .const) (b : Bool)
    (harg : r.arg1 = if b then 1 else 0) :
    g1AdvanceList .readBStart (g1FieldRouteFrames r) = g1ConstMode b :=
  g1FieldRoute_advance_const r ht b harg

theorem check_g1FieldRoute_advance_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1AdvanceList .readBStart (g1FieldRouteFrames r) = .bScan :=
  g1FieldRoute_advance_binary r ht

theorem check_g1ReadBRoute_advance (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool) :
    g1AdvanceList .readBStart (g1ReadBRouteFrames r b) = g1StoreMode b :=
  g1ReadBRoute_advance r ht b

theorem check_g1ReadBRoute_validPath (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool) :
    G1ValidPath .readBStart (g1ReadBRouteFrames r b) :=
  g1ReadBRoute_validPath r ht b

theorem check_g1ReadBOOB_advance (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1AdvanceList .readBStart (g1ReadBOOBFrames r) = .bOOB :=
  g1ReadBOOB_advance r ht

theorem check_g1ReadBOOB_validPath (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    G1ValidPath .readBStart (g1ReadBOOBFrames r) :=
  g1ReadBOOB_validPath r ht

theorem check_g1_bScan_index_bridge (rest : List G1Frame) :
    g1AdvanceList .bScan (.index :: rest) =
      g1AdvanceList .bRoundStart rest :=
  g1_bScan_index_bridge rest

theorem check_g1_bRoundStart_stuck : G1Stuck .bRoundStart :=
  g1_bRoundStart_stuck

end Pnp3.Tests.TMGateOneRoutingSurface
