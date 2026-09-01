import Complexity.TMVerifier.TuringToolkit.GateOneRouteRewindTraceSafety

/-!
# GN-3B2fA unary/constant route-rewind trace safety surface (2026-09-01)

Definitions receive `#check` pins.  Every theorem has an explicit proposition
and is rooted directly in its named source theorem.  There are no inferred-type
wrappers or Lean `example` declarations.
-/

namespace Pnp3.Tests.TMGateOneRouteRewindTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1AResultProbes

#check @G1RunSafe
#check @g1AUnaryLeft
#check @g1AConstLeft
#check @g1UReadASteps
#check @g1ConstReadASteps
#check @g1UActivatedSteps
#check @g1ConstActivatedSteps
#check @g1ReadAConfig
#check @g1ReadAResultConfig
#check @g1ABofConfig
#check @g1CombineConfig
#check @reqInputT
#check @reqNotF
#check @reqConstF
#check @reqConstT

/-! ## Public canonical route lists -/

theorem check_g1AUnaryLeft_length (r : G1Request) :
    (g1AUnaryLeft r).length = r.tag.units + 1 :=
  g1AUnaryLeft_length r

theorem check_g1AConstLeft_length (r : G1Request) :
    (g1AConstLeft r).length = r.tag.units + r.arg1 + 2 :=
  g1AConstLeft_length r

theorem check_g1AUnaryLeft_skip (r : G1Request) :
    ∀ f ∈ g1AUnaryLeft r, G1RepairSkip f :=
  g1AUnaryLeft_skip r

theorem check_g1AConstLeft_skip (r : G1Request) :
    ∀ f ∈ g1AConstLeft r, G1RepairSkip f :=
  g1AConstLeft_skip r

theorem check_g1AUnaryLeft_split (r : G1Request) :
    [G1Frame.bof] ++ g1AUnaryLeft r ++ g1TagRouteRest r =
      encodeG1Frames r ++ [G1Frame.blank] :=
  g1AUnaryLeft_split r

theorem check_g1AConstLeft_split (r : G1Request) :
    [G1Frame.bof] ++ g1AConstLeft r ++ g1FieldRouteRest r =
      encodeG1Frames r ++ [G1Frame.blank] :=
  g1AConstLeft_split r

/-! ## Generic route and rewind safety -/

theorem check_g1CS_readB_forward_route_runSafe
    (r : G1Request) (hc : r.Canonical) (route suffix : List G1Frame)
    (hsplit : route ++ suffix = encodeG1Frames r ++ [G1Frame.blank])
    (hpath : G1ValidPath .readBStart route)
    (hroom : 4 * route.length < gnLocalSpan (encodeG1 r).length) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBHandoffSteps r + 4 * route.length) :=
  g1CS_readB_forward_route_runSafe r hc route suffix hsplit hpath hroom

theorem check_g1CS_route_rewind_runSafe
    (r : G1Request) (left tail : List G1Frame)
    (hleft : ∀ f ∈ left, G1RepairSkip f)
    (hsplit : [G1Frame.bof] ++ left ++ tail =
      encodeG1Frames r ++ [G1Frame.blank])
    (hroom : 4 * (1 + left.length) + 3 <
      gnLocalSpan (encodeG1 r).length) (ctx : G1Ctx) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length (4 * (1 + left.length)) (by
        apply lt_of_lt_of_le (b := gnLocalSpan (encodeG1 r).length)
        · omega
        · exact gnLocalSpan_le_g1_tapeLength (encodeG1 r).length)
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .readAResetStart .p0 false false false ctx)
      (4 * left.length + 6) :=
  g1CS_route_rewind_runSafe r left tail hleft hsplit hroom ctx

/-! ## Exact real-initial routes and activations -/

theorem check_g1CS_readA_unary_repaired_trace_safe
    (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UReadASteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1UReadASteps r) = g1ReadAConfig r false :=
  g1CS_readA_unary_repaired_trace_safe r hc ht

theorem check_g1CS_const_repaired_trace_safe
    (r : G1Request) (hc : r.Canonical) (ht : r.tag = .const)
    (b : Bool) (hs : r.spec = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstReadASteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ConstReadASteps r) = g1ReadAResultConfig r b :=
  g1CS_const_repaired_trace_safe r hc ht b hs

theorem check_g1CS_readA_unary_activate_runSafe (r : G1Request) :
    G1RunSafe (g1ReadAConfig r false) 1 :=
  g1CS_readA_unary_activate_runSafe r

theorem check_g1CS_readA_const_activate_runSafe
    (r : G1Request) (b : Bool) :
    G1RunSafe (g1ReadAResultConfig r b) 1 :=
  g1CS_readA_const_activate_runSafe r b

theorem check_g1CS_activate_unary_trace_safe
    (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UActivatedSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1UActivatedSteps r) = g1ABofConfig r false :=
  g1CS_activate_unary_trace_safe r hc ht

theorem check_g1CS_activate_const_trace_safe
    (r : G1Request) (hc : r.Canonical) (ht : r.tag = .const)
    (b : Bool) (hs : r.spec = some b) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstActivatedSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ConstActivatedSteps r) = g1CombineConfig r b :=
  g1CS_activate_const_trace_safe r hc ht b hs

/-! ## Literal schedules and safe endpoints -/

theorem check_literal_route_activation_steps :
    g1UReadASteps reqInputT = 99 ∧ g1UActivatedSteps reqInputT = 100 ∧
      g1UReadASteps reqNotF = 131 ∧ g1UActivatedSteps reqNotF = 132 ∧
      g1ConstReadASteps reqConstF = 116 ∧
        g1ConstActivatedSteps reqConstF = 117 ∧
      g1ConstReadASteps reqConstT = 132 ∧
        g1ConstActivatedSteps reqConstT = 133 :=
  G1RouteRewindTraceProbes.literal_route_activation_steps

theorem check_literal_input_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 99 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 99 =
        g1ReadAConfig reqInputT false) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 100 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 100 =
        g1ABofConfig reqInputT false) :=
  G1RouteRewindTraceProbes.literal_input_trace_safe

theorem check_literal_not_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 131 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 131 =
        g1ReadAConfig reqNotF false) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 132 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 132 =
        g1ABofConfig reqNotF false) :=
  G1RouteRewindTraceProbes.literal_not_trace_safe

theorem check_literal_const_false_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 116 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 116 =
        g1ReadAResultConfig reqConstF false) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 117 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstF))) 117 =
        g1CombineConfig reqConstF false) :=
  G1RouteRewindTraceProbes.literal_const_false_trace_safe

theorem check_literal_const_true_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 132 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 132 =
        g1ReadAResultConfig reqConstT true) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 133 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqConstT))) 133 =
        g1CombineConfig reqConstT true) :=
  G1RouteRewindTraceProbes.literal_const_true_trace_safe

end Pnp3.Tests.TMGateOneRouteRewindTraceSafetySurface
