import Complexity.TMVerifier.TuringToolkit.GateOnePassAEntryExamples

/-!
# G1 real-initial pass-A entry probes: surface tests

S1c import-side pins for every public definition and theorem in
`GateOnePassAEntryExamples`.  The ten request definitions retain direct
`#check`s, while the eighteen evidence theorems have named exact wrappers that
preserve their full exported propositions.

Deliberately absent: an operand-1 read or cursor, combine execution, output,
acceptance, advice changes, or new OOB/reject behavior.
-/

namespace Pnp3.Tests.TMGateOnePassAEntrySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1PassAEntryExamples

-- Every public request definition.
#check @reqInputFalse
#check @reqInputTrue
#check @reqNotFalse
#check @reqNotTrue
#check @reqAndFalse
#check @reqAndTrue
#check @reqOrFalse
#check @reqOrTrue
#check @reqConstFalse
#check @reqConstTrue

-- Every public evidence theorem, as a named exact wrapper.
theorem check_requests_canonical :
    reqInputFalse.Canonical ∧ reqInputTrue.Canonical ∧
      reqNotFalse.Canonical ∧ reqNotTrue.Canonical ∧
      reqAndFalse.Canonical ∧ reqAndTrue.Canonical ∧
      reqOrFalse.Canonical ∧ reqOrTrue.Canonical ∧
      reqConstFalse.Canonical ∧ reqConstTrue.Canonical := requests_canonical

theorem check_selected_literals :
    reqInputFalse.vals[reqInputFalse.arg1]? = some false ∧
      reqInputTrue.vals[reqInputTrue.arg1]? = some true ∧
      reqNotFalse.vals[reqNotFalse.arg1]? = some false ∧
      reqNotTrue.vals[reqNotTrue.arg1]? = some true ∧
      reqAndFalse.vals[reqAndFalse.arg2]? = some false ∧
      reqAndTrue.vals[reqAndTrue.arg2]? = some true ∧
      reqOrFalse.vals[reqOrFalse.arg2]? = some false ∧
      reqOrTrue.vals[reqOrTrue.arg2]? = some true ∧
      reqConstFalse.spec = some false ∧ reqConstTrue.spec = some true := selected_literals

theorem check_probe_extents :
    ((encodeG1 reqInputFalse).length = 32 ∧
        ((encodeG1Frames reqInputFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 36 ∧
        G1M.tapeLength (encodeG1 reqInputFalse).length = 558113) ∧
      ((encodeG1 reqInputTrue).length = 32 ∧
        ((encodeG1Frames reqInputTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 36 ∧
        G1M.tapeLength (encodeG1 reqInputTrue).length = 558113) ∧
      ((encodeG1 reqNotFalse).length = 40 ∧
        ((encodeG1Frames reqNotFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 44 ∧
        G1M.tapeLength (encodeG1 reqNotFalse).length = 861225) ∧
      ((encodeG1 reqNotTrue).length = 40 ∧
        ((encodeG1Frames reqNotTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 44 ∧
        G1M.tapeLength (encodeG1 reqNotTrue).length = 861225) ∧
      ((encodeG1 reqAndFalse).length = 44 ∧
        ((encodeG1Frames reqAndFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 48 ∧
        G1M.tapeLength (encodeG1 reqAndFalse).length = 1037357) ∧
      ((encodeG1 reqAndTrue).length = 44 ∧
        ((encodeG1Frames reqAndTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 48 ∧
        G1M.tapeLength (encodeG1 reqAndTrue).length = 1037357) ∧
      ((encodeG1 reqOrFalse).length = 48 ∧
        ((encodeG1Frames reqOrFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 52 ∧
        G1M.tapeLength (encodeG1 reqOrFalse).length = 1229873) ∧
      ((encodeG1 reqOrTrue).length = 48 ∧
        ((encodeG1Frames reqOrTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 52 ∧
        G1M.tapeLength (encodeG1 reqOrTrue).length = 1229873) ∧
      ((encodeG1 reqConstFalse).length = 32 ∧
        ((encodeG1Frames reqConstFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 36 ∧
        G1M.tapeLength (encodeG1 reqConstFalse).length = 558113) ∧
      ((encodeG1 reqConstTrue).length = 36 ∧
        ((encodeG1Frames reqConstTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 40 ∧
        G1M.tapeLength (encodeG1 reqConstTrue).length = 701477) := probe_extents

theorem check_input_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113 =
      g1AInstallConfig reqInputFalse false := input_false_install

theorem check_input_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113 =
      g1AInstallConfig reqInputTrue false := input_true_install

theorem check_not_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153 =
      g1AInstallConfig reqNotFalse false := not_false_install

theorem check_not_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153 =
      g1AInstallConfig reqNotTrue false := not_true_install

theorem check_and_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198 =
      g1AInstallConfig reqAndFalse false := and_false_install

theorem check_and_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198 =
      g1AInstallConfig reqAndTrue true := and_true_install

theorem check_or_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218 =
      g1AInstallConfig reqOrFalse false := or_false_install

theorem check_or_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218 =
      g1AInstallConfig reqOrTrue true := or_true_install

theorem check_const_false_result :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117 =
      g1CombineConfig reqConstFalse false := const_false_result

theorem check_const_true_result :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133 =
      g1CombineConfig reqConstTrue true := const_true_result

theorem check_endpoint_heads :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113).head : Nat) = 12 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113).head : Nat) = 12 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153).head : Nat) = 20 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153).head : Nat) = 20 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).head : Nat) = 24 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198).head : Nat) = 24 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218).head : Nat) = 28 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218).head : Nat) = 28 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117).head : Nat) = 0 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133).head : Nat) = 0 :=
  endpoint_heads

theorem check_endpoint_states :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .notA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .notA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd =
          g1AInstallState (g1ResultCtx false) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198).state.snd =
          g1AInstallState ((g1Ctx0.withVB true).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218).state.snd =
          g1AInstallState ((g1Ctx0.withVB true).withRes .constTrue) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117).state.snd =
          g1CombineState (g1ResultCtx false) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133).state.snd =
          g1CombineState (g1ResultCtx true) := endpoint_states

theorem check_endpoint_tapes :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))).tape := endpoint_tapes

theorem check_and_false_no_wrong_result :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd.ctx =
          g1ResultCtx false ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd.mode =
          .aInstallStart ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd.mode ≠
          .combineStart := and_false_no_wrong_result

theorem check_probe_clocks :
    113 ≤ g1Clock (encodeG1 reqInputFalse).length ∧
      113 ≤ g1Clock (encodeG1 reqInputTrue).length ∧
      153 ≤ g1Clock (encodeG1 reqNotFalse).length ∧
      153 ≤ g1Clock (encodeG1 reqNotTrue).length ∧
      198 ≤ g1Clock (encodeG1 reqAndFalse).length ∧
      198 ≤ g1Clock (encodeG1 reqAndTrue).length ∧
      218 ≤ g1Clock (encodeG1 reqOrFalse).length ∧
      218 ≤ g1Clock (encodeG1 reqOrTrue).length ∧
      117 ≤ g1Clock (encodeG1 reqConstFalse).length ∧
      133 ≤ g1Clock (encodeG1 reqConstTrue).length := probe_clocks

end Pnp3.Tests.TMGateOnePassAEntrySurface
