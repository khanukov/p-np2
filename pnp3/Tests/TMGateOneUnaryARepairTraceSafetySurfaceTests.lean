import Complexity.TMVerifier.TuringToolkit.GateOneUnaryARepairTraceSafety

/-!
# GN-3B2fB unary pass-A install/driver/repair safety surface (2026-09-01)

Definitions receive `#check` pins.  Every theorem has an explicit proposition
and is rooted directly in its named source theorem.  There are no inferred-type
wrappers or Lean `example` declarations.
-/

namespace Pnp3.Tests.TMGateOneUnaryARepairTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1AResultProbes

#check @g1AReadInstallSteps
#check @g1AUnaryCursorSteps
#check @g1AWalkExhaustDriverSteps
#check @g1AWalkTerminalSteps
#check @g1ARepairLiveSteps
#check @g1AUnaryRepairSteps
#check @g1ABofConfig
#check @g1AWalkConfig
#check @g1AWalkRepairStartConfig
#check @g1ARepairDoneConfig
#check @reqInputT
#check @reqNotF

theorem check_g1CS_aBof_install_runSafe (r : G1Request)
    (htag : r.tag ≠ .const) (bA bB : Bool) (rest : List Bool)
    (hv : r.vals = bA :: rest) :
    G1RunSafe (g1ABofConfig r bB)
      ((4 * (r.tag.units + 2) + 1) + g1ALiveInstallSteps r) :=
  g1CS_aBof_install_runSafe r htag bA bB rest hv

theorem check_g1CS_readA_unary_install_from_initial_trace_safe
    (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (bA : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1AUnaryCursorSteps r) =
        g1AWalkConfig r false 0 (Nat.zero_le _) (by rw [hv]; simp) bA
          (by rw [hv]; simp) :=
  g1CS_readA_unary_install_from_initial_trace_safe r hc ht bA rest hv

theorem check_g1AUnaryRepairSteps_trace_eq (r : G1Request) :
    g1AUnaryRepairSteps r =
      (g1AUnaryCursorSteps r +
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) +
      g1ARepairLiveSteps r :=
  g1AUnaryRepairSteps_trace_eq r

theorem check_g1CS_aRepair_unary_initial_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryRepairSteps r) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1AUnaryRepairSteps r) =
        g1ARepairDoneConfig r false (v r.arg1) :=
  g1CS_aRepair_unary_initial_trace_safe r hc ht v hv rest hvals

theorem check_g1CS_aRepair_unary_spec_trace_safe (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (res : Bool) (hs : r.spec = some res) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryRepairSteps r) ∧
      ∃ selectedA : Bool,
        TM.runConfig (M := G1M)
            (G1M.initialConfig (g1Point (encodeG1 r)))
            (g1AUnaryRepairSteps r) =
          g1ARepairDoneConfig r false selectedA ∧
        (g1Residual r.tag false).apply selectedA = res :=
  g1CS_aRepair_unary_spec_trace_safe r hc ht res hs

theorem check_literal_steps :
    g1AUnaryCursorSteps reqInputT = 131 ∧
      g1AUnaryRepairSteps reqInputT = 192 ∧
      g1AUnaryCursorSteps reqNotF = 171 ∧
      g1AUnaryRepairSteps reqNotF = 240 :=
  G1UnaryARepairTraceProbes.literal_steps

theorem check_literal_input_install_repair_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 131 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 131 =
        g1AWalkConfig reqInputT false 0 (by decide) (by decide) true
          (by decide)) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 192 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqInputT))) 192 =
        g1ARepairDoneConfig reqInputT false true) :=
  G1UnaryARepairTraceProbes.literal_input_install_repair_trace_safe

theorem check_literal_not_install_repair_trace_safe :
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 171 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 171 =
        g1AWalkConfig reqNotF false 0 (by decide) (by decide) true
          (by decide)) ∧
    (G1RunSafe (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 240 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 reqNotF))) 240 =
        g1ARepairDoneConfig reqNotF false true) :=
  G1UnaryARepairTraceProbes.literal_not_install_repair_trace_safe

end Pnp3.Tests.TMGateOneUnaryARepairTraceSafetySurface
