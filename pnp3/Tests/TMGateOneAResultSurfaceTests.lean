import Complexity.TMVerifier.TuringToolkit.GateOneAResult

/-!
# S9 five-tag gate-result exact surface (2026-08-30)

Definitions receive type checks only.  Every public theorem in
`GateOneAResult` has one exact named wrapper rooted directly in that theorem;
there are no anonymous examples.  The surface stops at stationary
`combineStart` and contains no output, accept/reject, or `TM.accepts` claim.
-/

namespace Pnp3.Tests.TMGateOneAResultSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

set_option maxRecDepth 4096

#check @g1AResultStartConfig
#check @g1ReadAResultConfig
#check @g1BACombineSteps
#check @g1UACombineSteps
#check @g1GateResultSteps
#check @G1AResultProbes.reqInputT
#check @G1AResultProbes.reqNotF
#check @G1AResultProbes.reqAndF
#check @G1AResultProbes.reqOrT
#check @G1AResultProbes.reqConstF
#check @G1AResultProbes.reqConstT

theorem check_g1CS_step_aRepairDone_result (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aRepairDone .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .aResultStart .p0 false false false ctx := by
  exact g1CS_step_aRepairDone_result n h hh tape ctx

theorem check_g1CS_step_aResultStart_apply (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aResultStart .p0 false false false ctx) 1 =
      g1AlignedConfig n h hh tape .readAStart .p0 false false false
        (g1ResultCtx (ctx.res.apply ctx.vB)) := by
  exact g1CS_step_aResultStart_apply n h hh tape ctx

theorem check_g1CS_aRepairDone_combine_exact (r : G1Request) (b v : Bool) :
    TM.runConfig (M := G1M) (g1ARepairDoneConfig r b v) 3 =
      g1CombineConfig r ((g1Residual r.tag b).apply v) := by
  exact g1CS_aRepairDone_combine_exact r b v

theorem check_g1BACombineSteps_eq (r : G1Request) :
    g1BACombineSteps r = g1ABinaryCursorSteps r +
      (8 * r.arg1 ^ 2 + (8 * r.arg2 + 70) * r.arg1 +
        4 * r.tag.units + 12 * r.arg2 + 60) := by
  exact g1BACombineSteps_eq r

theorem check_g1UACombineSteps_eq (r : G1Request) :
    g1UACombineSteps r = g1AUnaryCursorSteps r +
      (8 * r.arg1 ^ 2 + (8 * r.arg2 + 70) * r.arg1 +
        4 * r.tag.units + 12 * r.arg2 + 60) := by
  exact g1UACombineSteps_eq r

theorem check_g1GateResultSteps_const (r : G1Request)
    (ht : r.tag = .const) :
    g1GateResultSteps r = g1ConstActivatedSteps r := by
  exact g1GateResultSteps_const r ht

theorem check_g1GateResultSteps_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) :
    g1GateResultSteps r = g1BACombineSteps r := by
  exact g1GateResultSteps_binary r ht

theorem check_g1GateResultSteps_unary (r : G1Request)
    (ht : r.tag = .input ∨ r.tag = .not) :
    g1GateResultSteps r = g1UACombineSteps r := by
  exact g1GateResultSteps_unary r ht

theorem check_g1ResultSq_succ (N : Nat) :
    (N + 1) ^ 2 = N ^ 2 + (2 * N + 1) := by
  exact g1ResultSq_succ N

theorem check_g1ResultClock_quad (N : Nat) :
    g1Clock (4 * N) = 8192 * N ^ 2 + (4096 * N + 1024) := by
  exact g1ResultClock_quad N

theorem check_g1BACombineSteps_le_clock (r : G1Request) :
    g1BACombineSteps r ≤ g1Clock (encodeG1 r).length := by
  exact g1BACombineSteps_le_clock r

theorem check_g1UACombineSteps_le_clock (r : G1Request) :
    g1UACombineSteps r ≤ g1Clock (encodeG1 r).length := by
  exact g1UACombineSteps_le_clock r

theorem check_g1GateResultSteps_le_clock (r : G1Request) :
    g1GateResultSteps r ≤ g1Clock (encodeG1 r).length := by
  exact g1GateResultSteps_le_clock r

theorem check_g1CS_aCombine_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BACombineSteps r) =
      g1CombineConfig r ((g1Residual r.tag b).apply (v r.arg1)) := by
  exact g1CS_aCombine_binary_exact r hc ht b hb v hv rest hvals

theorem check_g1CS_aCombine_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (rest : List Bool) (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UACombineSteps r) =
      g1CombineConfig r ((g1Residual r.tag false).apply (v r.arg1)) := by
  exact g1CS_aCombine_unary_exact r hc ht v hv rest hvals

theorem check_g1Vals_prefix_witness {r : G1Request} {a : Bool}
    (ha : r.vals[r.arg1]? = some a) :
    ∃ v : Nat → Bool, (∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) ∧
      v r.arg1 = a ∧ ∃ rest : List Bool, r.vals = v 0 :: rest := by
  exact g1Vals_prefix_witness ha

theorem check_g1Spec_operands_binary {r : G1Request}
    (ht : r.tag = .and ∨ r.tag = .or) {res : Bool}
    (hs : r.spec = some res) :
    ∃ a b, r.vals[r.arg1]? = some a ∧ r.vals[r.arg2]? = some b := by
  exact g1Spec_operands_binary ht hs

theorem check_g1Spec_operand_unary {r : G1Request}
    (ht : r.tag = .input ∨ r.tag = .not) {res : Bool}
    (hs : r.spec = some res) : ∃ a, r.vals[r.arg1]? = some a := by
  exact g1Spec_operand_unary ht hs

theorem check_g1Spec_input_bridge {r : G1Request} (ht : r.tag = .input)
    {res : Bool} (hs : r.spec = some res) :
    r.vals[r.arg1]? = some res := by
  exact g1Spec_input_bridge ht hs

theorem check_g1Spec_not_bridge {r : G1Request} (ht : r.tag = .not)
    {res : Bool} (hs : r.spec = some res) :
    ∃ a, r.vals[r.arg1]? = some a ∧ res = !a := by
  exact g1Spec_not_bridge ht hs

theorem check_g1Spec_and_bridge {r : G1Request} (ht : r.tag = .and)
    {res : Bool} (hs : r.spec = some res) :
    ∃ a b, r.vals[r.arg1]? = some a ∧ r.vals[r.arg2]? = some b ∧
      res = (a && b) := by
  exact g1Spec_and_bridge ht hs

theorem check_g1Spec_or_bridge {r : G1Request} (ht : r.tag = .or)
    {res : Bool} (hs : r.spec = some res) :
    ∃ a b, r.vals[r.arg1]? = some a ∧ r.vals[r.arg2]? = some b ∧
      res = (a || b) := by
  exact g1Spec_or_bridge ht hs

theorem check_g1Spec_const_bridge {r : G1Request} (ht : r.tag = .const)
    {res : Bool} (hs : r.spec = some res) :
    (r.arg1 = 0 ∧ res = false) ∨ (r.arg1 = 1 ∧ res = true) := by
  exact g1Spec_const_bridge ht hs

theorem check_g1CS_gate_result_binary (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (res : Bool)
    (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BACombineSteps r) = g1CombineConfig r res := by
  exact g1CS_gate_result_binary r hc ht res hs

theorem check_g1CS_gate_result_unary (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (res : Bool)
    (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UACombineSteps r) = g1CombineConfig r res := by
  exact g1CS_gate_result_unary r hc ht res hs

theorem check_g1CS_gate_result_exact (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r) = g1CombineConfig r res := by
  exact g1CS_gate_result_exact r hc res hs

theorem check_g1CS_gate_result_ctx (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).state.snd.ctx = g1ResultCtx res := by
  exact g1CS_gate_result_ctx r hc res hs

theorem check_g1CS_gate_result_pass_vB (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r)).state.snd.ctx.pass = true ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r)).state.snd.ctx.vB = res := by
  exact g1CS_gate_result_pass_vB r hc res hs

theorem check_g1CS_gate_result_head (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).head : Nat) = 0 := by
  exact g1CS_gate_result_head r hc res hs

theorem check_g1CS_gate_result_state (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).state.snd = g1CombineState (g1ResultCtx res) := by
  exact g1CS_gate_result_state r hc res hs

theorem check_g1CS_gate_result_tape (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  exact g1CS_gate_result_tape r hc res hs

theorem check_g1CS_gate_result_stable (r : G1Request) (hc : r.Canonical)
    (res : Bool) (hs : r.spec = some res) (k : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r + k) = g1CombineConfig r res := by
  exact g1CS_gate_result_stable r hc res hs k

theorem check_g1Spec_none_of_arg1_oob (r : G1Request)
    (ht : r.tag ≠ .const) (hm : r.vals.length ≤ r.arg1) :
    r.spec = none := by
  exact g1Spec_none_of_arg1_oob r ht hm

theorem check_g1Spec_none_of_arg2_oob_binary (r : G1Request)
    (ht : r.tag = .and ∨ r.tag = .or) (hm : r.vals.length ≤ r.arg2) :
    r.spec = none := by
  exact g1Spec_none_of_arg2_oob_binary r ht hm

theorem check_g1CS_gate_result_or_spec_none (r : G1Request)
    (hc : r.Canonical) :
    (∃ res, r.spec = some res ∧
      TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1GateResultSteps r) = g1CombineConfig r res) ∨ r.spec = none := by
  exact g1CS_gate_result_or_spec_none r hc

theorem check_g1CombineState_ne_oob (res : Bool) (ctx : G1Ctx) :
    g1CombineState (g1ResultCtx res) ≠ g1OOBState ctx := by
  exact g1CombineState_ne_oob res ctx

theorem check_g1CS_gate_result_false_ne_oob (r : G1Request)
    (hc : r.Canonical) (hs : r.spec = some false) (ctx : G1Ctx) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1GateResultSteps r)).state.snd ≠ g1OOBState ctx := by
  exact g1CS_gate_result_false_ne_oob r hc hs ctx

theorem check_literal_canonical :
    G1AResultProbes.reqInputT.Canonical ∧
      G1AResultProbes.reqNotF.Canonical ∧
      G1AResultProbes.reqAndF.Canonical ∧
      G1AResultProbes.reqOrT.Canonical ∧
      G1AResultProbes.reqConstF.Canonical ∧
      G1AResultProbes.reqConstT.Canonical := by
  exact G1AResultProbes.literal_canonical

theorem check_literal_specs :
    G1AResultProbes.reqInputT.spec = some true ∧
      G1AResultProbes.reqNotF.spec = some false ∧
      G1AResultProbes.reqAndF.spec = some false ∧
      G1AResultProbes.reqOrT.spec = some true ∧
      G1AResultProbes.reqConstF.spec = some false ∧
      G1AResultProbes.reqConstT.spec = some true := by
  exact G1AResultProbes.literal_specs

theorem check_literal_steps :
    g1GateResultSteps G1AResultProbes.reqInputT = 195 ∧
      g1GateResultSteps G1AResultProbes.reqNotF = 243 ∧
      g1GateResultSteps G1AResultProbes.reqAndF = 430 ∧
      g1GateResultSteps G1AResultProbes.reqOrT = 454 ∧
      g1GateResultSteps G1AResultProbes.reqConstF = 117 ∧
      g1GateResultSteps G1AResultProbes.reqConstT = 133 := by
  exact G1AResultProbes.literal_steps

theorem check_literal_clocks :
    g1Clock (encodeG1 G1AResultProbes.reqInputT).length = 558080 ∧
      g1Clock (encodeG1 G1AResultProbes.reqNotF).length = 861184 ∧
      g1Clock (encodeG1 G1AResultProbes.reqAndF).length = 1438720 ∧
      g1Clock (encodeG1 G1AResultProbes.reqOrT).length = 1664000 ∧
      g1Clock (encodeG1 G1AResultProbes.reqConstF).length = 558080 ∧
      g1Clock (encodeG1 G1AResultProbes.reqConstT).length = 701440 := by
  exact G1AResultProbes.literal_clocks

theorem check_literal_results :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 G1AResultProbes.reqInputT))) 195 =
          g1CombineConfig G1AResultProbes.reqInputT true ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 G1AResultProbes.reqNotF))) 243 =
          g1CombineConfig G1AResultProbes.reqNotF false ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 G1AResultProbes.reqAndF))) 430 =
          g1CombineConfig G1AResultProbes.reqAndF false ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 G1AResultProbes.reqOrT))) 454 =
          g1CombineConfig G1AResultProbes.reqOrT true ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 G1AResultProbes.reqConstF))) 117 =
          g1CombineConfig G1AResultProbes.reqConstF false ∧
      TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 G1AResultProbes.reqConstT))) 133 =
          g1CombineConfig G1AResultProbes.reqConstT true := by
  exact G1AResultProbes.literal_results

end Pnp3.Tests.TMGateOneAResultSurface
