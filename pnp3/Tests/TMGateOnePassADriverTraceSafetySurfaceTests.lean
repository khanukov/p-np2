import Complexity.TMVerifier.TuringToolkit.GateOnePassADriverTraceSafety

/-!
# GN-3B2e2 pass-A driver trace safety surface (2026-09-01)

Every source theorem has one explicit proposition wrapper rooted directly in
that theorem.  Definitions are pinned with `#check`; no inferred-type macros
or Lean `example` commands are used.
-/

namespace Pnp3.Tests.TMGateOnePassADriverTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

#check @g1AWalkDriverSteps
#check @g1AWalkExhaustSteps
#check @g1AWalkExhaustDriverSteps
#check @g1AWalkTerminalSteps
#check @g1AWalkRepairStartConfig
#check @g1ABinaryCursorSteps
#check @G1AWalkDriverExamples.reqDriver

theorem check_g1CS_aWalk_driver_runSafe (r : G1Request) (b : Bool) (m : Nat)
    (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    G1RunSafe
      (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
        (hv 0 (by omega))) (g1AWalkDriverSteps r m) :=
  g1CS_aWalk_driver_runSafe r b m hm1 hm v hv

theorem check_g1CS_aWalk_driver_trace_safe (r : G1Request) (b : Bool)
    (m : Nat) (hm1 : m ≤ r.arg1) (hm : m < r.vals.length)
    (v : Nat → Bool) (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    G1RunSafe
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega))) (g1AWalkDriverSteps r m) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
            (hv 0 (by omega))) (g1AWalkDriverSteps r m) =
        g1AWalkConfig r b m hm1 hm (v m) (hv m (Nat.le_refl _)) :=
  g1CS_aWalk_driver_trace_safe r b m hm1 hm v hv

theorem check_g1CS_aWalk_exhaust_runSafe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
      (g1AWalkExhaustSteps r) :=
  g1CS_aWalk_exhaust_runSafe r b v hj hv

theorem check_g1CS_aWalk_exhaust_trace_safe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe
        (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
        (g1AWalkExhaustSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
          (g1AWalkExhaustSteps r) = g1AWalkExhaustConfig r b v hj hv :=
  g1CS_aWalk_exhaust_trace_safe r b v hj hv

theorem check_g1CS_aWalk_exh_to_cursor_runSafe (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkExhaustConfig r b v hj hv)
      (8 * r.arg1 + 4 * r.arg2 + 16) :=
  g1CS_aWalk_exh_to_cursor_runSafe r b v hj hv

theorem check_g1CS_aWalk_terminal_turn_restore_runSafe (r : G1Request)
    (b v : Bool) (hj : r.arg1 < r.vals.length)
    (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r r.arg1 + 1)) (by
          have := g1AWalkCursor_safe r r.arg1 hj
          omega)
        (g1ListTape ((g1AWalkFrames r r.arg1).flatMap G1Frame.bits))
        .aTurnFin .p0 false false false (g1AWalkCtx r b v)) 8 :=
  g1CS_aWalk_terminal_turn_restore_runSafe r b v hj hv

theorem check_g1CS_aWalk_terminal_from_exhaust_trace_safe (r : G1Request)
    (b v : Bool) (hj : r.arg1 < r.vals.length)
    (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe (g1AWalkExhaustConfig r b v hj hv)
        (g1AWalkTerminalSteps r) ∧
      TM.runConfig (M := G1M) (g1AWalkExhaustConfig r b v hj hv)
          (g1AWalkTerminalSteps r) =
        g1AWalkRepairStartConfig r b v hj hv :=
  g1CS_aWalk_terminal_from_exhaust_trace_safe r b v hj hv

theorem check_g1CS_aWalk_exhaust_terminal_trace_safe (r : G1Request)
    (b v : Bool) (hj : r.arg1 < r.vals.length)
    (hv : r.vals[r.arg1]? = some v) :
    G1RunSafe
        (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
        (g1AWalkExhaustSteps r + g1AWalkTerminalSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
          (g1AWalkExhaustSteps r + g1AWalkTerminalSteps r) =
        g1AWalkRepairStartConfig r b v hj hv :=
  g1CS_aWalk_exhaust_terminal_trace_safe r b v hj hv

theorem check_g1CS_aWalk_exhaust_driver_trace_safe (r : G1Request)
    (b : Bool) (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    G1RunSafe
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega))) (g1AWalkExhaustDriverSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
            (hv 0 (by omega))) (g1AWalkExhaustDriverSteps r) =
        g1AWalkExhaustConfig r b (v r.arg1) hlen
          (hv r.arg1 (Nat.le_refl _)) :=
  g1CS_aWalk_exhaust_driver_trace_safe r b hlen v hv

theorem check_g1CS_aWalk_full_driver_trace_safe (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    G1RunSafe
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
            (hv 0 (by omega)))
          (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) =
        g1AWalkRepairStartConfig r b (v r.arg1) hlen
          (hv r.arg1 (Nat.le_refl _)) :=
  g1CS_aWalk_full_driver_trace_safe r b hlen v hv

theorem check_g1CS_readA_binary_full_driver_from_initial_trace_safe
    (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (bA bB : Bool) (rest : List Bool)
    (hB : r.vals[r.arg2]? = some bB) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (hvals : r.vals = bA :: rest) (hv0 : v 0 = bA) :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r +
          (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryCursorSteps r +
            (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r)) =
        g1AWalkRepairStartConfig r bB (v r.arg1) (by
          have h := hv r.arg1 (Nat.le_refl _)
          exact (List.getElem?_eq_some_iff.1 h).1)
          (hv r.arg1 (Nat.le_refl _)) :=
  g1CS_readA_binary_full_driver_from_initial_trace_safe r hc ht bA bB rest
    hB v hv hvals hv0

theorem check_g1AWalkDoneFrames_count_spent (r : G1Request) :
    (g1AWalkDoneFrames r).count .spent = r.arg1 :=
  g1AWalkDoneFrames_count_spent r

theorem check_g1AWalkDoneFrames_count_index (r : G1Request) :
    (g1AWalkDoneFrames r).count .index = r.arg2 :=
  g1AWalkDoneFrames_count_index r

set_option linter.unusedVariables false in
theorem check_g1CS_readA_binary_full_driver_structure (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (v : Nat → Bool) (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j))
    (hvals : r.vals = bA :: rest) (hv0 : v 0 = bA) :
    let hlen : r.arg1 < r.vals.length := by
      have h := hv r.arg1 (Nat.le_refl _)
      exact (List.getElem?_eq_some_iff.1 h).1
    let out := TM.runConfig (M := G1M)
      (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ABinaryCursorSteps r +
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r))
    out.tape = g1ListTape ((g1AWalkDoneFrames r).flatMap G1Frame.bits) ∧
      (out.head : Nat) = 4 * (g1AWalkCursor r r.arg1 + 1) ∧
      out.state.snd = g1State .aRepairStart .p0 false false false
        (g1AWalkCtx r bB (v r.arg1)) ∧
      out.state.snd.ctx = g1AWalkCtx r bB (v r.arg1) ∧
      out.state.snd.ctx.res = g1Residual r.tag bB ∧
      out.state.snd.ctx.vB = v r.arg1 ∧
      (g1AWalkDoneFrames r).count .cursor = 0 ∧
      (g1AWalkDoneFrames r).count .spent = r.arg1 ∧
      (g1AWalkDoneFrames r).count .index = r.arg2 ∧
      (g1AWalkOperand1 r r.arg1).count .spent = r.arg1 ∧
      (g1AWalkOperand1 r r.arg1).count .index = 0 ∧
      (g1AWalkOperand2 r).count .index = r.arg2 :=
  g1CS_readA_binary_full_driver_structure r hc ht bA bB rest hB v hv hvals hv0

theorem check_literal_two_round_trace_safe :
    G1RunSafe
        (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
          (by decide) (by decide) false (by decide)) 106 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
            (by decide) (by decide) false (by decide)) 106 =
        g1AWalkConfig G1AWalkDriverExamples.reqDriver false 2
          (by decide) (by decide) false (by decide) :=
  G1PassADriverTraceProbes.literal_two_round_trace_safe

theorem check_literal_exhaustion_trace_safe :
    G1RunSafe
        (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
          (by decide) (by decide) false (by decide)) 134 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
            (by decide) (by decide) false (by decide)) 134 =
        g1AWalkExhaustConfig G1AWalkDriverExamples.reqDriver false false
          (by decide) (by decide) :=
  G1PassADriverTraceProbes.literal_exhaustion_trace_safe

theorem check_literal_full_driver_trace_safe :
    G1RunSafe
        (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
          (by decide) (by decide) false (by decide)) 174 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
            (by decide) (by decide) false (by decide)) 174 =
        g1AWalkRepairStartConfig G1AWalkDriverExamples.reqDriver false false
          (by decide) (by decide) :=
  G1PassADriverTraceProbes.literal_full_driver_trace_safe

end Pnp3.Tests.TMGateOnePassADriverTraceSafetySurface
