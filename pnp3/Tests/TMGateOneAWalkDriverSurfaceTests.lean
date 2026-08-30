import Complexity.TMVerifier.TuringToolkit.GateOneAWalkDriver

/-!
# S7 exact operand-A driver surface (2026-08-30)

Definitions are checked only.  Every public S7 theorem has one exact named
wrapper; this file introduces no anonymous examples or new proof facts.
-/

namespace Pnp3.Tests.TMGateOneAWalkDriverSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

#check @g1AWalkDriverSteps
#check @g1AWalkDriverPoly
#check @g1AWalkExhaustDriverSteps
#check @g1AWalkDoneFrames
#check @g1AWalkTerminalSteps
#check @g1AWalkRepairStartConfig
#check @G1AWalkDriverExamples.reqDriver
#check @G1AWalkDriverExamples.reqZero

theorem check_g1AWalkDriverSteps_zero (r : G1Request) :
    g1AWalkDriverSteps r 0 = 0 := g1AWalkDriverSteps_zero r

theorem check_g1AWalkDriverSteps_succ (r : G1Request) (m : Nat) :
    g1AWalkDriverSteps r (m + 1) =
      g1AWalkDriverSteps r m + g1AWalkRoundSteps r m :=
  g1AWalkDriverSteps_succ r m

theorem check_g1AWalkDriverSteps_eq_sum (r : G1Request) (m : Nat) :
    g1AWalkDriverSteps r m =
      ((List.range m).map (fun j => 16 * j + 8 * r.arg2 + 45)).sum :=
  g1AWalkDriverSteps_eq_sum r m

theorem check_g1CS_aWalk_driver_exact (r : G1Request) (b : Bool) (m : Nat)
    (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega))) (g1AWalkDriverSteps r m) =
      g1AWalkConfig r b m hm1 hm (v m) (hv m (Nat.le_refl _)) :=
  g1CS_aWalk_driver_exact r b m hm1 hm v hv

theorem check_g1CS_aWalk_driver_preservation (r : G1Request) (b : Bool)
    (m : Nat) (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    let out := TM.runConfig (M := G1M)
      (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
        (hv 0 (by omega))) (g1AWalkDriverSteps r m)
    out.tape = g1ListTape ((g1AWalkFrames r m).flatMap G1Frame.bits) ∧
      (out.head : Nat) = 4 * g1AWalkCursor r m - 1 ∧
      out.state.snd =
        g1State .aSeekOut .p3 false false false (g1AWalkCtx r b (v m)) ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v m ∧
      (g1AWalkFrames r m).count .cursor = 1 ∧
      (g1AWalkFrames r m).count .spent = m ∧
      (g1AWalkFrames r m).count .index = (r.arg1 - m) + r.arg2 ∧
      (g1AWalkOperand1 r m).count .index = r.arg1 - m :=
  g1CS_aWalk_driver_preservation r b m hm1 hm v hv

theorem check_g1CS_readA_driver_unary_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not) (m : Nat)
    (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) (rest : List Bool)
    (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r + g1AWalkDriverSteps r m) =
      g1AWalkConfig r false m hm1 hm (v m) (hv m (Nat.le_refl _)) :=
  g1CS_readA_driver_unary_exact r hc ht m hm1 hm v hv rest hvals

theorem check_g1CS_readA_driver_binary_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (bB : Bool)
    (hB : r.vals[r.arg2]? = some bB) (m : Nat) (hm1 : m ≤ r.arg1)
    (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) (rest : List Bool)
    (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r + g1AWalkDriverSteps r m) =
      g1AWalkConfig r bB m hm1 hm (v m) (hv m (Nat.le_refl _)) :=
  g1CS_readA_driver_binary_exact r hc ht bB hB m hm1 hm v hv rest hvals

theorem check_g1AWalkDriverSteps_le_poly (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) : g1AWalkDriverSteps r m ≤ g1AWalkDriverPoly r :=
  g1AWalkDriverSteps_le_poly r m hm1

theorem check_g1AWalkDriverPoly_le_clock (r : G1Request) :
    g1AWalkDriverPoly r ≤ g1Clock (encodeG1 r).length :=
  g1AWalkDriverPoly_le_clock r

theorem check_g1AWalkDriverSteps_le_clock (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) :
    g1AWalkDriverSteps r m ≤ g1Clock (encodeG1 r).length :=
  g1AWalkDriverSteps_le_clock r m hm1

theorem check_g1AUnaryDriverSteps_le_clock (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) :
    g1AUnaryCursorSteps r + g1AWalkDriverSteps r m ≤
      g1Clock (encodeG1 r).length :=
  g1AUnaryDriverSteps_le_clock r m hm1

theorem check_g1ABinaryDriverSteps_le_clock (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) :
    g1ABinaryCursorSteps r + g1AWalkDriverSteps r m ≤
      g1Clock (encodeG1 r).length :=
  g1ABinaryDriverSteps_le_clock r m hm1

theorem check_g1CS_aWalk_exhaust_driver_exact (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _)
          (by omega) (v 0) (hv 0 (by omega)))
        (g1AWalkExhaustDriverSteps r) =
      g1AWalkExhaustConfig r b (v r.arg1) hlen
        (hv r.arg1 (Nat.le_refl _)) :=
  g1CS_aWalk_exhaust_driver_exact r b hlen v hv

theorem check_g1CS_aWalk_oob_driver_exact (r : G1Request) (b : Bool)
    (t : Nat) (ht1 : t < r.arg1) (hlast : t + 1 = r.vals.length)
    (v : Nat → Bool) (hv : ∀ j, j ≤ t → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t) =
      g1AWalkOOBConfig r b t ht1 (by omega) (v t)
        (hv t (Nat.le_refl _)) :=
  g1CS_aWalk_oob_driver_exact r b t ht1 hlast v hv

theorem check_g1AWalkExhaustDriverSteps_le_clock (r : G1Request) :
    g1AWalkExhaustDriverSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AWalkExhaustDriverSteps_le_clock r

theorem check_g1AWalkFullDriverSteps_le_clock (r : G1Request) :
    g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r ≤
      g1Clock (encodeG1 r).length :=
  g1AWalkFullDriverSteps_le_clock r

theorem check_g1AWalkRepairStartConfig_tape (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).tape =
      g1ListTape ((g1AWalkDoneFrames r).flatMap G1Frame.bits) :=
  g1AWalkRepairStartConfig_tape r b v hj hv

theorem check_g1AWalkRepairStartConfig_head (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    ((g1AWalkRepairStartConfig r b v hj hv).head : Nat) =
      4 * (g1AWalkCursor r r.arg1 + 1) :=
  g1AWalkRepairStartConfig_head r b v hj hv

theorem check_g1AWalkRepairStartConfig_state (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).state.snd =
      g1State .aRepairStart .p0 false false false (g1AWalkCtx r b v) :=
  g1AWalkRepairStartConfig_state r b v hj hv

theorem check_g1AWalkRepairStartConfig_res (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).state.snd.ctx.res =
      g1Residual r.tag b := g1AWalkRepairStartConfig_res r b v hj hv

theorem check_g1AWalkRepairStartConfig_vB (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).state.snd.ctx.vB = v :=
  g1AWalkRepairStartConfig_vB r b v hj hv

theorem check_g1AWalkSplit_done (r : G1Request) (v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    g1AWalkExhaustPre r ++ G1Frame.argSep ::
        g1AWalkFwdRun r r.arg1 ++ G1Frame.data v :: g1AWalkTail r r.arg1 =
      g1AWalkDoneFrames r := g1AWalkSplit_done r v hj hv

theorem check_g1AWalkSplit_exhaust_fwd (r : G1Request) :
    g1AWalkExhaustPre r ++ G1Frame.argSep ::
        g1AWalkFwdRun r r.arg1 ++ G1Frame.cursor :: g1AWalkTail r r.arg1 =
      g1AWalkFrames r r.arg1 := g1AWalkSplit_exhaust_fwd r

theorem check_g1AWalkDoneFrames_count_cursor (r : G1Request) :
    (g1AWalkDoneFrames r).count .cursor = 0 :=
  g1AWalkDoneFrames_count_cursor r

theorem check_g1CS_aWalk_terminal_from_exhaust_exact (r : G1Request)
    (b v : Bool) (hj : r.arg1 < r.vals.length)
    (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M) (g1AWalkExhaustConfig r b v hj hv)
        (g1AWalkTerminalSteps r) =
      g1AWalkRepairStartConfig r b v hj hv :=
  g1CS_aWalk_terminal_from_exhaust_exact r b v hj hv

theorem check_g1CS_aWalk_full_driver_exact (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _)
          (by omega) (v 0) (hv 0 (by omega)))
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) =
      g1AWalkRepairStartConfig r b (v r.arg1) hlen
        (hv r.arg1 (Nat.le_refl _)) :=
  g1CS_aWalk_full_driver_exact r b hlen v hv

theorem check_requests_canonical :
    G1AWalkDriverExamples.reqDriver.Canonical ∧
      G1AWalkDriverExamples.reqZero.Canonical :=
  G1AWalkDriverExamples.requests_canonical

theorem check_zero_round_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
        (by decide) (by decide) false (by decide)) 0 =
    g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
      (by decide) (by decide) false (by decide) :=
  G1AWalkDriverExamples.zero_round_exact

theorem check_one_round_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
        (by decide) (by decide) false (by decide)) 45 =
    g1AWalkConfig G1AWalkDriverExamples.reqDriver false 1
      (by decide) (by decide) true (by decide) :=
  G1AWalkDriverExamples.one_round_exact

theorem check_two_round_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
        (by decide) (by decide) false (by decide)) 106 =
    g1AWalkConfig G1AWalkDriverExamples.reqDriver false 2
      (by decide) (by decide) false (by decide) :=
  G1AWalkDriverExamples.two_round_exact

theorem check_exhaustion_driver_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig G1AWalkDriverExamples.reqDriver false 0
        (by decide) (by decide) false (by decide)) 134 =
    g1AWalkExhaustConfig G1AWalkDriverExamples.reqDriver false false
      (by decide) (by decide) :=
  G1AWalkDriverExamples.exhaustion_driver_exact

theorem check_zero_operand_exhaustion_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig G1AWalkDriverExamples.reqZero false 0
        (by decide) (by decide) true (by decide)) 12 =
    g1AWalkExhaustConfig G1AWalkDriverExamples.reqZero false true
      (by decide) (by decide) :=
  G1AWalkDriverExamples.zero_operand_exhaustion_exact

theorem check_two_round_from_initial_exact :
    TM.runConfig (M := G1M)
      (G1M.initialConfig
        (g1Point (encodeG1 G1AWalkDriverExamples.reqDriver)))
      277 =
    g1AWalkConfig G1AWalkDriverExamples.reqDriver false 2
      (by decide) (by decide) false (by decide) :=
  G1AWalkDriverExamples.two_round_from_initial_exact

end Pnp3.Tests.TMGateOneAWalkDriverSurface
