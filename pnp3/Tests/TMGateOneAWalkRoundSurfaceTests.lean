import Complexity.TMVerifier.TuringToolkit.GateOneAWalkRound

/-!
# S6 exact one-round operand-A walk surface (2026-08-30)

Definitions are checked only.  Every public S6 theorem has one exact named
wrapper; there are no anonymous examples or new proof facts here.
-/

namespace Pnp3.Tests.TMGateOneAWalkRoundSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

#check @g1AWalkSeekSteps
#check @g1AWalkRoundPrefixSteps
#check @g1AWalkRoundSteps
#check @g1AWalkRoundOOBSteps
#check @g1AWalkExhaustSteps
#check @g1AWalkOOBConfig
#check @g1AWalkExhaustConfig
#check @g1AWalkExhaustPre
#check @G1AWalkRoundExamples.reqNormal
#check @G1AWalkRoundExamples.reqOOB

theorem check_g1AWalkOOBConfig_tape (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).tape =
      g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits) :=
  g1AWalkOOBConfig_tape r b j hj1 hj v hv

theorem check_g1AWalkOOBConfig_head (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    ((g1AWalkOOBConfig r b j hj1 hj v hv).head : Nat) =
      4 * (g1AWalkCursor r j + 2) :=
  g1AWalkOOBConfig_head r b j hj1 hj v hv

theorem check_g1AWalkOOBConfig_state (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).state.snd =
      g1State .bOOB .p0 false false false (g1AWalkCtx r b v) :=
  g1AWalkOOBConfig_state r b j hj1 hj v hv

theorem check_g1AWalkOOBConfig_res (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).state.snd.ctx.res =
      g1Residual r.tag b := g1AWalkOOBConfig_res r b j hj1 hj v hv

theorem check_g1AWalkOOBConfig_vB (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).state.snd.ctx.vB = v :=
  g1AWalkOOBConfig_vB r b j hj1 hj v hv

theorem check_g1AWalkExhaustConfig_tape (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).tape =
      g1ListTape ((g1AWalkFrames r r.arg1).flatMap G1Frame.bits) :=
  g1AWalkExhaustConfig_tape r b v hj hv

theorem check_g1AWalkExhaustConfig_head (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    ((g1AWalkExhaustConfig r b v hj hv).head : Nat) =
      4 * (r.tag.units + 1) := g1AWalkExhaustConfig_head r b v hj hv

theorem check_g1AWalkExhaustConfig_state (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).state.snd =
      g1State .aExh .p0 false false false (g1AWalkCtx r b v) :=
  g1AWalkExhaustConfig_state r b v hj hv

theorem check_g1AWalkExhaustConfig_res (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).state.snd.ctx.res =
      g1Residual r.tag b := g1AWalkExhaustConfig_res r b v hj hv

theorem check_g1AWalkExhaustConfig_vB (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).state.snd.ctx.vB = v :=
  g1AWalkExhaustConfig_vB r b v hj hv

theorem check_g1CS_aWalk_round_prefix_exact (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) hj v hv)
        (g1AWalkRoundPrefixSteps r j) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1)) (by
          have h := g1AWalkCursor_safe r j hj
          omega)
        (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
        .aProbe .p0 false false false (g1AWalkCtx r b v) :=
  g1CS_aWalk_round_prefix_exact r b j hj1 hj v hv

theorem check_g1CS_aWalk_round_exact (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) (by omega) v hv)
        (g1AWalkRoundSteps r j) =
      g1AWalkConfig r b (j + 1) (by omega) hnext v' hv' :=
  g1CS_aWalk_round_exact r b j hj1 hnext v v' hv hv'

theorem check_g1CS_aWalk_round_oob_exact (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hlast : j + 1 = r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) (by omega) v hv)
        (g1AWalkRoundOOBSteps r j) =
      g1AWalkOOBConfig r b j hj1 (by omega) v hv :=
  g1CS_aWalk_round_oob_exact r b j hj1 hlast v hv

theorem check_g1AWalkExhaustPre_length (r : G1Request) :
    (g1AWalkExhaustPre r).length = r.tag.units + 1 :=
  g1AWalkExhaustPre_length r

theorem check_g1AWalkSplit_exhaust (r : G1Request) :
    g1AWalkExhaustPre r ++ G1Frame.argSep ::
        g1AWalkInnerRun r.arg1 ++ G1Frame.argSep ::
        g1AWalkOuterRun r r.arg1 ++
        G1Frame.cursor :: g1AWalkTail r r.arg1 =
      g1AWalkFrames r r.arg1 := g1AWalkSplit_exhaust r

theorem check_g1CS_aWalk_exhaust_exact (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
        (g1AWalkExhaustSteps r) =
      g1AWalkExhaustConfig r b v hj hv :=
  g1CS_aWalk_exhaust_exact r b v hj hv

theorem check_g1CS_aWalk_round_preservation (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    let out := TM.runConfig (M := G1M)
      (g1AWalkConfig r b j (by omega) (by omega) v hv)
      (g1AWalkRoundSteps r j)
    (g1AWalkConfig r b j (by omega) (by omega) v hv).state.snd.ctx.vB = v ∧
      out.tape = g1ListTape
        ((g1AWalkFrames r (j + 1)).flatMap G1Frame.bits) ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v' ∧
      (g1AWalkFrames r (j + 1)).count .cursor = 1 ∧
      (g1AWalkFrames r (j + 1)).count .spent = j + 1 ∧
      (g1AWalkFrames r (j + 1)).count .index =
        (r.arg1 - (j + 1)) + r.arg2 ∧
      (g1AWalkOperand1 r (j + 1)).count .index = r.arg1 - (j + 1) :=
  g1CS_aWalk_round_preservation r b j hj1 hnext v v' hv hv'

theorem check_g1CS_aWalk_round_oob_preservation (r : G1Request) (b : Bool)
    (j : Nat) (hj1 : j < r.arg1) (hlast : j + 1 = r.vals.length)
    (v : Bool) (hv : r.vals[j]? = some v) :
    let out := TM.runConfig (M := G1M)
      (g1AWalkConfig r b j (by omega) (by omega) v hv)
      (g1AWalkRoundOOBSteps r j)
    out.tape = g1ListTape
        ((g1AWalkFramesRestored r j).flatMap G1Frame.bits) ∧
      out.state.snd.mode = .bOOB ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v ∧
      (g1AWalkFramesRestored r j).count .cursor = 0 ∧
      (g1AWalkFramesRestored r j).count .spent = j + 1 ∧
      (g1AWalkFramesRestored r j).count .index =
        (r.arg1 - j - 1) + r.arg2 :=
  g1CS_aWalk_round_oob_preservation r b j hj1 hlast v hv

theorem check_g1AWalkRoundSteps_le_clock (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    g1AWalkRoundSteps r j ≤ g1Clock (encodeG1 r).length :=
  g1AWalkRoundSteps_le_clock r j hj1

theorem check_g1AWalkRoundOOBSteps_le_clock (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    g1AWalkRoundOOBSteps r j ≤ g1Clock (encodeG1 r).length :=
  g1AWalkRoundOOBSteps_le_clock r j hj1

theorem check_g1AWalkExhaustSteps_le_clock (r : G1Request) :
    g1AWalkExhaustSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AWalkExhaustSteps_le_clock r

theorem check_g1CS_readA_round_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (harg : 0 < r.arg1)
    (v v' : Bool) (rest : List Bool) (hvals : r.vals = v :: v' :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r + g1AWalkRoundSteps r 0) =
      g1AWalkConfig r false 1 (by omega) (by rw [hvals]; simp) v'
        (by rw [hvals]; simp) :=
  g1CS_readA_round_unary_exact r hc ht harg v v' rest hvals

theorem check_requests_canonical :
    G1AWalkRoundExamples.reqNormal.Canonical ∧
      G1AWalkRoundExamples.reqOOB.Canonical :=
  G1AWalkRoundExamples.requests_canonical

theorem check_normal_round_exact :
    TM.runConfig (M := G1M)
        (g1AWalkConfig G1AWalkRoundExamples.reqNormal false 0
          (by decide) (by decide) false (by decide)) 45 =
      g1AWalkConfig G1AWalkRoundExamples.reqNormal false 1
        (by decide) (by decide) true (by decide) :=
  G1AWalkRoundExamples.normal_round_exact

theorem check_normal_round_from_initial_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig
          (g1Point (encodeG1 G1AWalkRoundExamples.reqNormal))) 196 =
      g1AWalkConfig G1AWalkRoundExamples.reqNormal false 1
        (by decide) (by decide) true (by decide) :=
  G1AWalkRoundExamples.normal_round_from_initial_exact

theorem check_oob_round_exact :
    TM.runConfig (M := G1M)
        (g1AWalkConfig G1AWalkRoundExamples.reqOOB false 0
          (by decide) (by decide) false (by decide)) 40 =
      g1AWalkOOBConfig G1AWalkRoundExamples.reqOOB false 0
        (by decide) (by decide) false (by decide) :=
  G1AWalkRoundExamples.oob_round_exact

theorem check_exhaust_exact :
    TM.runConfig (M := G1M)
        (g1AWalkConfig G1AWalkRoundExamples.reqNormal false 1
          (by decide) (by decide) true (by decide)) 20 =
      g1AWalkExhaustConfig G1AWalkRoundExamples.reqNormal false true
        (by decide) (by decide) := G1AWalkRoundExamples.exhaust_exact

theorem check_literal_clock_bounds :
    45 ≤ g1Clock (encodeG1 G1AWalkRoundExamples.reqNormal).length ∧
      196 ≤ g1Clock (encodeG1 G1AWalkRoundExamples.reqNormal).length ∧
      40 ≤ g1Clock (encodeG1 G1AWalkRoundExamples.reqOOB).length ∧
      20 ≤ g1Clock (encodeG1 G1AWalkRoundExamples.reqNormal).length :=
  G1AWalkRoundExamples.literal_clock_bounds

end Pnp3.Tests.TMGateOneAWalkRoundSurface
