import Complexity.TMVerifier.TuringToolkit.GateOneAcceptsClosureExamples

/-! # S11 G1 acceptance-closure surface (2026-09-19)

Definitions receive `#check` only.  Every public S11 theorem, in both the
toolkit module and the literal probe module, has one named, exactly stated
wrapper rooted directly in that theorem: a bare `#check @name` pins only the
name, so a silently restated signature would not be caught by it.

The two frozen endpoints are `check_g1CS_accepts_eq_isSome` and
`check_g1CS_accepts_iff_wellFormed`; the two nonacceptance classes are
`check_g1CS_noncanonical_not_accepts` and
`check_g1CS_canonical_none_not_accepts`.
-/

namespace Pnp3.Tests.TMGateOneAcceptsClosureSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1AResultProbes
open Pnp3.Internal.PsubsetPpoly.TM.G1AcceptsClosureProbes

/-! ## Named surfaces -/

#check @g1_validate_le_clock
#check @g1CS_pad_to_clock
#check @g1State_ne_accept_of_mode
#check @g1RejectState_ne_accept
#check @g1OOBState_ne_accept
#check @g1OOBState_ne_reject
#check @g1CS_stepConfig_reject_state
#check @g1CS_runConfig_reject_state
#check @g1CS_run_eq_runConfig
#check @g1CS_state_eq_accept_iff
#check @g1CS_accepts_iff_state
#check @g1CS_not_accepts_of_state
#check @g1_canonical_of_spec_some
#check @g1CS_accepts_true_of_spec_some
#check @g1CS_noncanonical_clock_reject
#check @g1CS_noncanonical_run_reject
#check @g1CS_noncanonical_not_accepts
#check @g1_operandsInBounds_const
#check @g1_operandsInBounds_unary
#check @g1_operandsInBounds_binary
#check @g1_operands_oob_of_canonical_none
#check @g1_spec_ne_none_of_canonical_const
#check @g1AWalkOOBRoute_le_driver
#check @g1AUnaryWalkOOBSteps_le_clock
#check @g1ABinaryWalkOOBSteps_le_clock
#check @g1ValsWitness
#check @g1ValsWitness_spec
#check @g1ValsWitness_zero
#check @g1CS_canonical_none_clock_oob_unary
#check @g1CS_canonical_none_clock_oob_binary
#check @g1CS_canonical_none_clock_oob
#check @g1CS_canonical_none_run_oob
#check @g1CS_canonical_none_not_accepts
#check @g1CS_none_not_accepts
#check @g1CS_accepts_eq_isSome
#check @g1CS_accepts_iff_spec_isSome
#check @g1CS_accepts_iff_wellFormed
#check @g1CS_accepts_eq_decide_wellFormed
#check @g1CS_not_accepts_iff_spec_none

#check @reqNonCanonInput
#check @reqNonCanonConst
#check @reqArg1OOBWalk
#check @reqArg1OOBEmpty
#check @reqArg1OOBBinary
#check @reqArg2OOBZero
#check @reqArg2OOBPositive

/-! ## Clock padding and the literal sinks -/

theorem check_g1_validate_le_clock (n : Nat) : n + 4 ≤ g1Clock n :=
  g1_validate_le_clock n

theorem check_g1CS_pad_to_clock {r : G1Request} {steps : Nat}
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (hle : steps ≤ g1Clock (encodeG1 r).length)
    (h : ∀ k, TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (steps + k) = c) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length) = c :=
  g1CS_pad_to_clock hle h

theorem check_g1State_ne_accept_of_mode {q : G1State} (h : q.mode ≠ .accept) :
    q ≠ g1AcceptState :=
  g1State_ne_accept_of_mode h

theorem check_g1RejectState_ne_accept : g1RejectState ≠ g1AcceptState :=
  g1RejectState_ne_accept

theorem check_g1OOBState_ne_accept (ctx : G1Ctx) :
    g1OOBState ctx ≠ g1AcceptState :=
  g1OOBState_ne_accept ctx

theorem check_g1OOBState_ne_reject (ctx : G1Ctx) :
    g1OOBState ctx ≠ g1RejectState :=
  g1OOBState_ne_reject ctx

/-! ## Reject absorption -/

theorem check_g1CS_stepConfig_reject_state {n : Nat}
    (c : Configuration (M := G1M) n) (h : c.state.snd = g1RejectState) :
    (TM.stepConfig (M := G1M) c).state.snd = g1RejectState :=
  g1CS_stepConfig_reject_state c h

theorem check_g1CS_runConfig_reject_state {n : Nat}
    (c : Configuration (M := G1M) n) (h : c.state.snd = g1RejectState)
    (k : Nat) :
    (TM.runConfig (M := G1M) c k).state.snd = g1RejectState :=
  g1CS_runConfig_reject_state c h k

/-! ## From the clock to `TM.accepts` -/

theorem check_g1CS_run_eq_runConfig {n : Nat} (x : Boolcube.Point n) :
    TM.run (M := G1M) (n := n) x =
      TM.runConfig (M := G1M) (G1M.initialConfig x) (g1Clock n) :=
  g1CS_run_eq_runConfig x

theorem check_g1CS_state_eq_accept_iff {n : Nat}
    (c : Configuration (M := G1M) n) :
    c.state = G1M.accept ↔ c.state.snd = g1AcceptState :=
  g1CS_state_eq_accept_iff c

theorem check_g1CS_accepts_iff_state {n : Nat} (x : Boolcube.Point n) :
    TM.accepts (M := G1M) n x = true ↔
      (TM.runConfig (M := G1M) (G1M.initialConfig x)
        (g1Clock n)).state.snd = g1AcceptState :=
  g1CS_accepts_iff_state x

theorem check_g1CS_not_accepts_of_state {n : Nat} (x : Boolcube.Point n)
    (h : (TM.runConfig (M := G1M) (G1M.initialConfig x)
      (g1Clock n)).state.snd ≠ g1AcceptState) :
    TM.accepts (M := G1M) n x = false :=
  g1CS_not_accepts_of_state x h

/-! ## A defined result accepts -/

theorem check_g1_canonical_of_spec_some {r : G1Request} {res : Bool}
    (hs : r.spec = some res) : r.Canonical :=
  g1_canonical_of_spec_some hs

theorem check_g1CS_accepts_true_of_spec_some (r : G1Request) (res : Bool)
    (hs : r.spec = some res) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true :=
  g1CS_accepts_true_of_spec_some r res hs

/-! ## The noncanonical class -/

theorem check_g1CS_noncanonical_clock_reject (r : G1Request)
    (hnc : ¬ r.Canonical) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1RejectState :=
  g1CS_noncanonical_clock_reject r hnc

theorem check_g1CS_noncanonical_run_reject (r : G1Request)
    (hnc : ¬ r.Canonical) :
    (TM.run (M := G1M) (g1Point (encodeG1 r))).state.snd = g1RejectState :=
  g1CS_noncanonical_run_reject r hnc

theorem check_g1CS_noncanonical_not_accepts (r : G1Request)
    (hnc : ¬ r.Canonical) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false :=
  g1CS_noncanonical_not_accepts r hnc

/-! ## Operand-domain projections -/

theorem check_g1_operandsInBounds_const {r : G1Request} (ht : r.tag = .const) :
    r.operandsInBounds :=
  g1_operandsInBounds_const ht

theorem check_g1_operandsInBounds_unary {r : G1Request}
    (ht : r.tag = .input ∨ r.tag = .not) :
    r.operandsInBounds ↔ r.arg1 < r.vals.length :=
  g1_operandsInBounds_unary ht

theorem check_g1_operandsInBounds_binary {r : G1Request}
    (ht : r.tag = .and ∨ r.tag = .or) :
    r.operandsInBounds ↔ (r.arg1 < r.vals.length ∧ r.arg2 < r.vals.length) :=
  g1_operandsInBounds_binary ht

theorem check_g1_operands_oob_of_canonical_none (r : G1Request)
    (hc : r.Canonical) (hs : r.spec = none) : ¬ r.operandsInBounds :=
  g1_operands_oob_of_canonical_none r hc hs

theorem check_g1_spec_ne_none_of_canonical_const (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .const) : r.spec ≠ none :=
  g1_spec_ne_none_of_canonical_const r hc ht

/-! ## The operand-1 walk fits the unchanged clock -/

theorem check_g1AWalkOOBRoute_le_driver (r : G1Request) (t : Nat) :
    g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t ≤
      g1AWalkDriverSteps r (t + 1) :=
  g1AWalkOOBRoute_le_driver r t

theorem check_g1AUnaryWalkOOBSteps_le_clock (r : G1Request) (t : Nat)
    (ht1 : t < r.arg1) :
    g1AUnaryCursorSteps r +
        (g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t) ≤
      g1Clock (encodeG1 r).length :=
  g1AUnaryWalkOOBSteps_le_clock r t ht1

theorem check_g1ABinaryWalkOOBSteps_le_clock (r : G1Request) (t : Nat)
    (ht1 : t < r.arg1) :
    g1ABinaryCursorSteps r +
        (g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t) ≤
      g1Clock (encodeG1 r).length :=
  g1ABinaryWalkOOBSteps_le_clock r t ht1

/-! ## The physical value witness -/

theorem check_g1ValsWitness_spec (r : G1Request) (j : Nat)
    (hj : j < r.vals.length) : r.vals[j]? = some (g1ValsWitness r j) :=
  g1ValsWitness_spec r j hj

theorem check_g1ValsWitness_zero (r : G1Request) (a : Bool) (rest : List Bool)
    (hvals : r.vals = a :: rest) : g1ValsWitness r 0 = a :=
  g1ValsWitness_zero r a rest hvals

/-! ## The canonical out-of-range class -/

theorem check_g1CS_canonical_none_clock_oob_unary (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (hs : r.spec = none) :
    ∃ ctx : G1Ctx,
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1OOBState ctx :=
  g1CS_canonical_none_clock_oob_unary r hc ht hs

theorem check_g1CS_canonical_none_clock_oob_binary (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (hs : r.spec = none) :
    ∃ ctx : G1Ctx,
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1OOBState ctx :=
  g1CS_canonical_none_clock_oob_binary r hc ht hs

theorem check_g1CS_canonical_none_clock_oob (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = none) :
    ∃ ctx : G1Ctx,
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1OOBState ctx :=
  g1CS_canonical_none_clock_oob r hc hs

theorem check_g1CS_canonical_none_run_oob (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = none) :
    (TM.run (M := G1M) (g1Point (encodeG1 r))).state.snd.mode = G1Mode.bOOB :=
  g1CS_canonical_none_run_oob r hc hs

theorem check_g1CS_canonical_none_not_accepts (r : G1Request)
    (hc : r.Canonical) (hs : r.spec = none) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false :=
  g1CS_canonical_none_not_accepts r hc hs

theorem check_g1CS_none_not_accepts (r : G1Request) (hs : r.spec = none) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false :=
  g1CS_none_not_accepts r hs

/-! ## The two frozen endpoints -/

theorem check_g1CS_accepts_eq_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      r.spec.isSome :=
  g1CS_accepts_eq_isSome r

theorem check_g1CS_accepts_iff_spec_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true ↔
      r.spec.isSome = true :=
  g1CS_accepts_iff_spec_isSome r

theorem check_g1CS_accepts_iff_wellFormed (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true ↔
      r.WellFormed :=
  g1CS_accepts_iff_wellFormed r

theorem check_g1CS_accepts_eq_decide_wellFormed (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      decide r.WellFormed :=
  g1CS_accepts_eq_decide_wellFormed r

theorem check_g1CS_not_accepts_iff_spec_none (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false ↔
      r.spec = none :=
  g1CS_not_accepts_iff_spec_none r

/-! ## The literal probes -/

theorem check_literal_noncanonical :
    ¬ reqNonCanonInput.Canonical ∧ ¬ reqNonCanonConst.Canonical :=
  G1AcceptsClosureProbes.literal_noncanonical

theorem check_literal_oob_canonical :
    reqArg1OOBWalk.Canonical ∧ reqArg1OOBEmpty.Canonical ∧
      reqArg1OOBBinary.Canonical ∧ reqArg2OOBZero.Canonical ∧
      reqArg2OOBPositive.Canonical :=
  G1AcceptsClosureProbes.literal_oob_canonical

theorem check_literal_none_specs :
    reqNonCanonInput.spec = none ∧ reqNonCanonConst.spec = none ∧
      reqArg1OOBWalk.spec = none ∧ reqArg1OOBEmpty.spec = none ∧
      reqArg1OOBBinary.spec = none ∧ reqArg2OOBZero.spec = none ∧
      reqArg2OOBPositive.spec = none :=
  G1AcceptsClosureProbes.literal_none_specs

theorem check_literal_oob_operands :
    ¬ reqArg1OOBWalk.operandsInBounds ∧ ¬ reqArg1OOBEmpty.operandsInBounds ∧
      ¬ reqArg1OOBBinary.operandsInBounds ∧
      ¬ reqArg2OOBZero.operandsInBounds ∧
      ¬ reqArg2OOBPositive.operandsInBounds :=
  G1AcceptsClosureProbes.literal_oob_operands

theorem check_literal_arg1_oob_reads_operand2 :
    reqArg1OOBBinary.vals[reqArg1OOBBinary.arg2]? = some true :=
  G1AcceptsClosureProbes.literal_arg1_oob_reads_operand2

theorem check_literal_wellFormed :
    reqInputT.WellFormed ∧ reqNotF.WellFormed ∧ reqAndF.WellFormed ∧
      reqOrT.WellFormed ∧ reqConstF.WellFormed ∧ reqConstT.WellFormed :=
  G1AcceptsClosureProbes.literal_wellFormed

theorem check_literal_not_wellFormed :
    ¬ reqNonCanonInput.WellFormed ∧ ¬ reqNonCanonConst.WellFormed ∧
      ¬ reqArg1OOBWalk.WellFormed ∧ ¬ reqArg1OOBEmpty.WellFormed ∧
      ¬ reqArg1OOBBinary.WellFormed ∧ ¬ reqArg2OOBZero.WellFormed ∧
      ¬ reqArg2OOBPositive.WellFormed :=
  G1AcceptsClosureProbes.literal_not_wellFormed

theorem check_literal_defined_accepts :
    TM.accepts (M := G1M) (encodeG1 reqInputT).length
        (g1Point (encodeG1 reqInputT)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqNotF).length
        (g1Point (encodeG1 reqNotF)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqAndF).length
        (g1Point (encodeG1 reqAndF)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqOrT).length
        (g1Point (encodeG1 reqOrT)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqConstF).length
        (g1Point (encodeG1 reqConstF)) = true ∧
      TM.accepts (M := G1M) (encodeG1 reqConstT).length
        (g1Point (encodeG1 reqConstT)) = true :=
  G1AcceptsClosureProbes.literal_defined_accepts

theorem check_literal_noncanonical_not_accepts :
    TM.accepts (M := G1M) (encodeG1 reqNonCanonInput).length
        (g1Point (encodeG1 reqNonCanonInput)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqNonCanonConst).length
        (g1Point (encodeG1 reqNonCanonConst)) = false :=
  G1AcceptsClosureProbes.literal_noncanonical_not_accepts

theorem check_literal_arg1_oob_not_accepts :
    TM.accepts (M := G1M) (encodeG1 reqArg1OOBWalk).length
        (g1Point (encodeG1 reqArg1OOBWalk)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqArg1OOBEmpty).length
        (g1Point (encodeG1 reqArg1OOBEmpty)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqArg1OOBBinary).length
        (g1Point (encodeG1 reqArg1OOBBinary)) = false :=
  G1AcceptsClosureProbes.literal_arg1_oob_not_accepts

theorem check_literal_arg2_oob_not_accepts :
    TM.accepts (M := G1M) (encodeG1 reqArg2OOBZero).length
        (g1Point (encodeG1 reqArg2OOBZero)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqArg2OOBPositive).length
        (g1Point (encodeG1 reqArg2OOBPositive)) = false :=
  G1AcceptsClosureProbes.literal_arg2_oob_not_accepts

theorem check_literal_accepts_eq_isSome :
    TM.accepts (M := G1M) (encodeG1 reqOrT).length
        (g1Point (encodeG1 reqOrT)) = reqOrT.spec.isSome ∧
      TM.accepts (M := G1M) (encodeG1 reqNotF).length
        (g1Point (encodeG1 reqNotF)) = reqNotF.spec.isSome ∧
      TM.accepts (M := G1M) (encodeG1 reqArg1OOBWalk).length
        (g1Point (encodeG1 reqArg1OOBWalk)) = reqArg1OOBWalk.spec.isSome ∧
      TM.accepts (M := G1M) (encodeG1 reqNonCanonInput).length
        (g1Point (encodeG1 reqNonCanonInput)) =
          reqNonCanonInput.spec.isSome :=
  G1AcceptsClosureProbes.literal_accepts_eq_isSome

theorem check_literal_accepts_iff_wellFormed :
    (TM.accepts (M := G1M) (encodeG1 reqAndF).length
        (g1Point (encodeG1 reqAndF)) = true ↔ reqAndF.WellFormed) ∧
      (TM.accepts (M := G1M) (encodeG1 reqArg2OOBPositive).length
        (g1Point (encodeG1 reqArg2OOBPositive)) = true ↔
          reqArg2OOBPositive.WellFormed) :=
  G1AcceptsClosureProbes.literal_accepts_iff_wellFormed

theorem check_literal_oob_not_reject (ctx : G1Ctx) :
    g1OOBState ctx ≠ g1RejectState :=
  G1AcceptsClosureProbes.literal_oob_not_reject ctx

theorem check_literal_oob_not_accept_state (ctx : G1Ctx) :
    g1OOBState ctx ≠ g1AcceptState :=
  G1AcceptsClosureProbes.literal_oob_not_accept_state ctx

theorem check_literal_arg1_oob_run_mode :
    (TM.run (M := G1M) (g1Point (encodeG1 reqArg1OOBWalk))).state.snd.mode =
        G1Mode.bOOB ∧
      (TM.run (M := G1M)
        (g1Point (encodeG1 reqArg1OOBEmpty))).state.snd.mode = G1Mode.bOOB ∧
      (TM.run (M := G1M)
        (g1Point (encodeG1 reqArg1OOBBinary))).state.snd.mode = G1Mode.bOOB :=
  G1AcceptsClosureProbes.literal_arg1_oob_run_mode

theorem check_literal_noncanonical_run_reject :
    (TM.run (M := G1M)
        (g1Point (encodeG1 reqNonCanonInput))).state.snd = g1RejectState ∧
      (TM.run (M := G1M)
        (g1Point (encodeG1 reqNonCanonConst))).state.snd = g1RejectState :=
  G1AcceptsClosureProbes.literal_noncanonical_run_reject

end Pnp3.Tests.TMGateOneAcceptsClosureSurface
