import Complexity.TMVerifier.TuringToolkit.GateOneExamples
import Complexity.TMVerifier.TuringToolkit.GateOneReadB

/-!
# G1 pass-B named examples

**Progress classification: Infrastructure.**  Concrete instances of the T2b
pass-B execution surface: the unary route, both `const` literals, a `true` and
a `false` operand-2 read out of the data region, the out-of-range boundary, the
binary route to the operand-2 field, the frame-level bridge handoff, and exact
literal step counts.  Each capstone is the matching general theorem at a
concrete canonical request—a genuine finite run of the one fixed machine from
its real initial configuration.  Nothing depends on this audit module.

The two `and`/`or` value reads and the out-of-range example all have
`arg2 = 0`: that is the case in which the operand-2 walk terminates without any
destructive round.  The `arg2 = 1` example stops at the operand-2 field
(`g1CS_readB_route_binary_exact`) and the frame-level lemma
`readB_bridge_at_index` records that the very next frame sends the control to
the `bRoundStart` bridge.  The executed bridge and the one destructive round
behind it are in `GateOneIndexRound`, whose own concrete example runs the same
shape of request for exactly one round.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1Examples

/-! ## Concrete requests -/

/-- `not` of the operand-1 field: an arity-1 route. -/
def reqNotRoute : G1Request := ⟨.not, 0, 0, [true]⟩

/-- The `const` literal `0`. -/
def reqConstFalse : G1Request := ⟨.const, 0, 0, []⟩

/-- The `const` literal `1`. -/
def reqConstTrue : G1Request := ⟨.const, 1, 0, []⟩

/-- `and` whose operand-2 field selects the value `true`. -/
def reqAndTrueB : G1Request := ⟨.and, 0, 0, [true]⟩

/-- `and` whose operand-2 field selects the value `false`. -/
def reqAndFalseB : G1Request := ⟨.and, 0, 0, [false, true]⟩

/-- `or` whose operand-2 field selects the value `true`. -/
def reqOrTrueB : G1Request := ⟨.or, 1, 0, [true, false]⟩

/-- `and` with an empty data region: the operand-2 index is out of range. -/
def reqAndOOB : G1Request := ⟨.and, 0, 0, []⟩

theorem reqNotRoute_canonical : reqNotRoute.Canonical := by decide
theorem reqConstFalse_canonical : reqConstFalse.Canonical := by decide
theorem reqConstTrue_canonical : reqConstTrue.Canonical := by decide
theorem reqAndTrueB_canonical : reqAndTrueB.Canonical := by decide
theorem reqAndFalseB_canonical : reqAndFalseB.Canonical := by decide
theorem reqOrTrueB_canonical : reqOrTrueB.Canonical := by decide
theorem reqAndOOB_canonical : reqAndOOB.Canonical := by decide

/-! ## The unary route: `input` and `not` reach the pass-A handoff -/

/-- The unary-route capstone statement, at a concrete request. -/
abbrev ReadARouteAt (r : G1Request) : Prop :=
  TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadARouteSteps r) =
    g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + 2))
      (g1_route_lt_tapeLength r _ (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .readAStart .p0 false false false g1Ctx0

theorem readB_route_input : ReadARouteAt reqInput :=
  g1CS_readB_route_unary_exact reqInput reqInput_canonical (Or.inl rfl)

theorem readB_route_not : ReadARouteAt reqNotRoute :=
  g1CS_readB_route_unary_exact reqNotRoute reqNotRoute_canonical (Or.inr rfl)

/-- `input`: exactly `2 * 40 + 9` T2a steps plus `4 * 3` rescan steps. -/
theorem readB_route_input_steps :
    g1ReadARouteSteps reqInput = 2 * 40 + 9 + 12 := by
  simp [g1ReadARouteSteps, g1ReadBHandoffSteps, encodeG1_length, reqInput,
    G1Tag.units]

/-- `input`: the head stops on the first cell of the operand-1 field. -/
theorem readB_route_input_head :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 reqInput)))
        (g1ReadARouteSteps reqInput)).head : Nat) = 12 :=
  g1CS_readB_route_unary_head reqInput reqInput_canonical (Or.inl rfl)

/-- `not`: the head stops on the first cell of the operand-1 field. -/
theorem readB_route_not_head :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotRoute)))
        (g1ReadARouteSteps reqNotRoute)).head : Nat) = 20 :=
  g1CS_readB_route_unary_head reqNotRoute reqNotRoute_canonical (Or.inr rfl)

theorem readB_route_input_clock :
    g1ReadARouteSteps reqInput ≤ g1Clock (encodeG1 reqInput).length :=
  g1ReadARouteSteps_le_clock reqInput

/-! ## Both `const` literals, decoded physically -/

/-- The `const` capstone statement, at a concrete request and literal. -/
abbrev ConstRouteAt (r : G1Request) (b : Bool) : Prop :=
  TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ConstRouteSteps r) =
    g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 3))
      (g1_route_lt_tapeLength r _ (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .combineStart .p0 false false false (g1Ctx0.withVB b)

theorem readB_const_false : ConstRouteAt reqConstFalse false :=
  g1CS_readB_route_const_exact reqConstFalse reqConstFalse_canonical rfl false
    rfl

theorem readB_const_true : ConstRouteAt reqConstTrue true :=
  g1CS_readB_route_const_exact reqConstTrue reqConstTrue_canonical rfl true rfl

/-- The decoded literal really sits in the fixed Boolean register. -/
theorem readB_const_true_vB :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue)))
        (g1ConstRouteSteps reqConstTrue)).state.snd.ctx.vB = true :=
  g1CS_readB_route_const_vB reqConstTrue reqConstTrue_canonical rfl true rfl

/-- `const 1`: exactly `2 * 36 + 9` T2a steps, `4 * 6` rescan steps and the one
literal-dispatch step. -/
theorem readB_const_true_steps :
    g1ConstRouteSteps reqConstTrue = 2 * 36 + 9 + 24 + 1 := by
  simp [g1ConstRouteSteps, g1FieldRouteSteps, g1ReadBHandoffSteps,
    encodeG1_length, reqConstTrue, G1Tag.units]

theorem readB_const_true_clock :
    g1ConstRouteSteps reqConstTrue ≤ g1Clock (encodeG1 reqConstTrue).length :=
  g1ConstRouteSteps_le_clock reqConstTrue

/-! ## The binary route to the operand-2 field -/

/-- The binary-route capstone statement, at a concrete request. -/
abbrev FieldRouteAt (r : G1Request) : Prop :=
  TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1FieldRouteSteps r) =
    g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 3))
      (g1_route_lt_tapeLength r _ (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .bScan .p0 false false false g1Ctx0

/-- `reqAnd` has `arg2 = 1`, so this is the last endpoint the *pass-B read*
proves for it: the head sits on the first cell of `index^1`.  One destructive
round past it is `GateOneIndexRound`. -/
theorem readB_field_route_and : FieldRouteAt reqAnd :=
  g1CS_readB_route_binary_exact reqAnd reqAnd_canonical (Or.inl rfl)

theorem readB_field_route_or : FieldRouteAt reqOr :=
  g1CS_readB_route_binary_exact reqOr reqOr_canonical (Or.inr rfl)

/-- **The bridge branch, named.**  From the operand-2 field of a request with
`arg2 > 0` the very next frame is an unspent `index`, and the fixed control
hands off to `bRoundStart`, the one-step bridge into the destructive round.  The
executed round is `GateOneIndexRound.g1CS_index_first_round`; this lemma is only
the frame-level handoff. -/
theorem readB_bridge_at_index (rest : List G1Frame) :
    g1AdvanceList .bScan (.index :: rest) = g1AdvanceList .bRoundStart rest :=
  g1_bScan_index_bridge rest

/-! ## Genuine operand-2 reads out of the data region

Each of the three theorems below resolves `r.vals[r.arg2]?` **physically**: the
value comes from the data frame the machine reads off the tape, and the only
hypothesis about it is the pure selector equation on the encoded request. -/

/-- The zero-index read capstone statement, at a concrete request and value. -/
abbrev ReadBZeroAt (r : G1Request) (b : Bool) : Prop :=
  TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
      (g1ReadBSteps r) =
    g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 5))
      (g1_route_lt_tapeLength r _ (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .readAResetStart .p0 false false false (g1Ctx0.withVB b)

/-- **`and`, operand-2 value `true`.** -/
theorem readB_and_true : ReadBZeroAt reqAndTrueB true :=
  g1CS_readB_zero_exact reqAndTrueB reqAndTrueB_canonical (Or.inl rfl) rfl true
    rfl

/-- **`and`, operand-2 value `false`.** -/
theorem readB_and_false : ReadBZeroAt reqAndFalseB false :=
  g1CS_readB_zero_exact reqAndFalseB reqAndFalseB_canonical (Or.inl rfl) rfl
    false rfl

/-- **`or`, operand-2 value `true`.** -/
theorem readB_or_true : ReadBZeroAt reqOrTrueB true :=
  g1CS_readB_zero_exact reqOrTrueB reqOrTrueB_canonical (Or.inr rfl) rfl true
    rfl

/-- The resolved value is in `vB`. -/
theorem readB_and_true_vB :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrueB)))
        (g1ReadBSteps reqAndTrueB)).state.snd.ctx.vB = true :=
  g1CS_readB_zero_vB reqAndTrueB reqAndTrueB_canonical (Or.inl rfl) rfl true rfl

/-- The read is non-destructive: the tape is exactly the initial tape. -/
theorem readB_and_true_tape :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrueB)))
        (g1ReadBSteps reqAndTrueB)).tape =
      (G1M.initialConfig (g1Point (encodeG1 reqAndTrueB))).tape :=
  g1CS_readB_zero_tape reqAndTrueB reqAndTrueB_canonical (Or.inl rfl) rfl true
    rfl

/-- `and` with `arg2 = 0` over a one-element data region: exactly
`2 * 44 + 9` T2a steps, `4 * 9` rescan steps and the one store step. -/
theorem readB_and_true_steps :
    g1ReadBSteps reqAndTrueB = 2 * 44 + 9 + 36 + 1 := by
  simp [g1ReadBSteps, g1ReadBHandoffSteps, encodeG1_length, reqAndTrueB,
    G1Tag.units]

theorem readB_and_true_clock :
    g1ReadBSteps reqAndTrueB ≤ g1Clock (encodeG1 reqAndTrueB).length :=
  g1ReadBSteps_le_clock reqAndTrueB

/-! ## The out-of-range boundary -/

/-- **`and` with an empty data region.**  The probe meets the `output`
destination frame and the machine stops at the explicit, stable `bOOB`
boundary — not at a success handoff, and not in the reject sink. -/
theorem readB_and_oob :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 reqAndOOB)))
        (g1ReadBOOBSteps reqAndOOB) =
      g1AlignedConfig (encodeG1 reqAndOOB).length
        (4 * (reqAndOOB.tag.units + reqAndOOB.arg1 + 5))
        (g1_route_lt_tapeLength reqAndOOB _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 reqAndOOB))).tape
        .bOOB .p0 false false false g1Ctx0 :=
  g1CS_readB_zero_oob_exact reqAndOOB reqAndOOB_canonical (Or.inl rfl) rfl rfl

/-- The out-of-range boundary is stable for any further budget. -/
theorem readB_and_oob_stable (k : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 reqAndOOB)))
        (g1ReadBOOBSteps reqAndOOB + k) =
      g1AlignedConfig (encodeG1 reqAndOOB).length
        (4 * (reqAndOOB.tag.units + reqAndOOB.arg1 + 5))
        (g1_route_lt_tapeLength reqAndOOB _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 reqAndOOB))).tape
        .bOOB .p0 false false false g1Ctx0 :=
  g1CS_readB_zero_oob_stable reqAndOOB reqAndOOB_canonical (Or.inl rfl) rfl rfl k

theorem readB_and_oob_state :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndOOB)))
        (g1ReadBOOBSteps reqAndOOB)).state.snd = g1OOBState g1Ctx0 :=
  g1CS_readB_zero_oob_state reqAndOOB reqAndOOB_canonical (Or.inl rfl) rfl rfl

theorem readB_and_oob_tape :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndOOB)))
        (g1ReadBOOBSteps reqAndOOB)).tape =
      (G1M.initialConfig (g1Point (encodeG1 reqAndOOB))).tape :=
  g1CS_readB_zero_oob_tape reqAndOOB reqAndOOB_canonical (Or.inl rfl) rfl rfl

/-- `and` with an empty data region: exactly `2 * 40 + 9` T2a steps and
`4 * 9` rescan steps; there is no store step on this branch. -/
theorem readB_and_oob_steps :
    g1ReadBOOBSteps reqAndOOB = 2 * 40 + 9 + 36 := by
  simp [g1ReadBOOBSteps, g1ReadBHandoffSteps, encodeG1_length, reqAndOOB,
    G1Tag.units]

theorem readB_and_oob_clock :
    g1ReadBOOBSteps reqAndOOB ≤ g1Clock (encodeG1 reqAndOOB).length :=
  g1ReadBOOBSteps_le_clock reqAndOOB

/-- **Success and out-of-range never collide.** -/
theorem readB_oob_ne_success :
    g1OOBState g1Ctx0 ≠ g1ReadAResetState (g1Ctx0.withVB true) :=
  g1CS_readB_zero_oob_ne_success _

/-- **Out of range is not rejection.** -/
theorem readB_oob_ne_reject : g1OOBState g1Ctx0 ≠ g1RejectState :=
  g1CS_readB_oob_ne_reject

end G1Examples

end Pnp3.Internal.PsubsetPpoly.TM
