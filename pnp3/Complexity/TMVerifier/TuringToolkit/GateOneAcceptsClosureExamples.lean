import Complexity.TMVerifier.TuringToolkit.GateOneAcceptsClosure

/-!
# S11 literal acceptance-closure probes (2026-09-19)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

Literal `G1Request` witnesses keeping every branch of
`g1CS_accepts_eq_isSome` and `g1CS_accepts_iff_wellFormed` nonvacuous.  Each
verdict is a literal `Bool`, obtained from the theorems by running the real
machine — never by `decide` on `TM.accepts`, which would evaluate the whole
clock.

The accepting side reuses main's five-tag literals from `G1AResultProbes`
(`reqInputT`, `reqNotF`, `reqAndF`, `reqOrT`, `reqConstF`, `reqConstT`) and so
covers **both** completions and both `const` bits, since main's transducer
convention accepts a defined `false` exactly as it accepts a defined `true`.

The nonaccepting side exercises all three route classes, including both
sub-branches of each out-of-range walk:

| request | class | route |
|---|---|---|
| `reqNonCanonInput` | noncanonical | validation prefix → `g1RejectState` |
| `reqNonCanonConst` | noncanonical | validation prefix → `g1RejectState` |
| `reqArg1OOBWalk` | operand-1 out of range | pass-A walk → `bOOB` |
| `reqArg1OOBEmpty` | operand-1 out of range, empty data | S4 install → `bOOB` |
| `reqArg1OOBBinary` | operand-1 out of range, arity 2 | pass-A walk → `bOOB` |
| `reqArg2OOBZero` | operand-2 out of range at index `0` | pass-B → `bOOB` |
| `reqArg2OOBPositive` | operand-2 out of range above `0` | pass-B → `bOOB` |

Only the two noncanonical rows are rejections.  The five out-of-range rows idle
at a `bOOB` boundary, which is neither sink: `literal_oob_not_reject` records
that, so no probe here can be misread as calling `bOOB` a rejection.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1AcceptsClosureProbes

open G1AResultProbes

/-! ## The nonaccepting literals -/

/-- Arity-1 tag with a non-zero unused operand-2 field: not canonical. -/
def reqNonCanonInput : G1Request := ⟨.input, 0, 3, [true]⟩

/-- `const` field beyond the unary bit convention: not canonical. -/
def reqNonCanonConst : G1Request := ⟨.const, 5, 0, []⟩

/-- Canonical `input` whose operand-1 index is past the nonempty data region. -/
def reqArg1OOBWalk : G1Request := ⟨.input, 2, 0, [true]⟩

/-- Canonical `not` with an empty data region: operand 1 cannot select. -/
def reqArg1OOBEmpty : G1Request := ⟨.not, 1, 0, []⟩

/-- Canonical `and` whose operand 2 selects but whose operand 1 is past the
data region. -/
def reqArg1OOBBinary : G1Request := ⟨.and, 3, 0, [true]⟩

/-- Canonical `and` whose operand-2 index is `0` on an empty data region. -/
def reqArg2OOBZero : G1Request := ⟨.and, 0, 0, []⟩

/-- Canonical `or` whose operand-2 index is positive and past the data
region. -/
def reqArg2OOBPositive : G1Request := ⟨.or, 0, 2, [true, false]⟩

/-! ## Pure classification of the literals, decided -/

theorem literal_noncanonical :
    ¬ reqNonCanonInput.Canonical ∧ ¬ reqNonCanonConst.Canonical := by
  decide

theorem literal_oob_canonical :
    reqArg1OOBWalk.Canonical ∧ reqArg1OOBEmpty.Canonical ∧
      reqArg1OOBBinary.Canonical ∧ reqArg2OOBZero.Canonical ∧
      reqArg2OOBPositive.Canonical := by
  decide

theorem literal_none_specs :
    reqNonCanonInput.spec = none ∧ reqNonCanonConst.spec = none ∧
      reqArg1OOBWalk.spec = none ∧ reqArg1OOBEmpty.spec = none ∧
      reqArg1OOBBinary.spec = none ∧ reqArg2OOBZero.spec = none ∧
      reqArg2OOBPositive.spec = none := by
  decide

/-- The out-of-range literals really do leave the operand domain, while staying
canonical: canonicality alone is not what makes them valueless. -/
theorem literal_oob_operands :
    ¬ reqArg1OOBWalk.operandsInBounds ∧ ¬ reqArg1OOBEmpty.operandsInBounds ∧
      ¬ reqArg1OOBBinary.operandsInBounds ∧
      ¬ reqArg2OOBZero.operandsInBounds ∧
      ¬ reqArg2OOBPositive.operandsInBounds := by
  decide

/-- The operand-1 literals keep operand 2 *in* range, so they genuinely take
the pass-A walk branch and not the pass-B one. -/
theorem literal_arg1_oob_reads_operand2 :
    reqArg1OOBBinary.vals[reqArg1OOBBinary.arg2]? = some true := by
  decide

/-! ## Literal well-formedness verdicts -/

theorem literal_wellFormed :
    reqInputT.WellFormed ∧ reqNotF.WellFormed ∧ reqAndF.WellFormed ∧
      reqOrT.WellFormed ∧ reqConstF.WellFormed ∧ reqConstT.WellFormed := by
  decide

theorem literal_not_wellFormed :
    ¬ reqNonCanonInput.WellFormed ∧ ¬ reqNonCanonConst.WellFormed ∧
      ¬ reqArg1OOBWalk.WellFormed ∧ ¬ reqArg1OOBEmpty.WellFormed ∧
      ¬ reqArg1OOBBinary.WellFormed ∧ ¬ reqArg2OOBZero.WellFormed ∧
      ¬ reqArg2OOBPositive.WellFormed := by
  decide

/-! ## Literal machine verdicts

Both defined completions accept; every valueless request does not.  These come
from `g1CS_accepts_eq_isSome` applied to the literal `spec` values, so they are
statements about the real run of the real machine at its own clock. -/

/-- **Defined results accept, `false` exactly as much as `true`.** -/
theorem literal_defined_accepts :
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
  ⟨g1CS_accepts_true_of_spec_some reqInputT true literal_specs.1,
    g1CS_accepts_true_of_spec_some reqNotF false literal_specs.2.1,
    g1CS_accepts_true_of_spec_some reqAndF false literal_specs.2.2.1,
    g1CS_accepts_true_of_spec_some reqOrT true literal_specs.2.2.2.1,
    g1CS_accepts_true_of_spec_some reqConstF false literal_specs.2.2.2.2.1,
    g1CS_accepts_true_of_spec_some reqConstT true literal_specs.2.2.2.2.2⟩

/-- **A noncanonical encoded word does not accept.**  This is the standard
encoded word `encodeG1 r` of a noncanonical request: the word is in the image of
the encoder, the request it came from is not canonical, and the validation
prefix rejects it. -/
theorem literal_noncanonical_not_accepts :
    TM.accepts (M := G1M) (encodeG1 reqNonCanonInput).length
        (g1Point (encodeG1 reqNonCanonInput)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqNonCanonConst).length
        (g1Point (encodeG1 reqNonCanonConst)) = false :=
  ⟨g1CS_noncanonical_not_accepts reqNonCanonInput literal_noncanonical.1,
    g1CS_noncanonical_not_accepts reqNonCanonConst literal_noncanonical.2⟩

/-- **An operand-1 out-of-range request does not accept**, with nonempty data,
with empty data, and at arity 2. -/
theorem literal_arg1_oob_not_accepts :
    TM.accepts (M := G1M) (encodeG1 reqArg1OOBWalk).length
        (g1Point (encodeG1 reqArg1OOBWalk)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqArg1OOBEmpty).length
        (g1Point (encodeG1 reqArg1OOBEmpty)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqArg1OOBBinary).length
        (g1Point (encodeG1 reqArg1OOBBinary)) = false :=
  ⟨g1CS_canonical_none_not_accepts reqArg1OOBWalk literal_oob_canonical.1
      literal_none_specs.2.2.1,
    g1CS_canonical_none_not_accepts reqArg1OOBEmpty literal_oob_canonical.2.1
      literal_none_specs.2.2.2.1,
    g1CS_canonical_none_not_accepts reqArg1OOBBinary
      literal_oob_canonical.2.2.1 literal_none_specs.2.2.2.2.1⟩

/-- **An operand-2 out-of-range request does not accept**, at index `0` and
above it. -/
theorem literal_arg2_oob_not_accepts :
    TM.accepts (M := G1M) (encodeG1 reqArg2OOBZero).length
        (g1Point (encodeG1 reqArg2OOBZero)) = false ∧
      TM.accepts (M := G1M) (encodeG1 reqArg2OOBPositive).length
        (g1Point (encodeG1 reqArg2OOBPositive)) = false :=
  ⟨g1CS_canonical_none_not_accepts reqArg2OOBZero literal_oob_canonical.2.2.2.1
      literal_none_specs.2.2.2.2.2.1,
    g1CS_canonical_none_not_accepts reqArg2OOBPositive
      literal_oob_canonical.2.2.2.2 literal_none_specs.2.2.2.2.2.2⟩

/-! ## The endpoints themselves, at the literals -/

/-- The capstone's Boolean identity, instantiated. -/
theorem literal_accepts_eq_isSome :
    TM.accepts (M := G1M) (encodeG1 reqOrT).length
        (g1Point (encodeG1 reqOrT)) = reqOrT.spec.isSome ∧
      TM.accepts (M := G1M) (encodeG1 reqNotF).length
        (g1Point (encodeG1 reqNotF)) = reqNotF.spec.isSome ∧
      TM.accepts (M := G1M) (encodeG1 reqArg1OOBWalk).length
        (g1Point (encodeG1 reqArg1OOBWalk)) = reqArg1OOBWalk.spec.isSome ∧
      TM.accepts (M := G1M) (encodeG1 reqNonCanonInput).length
        (g1Point (encodeG1 reqNonCanonInput)) =
          reqNonCanonInput.spec.isSome :=
  ⟨g1CS_accepts_eq_isSome reqOrT, g1CS_accepts_eq_isSome reqNotF,
    g1CS_accepts_eq_isSome reqArg1OOBWalk,
    g1CS_accepts_eq_isSome reqNonCanonInput⟩

/-- The well-formedness endpoint, instantiated on an accepting and a
nonaccepting literal. -/
theorem literal_accepts_iff_wellFormed :
    (TM.accepts (M := G1M) (encodeG1 reqAndF).length
        (g1Point (encodeG1 reqAndF)) = true ↔ reqAndF.WellFormed) ∧
      (TM.accepts (M := G1M) (encodeG1 reqArg2OOBPositive).length
        (g1Point (encodeG1 reqArg2OOBPositive)) = true ↔
          reqArg2OOBPositive.WellFormed) :=
  ⟨g1CS_accepts_iff_wellFormed reqAndF,
    g1CS_accepts_iff_wellFormed reqArg2OOBPositive⟩

/-! ## `bOOB` is not a rejection

The out-of-range literals settle in a `bOOB` boundary.  That boundary is
distinct from the literal reject sink in every context, so none of the five
out-of-range probes above may be read as a rejection. -/

theorem literal_oob_not_reject (ctx : G1Ctx) :
    g1OOBState ctx ≠ g1RejectState :=
  g1OOBState_ne_reject ctx

theorem literal_oob_not_accept_state (ctx : G1Ctx) :
    g1OOBState ctx ≠ g1AcceptState :=
  g1OOBState_ne_accept ctx

/-- The canonical out-of-range literals really end in `bOOB`, on the real run
at the real clock — not merely "not in the accept sink". -/
theorem literal_arg1_oob_run_mode :
    (TM.run (M := G1M) (g1Point (encodeG1 reqArg1OOBWalk))).state.snd.mode =
        G1Mode.bOOB ∧
      (TM.run (M := G1M)
        (g1Point (encodeG1 reqArg1OOBEmpty))).state.snd.mode = G1Mode.bOOB ∧
      (TM.run (M := G1M)
        (g1Point (encodeG1 reqArg1OOBBinary))).state.snd.mode = G1Mode.bOOB :=
  ⟨g1CS_canonical_none_run_oob reqArg1OOBWalk literal_oob_canonical.1
      literal_none_specs.2.2.1,
    g1CS_canonical_none_run_oob reqArg1OOBEmpty literal_oob_canonical.2.1
      literal_none_specs.2.2.2.1,
    g1CS_canonical_none_run_oob reqArg1OOBBinary literal_oob_canonical.2.2.1
      literal_none_specs.2.2.2.2.1⟩

/-- The noncanonical literals really end in the literal reject sink. -/
theorem literal_noncanonical_run_reject :
    (TM.run (M := G1M)
        (g1Point (encodeG1 reqNonCanonInput))).state.snd = g1RejectState ∧
      (TM.run (M := G1M)
        (g1Point (encodeG1 reqNonCanonConst))).state.snd = g1RejectState :=
  ⟨g1CS_noncanonical_run_reject reqNonCanonInput literal_noncanonical.1,
    g1CS_noncanonical_run_reject reqNonCanonConst literal_noncanonical.2⟩

end G1AcceptsClosureProbes

end Pnp3.Internal.PsubsetPpoly.TM
