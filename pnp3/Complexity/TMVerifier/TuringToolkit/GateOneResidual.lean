import Complexity.TMVerifier.TuringToolkit.GateOneEncoding
import Mathlib.Tactic.DeriveFintype

/-!
# G1 pass A: the four residual operations of operand 1

**Progress classification: Infrastructure.**  A *pure* four-element type and
one pure function.  No Turing machine, no execution, no context, no request
state, no acceptance, no verifier claim.

Pass B resolves the operand-2 value `b` of a binary gate.  Once `b` is known
the whole remaining gate is a **unary** operation of the operand-1 value `a`,
and there are exactly four such operations — `idA`, `notA`, `constFalse`,
`constTrue`.  `g1Residual` is the pre-composition table; `input` and `not` do
not use operand 2 at all, so their residual is independent of `b`:

| tag | `b = false` | `b = true` |
|-----|-------------|------------|
| `input` | `idA` | `idA` |
| `not` | `notA` | `notA` |
| `and` | `constFalse` | `idA` |
| `or` | `idA` | `constTrue` |

**This is pure ABI data.**  `G1Residual` is a closed four-element inductive: no
`Nat`, no index, no width parameter, no request-dependent payload, nothing
read from a tape.  It is *not* an advice input and it is *not* a state field —
this slice adds no field to `G1Ctx`, touches no control table and executes no
step.  Four values are two bits, and the design intent is that the deferred
pass-A control can carry them in the *existing* finite context rather than in
a new field; **that wiring is deferred to S1b and is claimed nowhere here.**

**`G1Tag.const` is not a pass-A tag.**  A `const` gate is decided during the
pass-B rescan from its literal field, so its residual is never needed.  The
`const` row below is therefore an arbitrary filler:
`g1Residual_const_filler` states exactly what the filler is, no other theorem
of this module reads it, and every semantic bridge of `GateOneSemantics` is
restricted to non-`const` tags by a disequality or explicit tag case —
`GateOneSemantics.g1Residual_const_apply_ne_spec` exhibits the concrete
canonical `const` request on which the filler row *would* be wrong, so the
exclusion is load-bearing rather than decorative.  Proving that the pass-A
control physically rejects a `const` run is a **control-level** statement and
is deferred to S1b.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- **The four unary residuals of operand 1.**  Finite, four-element, closed:
no `Nat`, no index, no request-dependent data. -/
inductive G1Residual
  | idA | notA | constFalse | constTrue
  deriving Fintype, DecidableEq, Repr

/-- Applying a residual to the operand-1 value. -/
def G1Residual.apply : G1Residual → Bool → Bool
  | .idA, a => a
  | .notA, a => !a
  | .constFalse, _ => false
  | .constTrue, _ => true

/-! ### The truth table of `apply`, one equation per residual -/

@[simp] theorem G1Residual.apply_idA (a : Bool) : G1Residual.idA.apply a = a := rfl

@[simp] theorem G1Residual.apply_notA (a : Bool) :
    G1Residual.notA.apply a = !a := rfl

@[simp] theorem G1Residual.apply_constFalse (a : Bool) :
    G1Residual.constFalse.apply a = false := rfl

@[simp] theorem G1Residual.apply_constTrue (a : Bool) :
    G1Residual.constTrue.apply a = true := rfl

/-- **The type really is four-element.**  Two bits, exactly. -/
theorem G1Residual.card_eq_four : Fintype.card G1Residual = 4 := rfl

/-- **The four residuals are pairwise different operations**, so a two-bit
carrier genuinely has to distinguish all four. -/
theorem G1Residual.apply_pairwise_ne :
    ∀ res res' : G1Residual, res ≠ res' → ∃ a : Bool, res.apply a ≠ res'.apply a := by
  decide

/-- **The residual of a gate whose operand-2 value is already known.**  The
`const` row is filler: `const` is finished in pass B and never needs a
residual. -/
def g1Residual : G1Tag → Bool → G1Residual
  | .input, _ => .idA
  | .const, _ => .constFalse
  | .not, _ => .notA
  | .and, b => if b then .idA else .constFalse
  | .or, b => if b then .constTrue else .idA

/-! ### The table, entry by entry -/

@[simp] theorem g1Residual_input (b : Bool) : g1Residual .input b = .idA := rfl

@[simp] theorem g1Residual_not (b : Bool) : g1Residual .not b = .notA := rfl

@[simp] theorem g1Residual_and_false : g1Residual .and false = .constFalse := rfl

@[simp] theorem g1Residual_and_true : g1Residual .and true = .idA := rfl

@[simp] theorem g1Residual_or_false : g1Residual .or false = .idA := rfl

@[simp] theorem g1Residual_or_true : g1Residual .or true = .constTrue := rfl

/-- **The `const` row is filler, and this is the only theorem that reads it.**
Nothing else uses this equation: `const` is decided in pass B from its literal
field, and every bridge in `GateOneSemantics` carries `r.tag ≠ .const`. -/
theorem g1Residual_const_filler (b : Bool) :
    g1Residual .const b = .constFalse := rfl

/-- **`input` and `not` residuals do not depend on operand 2.** -/
theorem g1Residual_unary_const {t : G1Tag} (ht : t = .input ∨ t = .not)
    (b b' : Bool) : g1Residual t b = g1Residual t b' := by
  rcases ht with rfl | rfl <;> rfl

/-- **The binary residuals genuinely do depend on operand 2**, so the table is
not vacuous on `and`/`or`. -/
theorem g1Residual_binary_ne :
    g1Residual .and false ≠ g1Residual .and true ∧
      g1Residual .or false ≠ g1Residual .or true := by
  constructor <;> decide

/-! ### The composed truth table: residual, applied

Four exact equations, one per pass-A tag.  Each says the pre-composed residual
is the gate's own Boolean operation of `(a, b)`. -/

/-- **`and` is `&&`, pre-composed.** -/
@[simp] theorem g1Residual_and_apply (a b : Bool) :
    (g1Residual .and b).apply a = (a && b) := by cases b <;> cases a <;> rfl

/-- **`or` is `||`, pre-composed.** -/
@[simp] theorem g1Residual_or_apply (a b : Bool) :
    (g1Residual .or b).apply a = (a || b) := by cases b <;> cases a <;> rfl

/-- **`input` is the identity on the operand-1 *value*.**  `a` is whatever the
caller selected; this says nothing about where that value came from, and in
particular it is not an external circuit-input claim. -/
@[simp] theorem g1Residual_input_apply (a b : Bool) :
    (g1Residual .input b).apply a = a := rfl

/-- **`not` is negation of the operand-1 *value*.** -/
@[simp] theorem g1Residual_not_apply (a b : Bool) :
    (g1Residual .not b).apply a = !a := rfl

/-- **The four pass-A rows, in one statement.**  The `const` row is absent by
construction: it has no correct entry, only the filler of
`g1Residual_const_filler`. -/
theorem g1Residual_apply_table (a b : Bool) :
    (g1Residual .input b).apply a = a ∧ (g1Residual .not b).apply a = !a ∧
      (g1Residual .and b).apply a = (a && b) ∧
      (g1Residual .or b).apply a = (a || b) :=
  ⟨g1Residual_input_apply a b, g1Residual_not_apply a b,
    g1Residual_and_apply a b, g1Residual_or_apply a b⟩

end Pnp3.Internal.PsubsetPpoly.TM
