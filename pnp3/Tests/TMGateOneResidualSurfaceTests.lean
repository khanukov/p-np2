import Complexity.TMVerifier.TuringToolkit.GateOneSemantics

/-!
# G1 pass-A residual layer, pure: surface tests

Import-side probes for the S1a pure surface: the four unary residuals of
operand 1 (`GateOneResidual`), the operand-2 value `g1OperandB`, and the pure
bridge from `(tag, b, a)` to `G1Request.spec` (`GateOneSemantics`).

**Nothing here is about a machine.**  There is no configuration, no head, no
step, no `G1Ctx` and no `TM.runConfig` in any statement below; the pass-A
control that would consume the residual is deferred to S1b and is claimed
nowhere.  The `const` tag is excluded from every bridge, and
`check_g1Residual_const_apply_ne_spec` pins the concrete request that makes the
exclusion load-bearing.

This is an audit surface: every public declaration of the S1a pure layer is
pinned, and every wrapper below is discharged by the library theorem itself, so
nothing new is proved here.
-/

namespace Pnp3.Tests.TMGateOneResidualSurface

open Pnp3.Internal.PsubsetPpoly.TM

-- The residual carrier, its application, the residual table and the operand-2
-- selector: the only public declarations of the slice that are not
-- propositions.  Every public *theorem* is pinned by an exact
-- theorem-contract wrapper below, which subsumes a `#check` probe.
#check @G1Residual
#check @G1Residual.apply
#check @g1Residual
#check @g1OperandB

/-! ## Exact theorem-contract pins: the residual type -/

/-- The residual carrier is exactly four-valued — two bits, no more. -/
theorem check_G1Residual_card : Fintype.card G1Residual = 4 :=
  G1Residual.card_eq_four

/-- The defining truth table of `G1Residual.apply`, one row per residual. -/
theorem check_G1Residual_apply_table (a : Bool) :
    G1Residual.idA.apply a = a ∧ G1Residual.notA.apply a = !a ∧
      G1Residual.constFalse.apply a = false ∧
      G1Residual.constTrue.apply a = true :=
  ⟨G1Residual.apply_idA a, G1Residual.apply_notA a,
    G1Residual.apply_constFalse a, G1Residual.apply_constTrue a⟩

/-- The four residuals are pairwise distinct *operations*. -/
theorem check_G1Residual_apply_pairwise_ne (res res' : G1Residual)
    (h : res ≠ res') : ∃ a : Bool, res.apply a ≠ res'.apply a :=
  G1Residual.apply_pairwise_ne res res' h

/-! ## Exact theorem-contract pins: the residual table -/

/-- The two arity-1 rows: independent of the operand-2 value. -/
theorem check_g1Residual_unary_rows (b : Bool) :
    g1Residual .input b = G1Residual.idA ∧
      g1Residual .not b = G1Residual.notA :=
  ⟨g1Residual_input b, g1Residual_not b⟩

/-- The four binary rows, entry by entry. -/
theorem check_g1Residual_binary_rows :
    g1Residual .and false = G1Residual.constFalse ∧
      g1Residual .and true = G1Residual.idA ∧
      g1Residual .or false = G1Residual.idA ∧
      g1Residual .or true = G1Residual.constTrue :=
  ⟨g1Residual_and_false, g1Residual_and_true, g1Residual_or_false,
    g1Residual_or_true⟩

/-- **The `const` row is filler.**  Pinned so that a later change to the filler
is visible in the surface, not silent. -/
theorem check_g1Residual_const_filler (b : Bool) :
    g1Residual .const b = G1Residual.constFalse :=
  g1Residual_const_filler b

/-- `input` and `not` ignore operand 2. -/
theorem check_g1Residual_unary_const {t : G1Tag} (ht : t = .input ∨ t = .not)
    (b b' : Bool) : g1Residual t b = g1Residual t b' :=
  g1Residual_unary_const ht b b'

/-- `and` and `or` genuinely depend on operand 2. -/
theorem check_g1Residual_binary_ne :
    g1Residual .and false ≠ g1Residual .and true ∧
      g1Residual .or false ≠ g1Residual .or true :=
  g1Residual_binary_ne

/-- **The residual truth table**, one exact equation per pass-A tag. -/
theorem check_g1Residual_apply_rows (a b : Bool) :
    (g1Residual .input b).apply a = a ∧ (g1Residual .not b).apply a = !a ∧
      (g1Residual .and b).apply a = (a && b) ∧
      (g1Residual .or b).apply a = (a || b) :=
  ⟨g1Residual_input_apply a b, g1Residual_not_apply a b,
    g1Residual_and_apply a b, g1Residual_or_apply a b⟩

/-- The same four rows, as the packaged library statement. -/
theorem check_g1Residual_apply_table (a b : Bool) :
    (g1Residual .input b).apply a = a ∧ (g1Residual .not b).apply a = !a ∧
      (g1Residual .and b).apply a = (a && b) ∧
      (g1Residual .or b).apply a = (a || b) :=
  g1Residual_apply_table a b

/-! ## Exact theorem-contract pins: the operand-2 value -/

/-- `g1OperandB` per tag: binary gates select, arity-1 gates do not. -/
theorem check_g1OperandB_rows (a1 a2 : Nat) (vals : List Bool) :
    g1OperandB (G1Request.mk .input a1 a2 vals) = some false ∧
      g1OperandB (G1Request.mk .const a1 a2 vals) = some false ∧
      g1OperandB (G1Request.mk .not a1 a2 vals) = some false ∧
      g1OperandB (G1Request.mk .and a1 a2 vals) = vals[a2]? ∧
      g1OperandB (G1Request.mk .or a1 a2 vals) = vals[a2]? :=
  ⟨g1OperandB_input a1 a2 vals, g1OperandB_const a1 a2 vals,
    g1OperandB_not a1 a2 vals, g1OperandB_and a1 a2 vals,
    g1OperandB_or a1 a2 vals⟩

theorem check_g1OperandB_of_arity_one {r : G1Request} (h : r.tag.arity = 1) :
    g1OperandB r = some false :=
  g1OperandB_of_arity_one h

theorem check_g1OperandB_of_arity_two {r : G1Request} (h : r.tag.arity = 2) :
    g1OperandB r = r.vals[r.arg2]? :=
  g1OperandB_of_arity_two h

/-- A well-formed request has an operand-2 value, with no machine assumption. -/
theorem check_g1OperandB_isSome_of_wellFormed {r : G1Request}
    (h : r.WellFormed) : ∃ b : Bool, g1OperandB r = some b :=
  g1OperandB_isSome_of_wellFormed h

/-- A well-formed non-`const` request selects an operand-1 value. -/
theorem check_g1OperandA_isSome_of_wellFormed {r : G1Request}
    (h : r.WellFormed) (ht : r.tag ≠ .const) :
    ∃ a : Bool, r.vals[r.arg1]? = some a :=
  g1OperandA_isSome_of_wellFormed h ht

/-! ## Exact theorem-contract pins: the residual bridge -/

theorem check_g1Residual_apply_spec_unary {r : G1Request}
    (ht : r.tag = .input ∨ r.tag = .not) {a res : Bool} (b : Bool)
    (ha : r.vals[r.arg1]? = some a) (hs : r.spec = some res) :
    (g1Residual r.tag b).apply a = res :=
  g1Residual_apply_spec_unary ht b ha hs

theorem check_g1Residual_apply_spec_binary {r : G1Request}
    (ht : r.tag = .and ∨ r.tag = .or) {a b res : Bool}
    (ha : r.vals[r.arg1]? = some a) (hb : r.vals[r.arg2]? = some b)
    (hs : r.spec = some res) : (g1Residual r.tag b).apply a = res :=
  g1Residual_apply_spec_binary ht ha hb hs

/-- **The residual bridge**: `const` excluded, everything else exact. -/
theorem check_g1Residual_apply_spec {r : G1Request} (ht : r.tag ≠ .const)
    {a b res : Bool} (ha : r.vals[r.arg1]? = some a)
    (hb : g1OperandB r = some b) (hs : r.spec = some res) :
    (g1Residual r.tag b).apply a = res :=
  g1Residual_apply_spec ht ha hb hs

/-- The converse direction, on a canonical non-`const` request. -/
theorem check_g1Spec_eq_residual_apply {r : G1Request} (hc : r.Canonical)
    (ht : r.tag ≠ .const) {a b : Bool} (ha : r.vals[r.arg1]? = some a)
    (hb : g1OperandB r = some b) :
    r.spec = some ((g1Residual r.tag b).apply a) :=
  g1Spec_eq_residual_apply hc ht ha hb

/-- **Selection, not an external input**: `input` returns the value selected
out of the on-tape runtime region `vals`, and nothing more. -/
theorem check_g1Residual_input_selects (i : Nat) (vals : List Bool) (b : Bool)
    {a : Bool} (ha : vals[i]? = some a) :
    (g1Residual .input b).apply a = a ∧
      (G1Request.mk .input i 0 vals).spec = some a :=
  g1Residual_input_selects i vals b ha

theorem check_g1Residual_not_selects (i : Nat) (vals : List Bool) (b : Bool)
    {a : Bool} (ha : vals[i]? = some a) :
    (g1Residual .not b).apply a = !a ∧
      (G1Request.mk .not i 0 vals).spec = some (!a) :=
  g1Residual_not_selects i vals b ha

/-- **The `const` exclusion is load-bearing**: the concrete canonical request
on which the filler row would be wrong. -/
theorem check_g1Residual_const_apply_ne_spec :
    (G1Request.mk .const 1 0 [false, false]).Canonical ∧
      (G1Request.mk .const 1 0 [false, false]).vals[
        (G1Request.mk .const 1 0 [false, false]).arg1]? = some false ∧
      g1OperandB (G1Request.mk .const 1 0 [false, false]) = some false ∧
      (G1Request.mk .const 1 0 [false, false]).spec = some true ∧
      (g1Residual (G1Request.mk .const 1 0 [false, false]).tag false).apply
        false ≠ true :=
  g1Residual_const_apply_ne_spec

/-! ## The capstone

There is no machine-run capstone in a pure slice.  The capstone of S1a is the
exact five-tag truth-table/spec suite below: the bridge for every pass-A tag,
the four rows it composes to, the `const` filler row, and the concrete
canonical `const` request that shows the filler would be wrong. -/

theorem check_g1Residual_spec_capstone :
    (∀ (r : G1Request) (a b res : Bool), r.tag ≠ .const →
        r.vals[r.arg1]? = some a → g1OperandB r = some b →
        r.spec = some res → (g1Residual r.tag b).apply a = res) ∧
      (∀ a b : Bool,
          (g1Residual .input b).apply a = a ∧
            (g1Residual .not b).apply a = !a ∧
            (g1Residual .and b).apply a = (a && b) ∧
            (g1Residual .or b).apply a = (a || b)) ∧
      (∀ b : Bool, g1Residual .const b = G1Residual.constFalse) ∧
      (∃ r : G1Request, r.tag = .const ∧ r.Canonical ∧
          r.vals[r.arg1]? = some false ∧ g1OperandB r = some false ∧
          r.spec = some true ∧
          (g1Residual r.tag false).apply false ≠ true) :=
  g1Residual_spec_capstone

end Pnp3.Tests.TMGateOneResidualSurface
