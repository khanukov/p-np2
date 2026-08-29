import Complexity.TMVerifier.TuringToolkit.GateOneResidual

/-!
# G1 pure gate semantics

**Progress classification: Infrastructure.**  The *pure* meaning of a
`G1Request` and its branch equations.  No Turing machine, no execution, no
verifier: the T2a slice does **not** prove that the machine computes `spec`.

Operand selection is partial list indexing on the runtime value region,
`vals[i]?` — the `getElem?`/`List.get?` selector, `none` exactly out of range.
(`List.get?` is deprecated in this toolchain; `vals[i]?` is the same function
under the current spelling.)  A future circuit bridge must prefix external
input values into `vals`; the `input` tag here is therefore a partial copy from
the single on-tape runtime region, not yet an `SLGate.input` theorem.

| tag | arity | `arg1` | `arg2` |
|-----|-------|--------|--------|
| `input` | 1 | selected value index | unused, `0` |
| `const` | 1 | the bit, in unary (`0 ↦ false`, `1 ↦ true`) | unused, `0` |
| `not` | 1 | operand index | unused, `0` |
| `and`, `or` | 2 | operand-1 index | operand-2 index |

A larger `const` field, a non-zero unused field, or an out-of-range operand
gives `none`.  A *successful* result may of course be `false`.

## The residual bridge

`g1OperandB` is the operand-2 value a pass-A step would start from: the
selected data-region entry of a binary gate, and the convention value `false`
for an arity-1 gate, which does not use operand 2 at all.  It is a function of
the *pure request* only — there is no configuration, head, step count or finite
context anywhere in this file.

`g1Residual_apply_spec` is the bridge: from `r.tag ≠ .const`,
`r.vals[r.arg1]? = some a`, `g1OperandB r = some b` and `r.spec = some res`,
conclude `(g1Residual r.tag b).apply a = res`.  It is proved by cases on the
tag and the two Boolean values through the `getElem?` selector equations.
**No hypothesis is moved onto a machine, and nothing here says a machine
computes anything**: this is an equation between `G1Request.spec`,
`g1Residual` and list indexing.  What the deferred pass-A slices still have to
show — that the interpreter latches `g1Residual r.tag b` and reads
`r.vals[r.arg1]` off the tape — is claimed nowhere in this slice.

`const` is excluded from every bridge, and non-vacuously so:
`g1Residual_const_apply_ne_spec` exhibits the concrete canonical request on
which the filler `const` row of `g1Residual` *would* be wrong, which is why the
hypothesis is not decoration.  That a pass-A run physically never carries a
`const` tag is a control-level statement, deferred to S1b.

`input` and `not` keep selection separate from the values: `a` is whatever
`r.vals[r.arg1]?` selected out of the single on-tape runtime region, and
`g1Residual_input_selects` says only that the `input` residual returns *that*
selected value.  No external circuit input and no `SLGate.input` theorem is
claimed here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- **The pure one-gate semantics.**  Runtime operands are selected from
`vals` by partial list indexing; the arity/unused-field conventions are
explicit in each branch. -/
def G1Request.spec (r : G1Request) : Option Bool :=
  match r.tag with
  | .input => if r.arg2 = 0 then r.vals[r.arg1]? else none
  | .const =>
      if r.arg2 = 0 then
        (if r.arg1 = 0 then some false
         else if r.arg1 = 1 then some true else none)
      else none
  | .not => if r.arg2 = 0 then r.vals[r.arg1]?.map (!·) else none
  | .and =>
      match r.vals[r.arg1]?, r.vals[r.arg2]? with
      | some a, some b => some (a && b)
      | _, _ => none
  | .or =>
      match r.vals[r.arg1]?, r.vals[r.arg2]? with
      | some a, some b => some (a || b)
      | _, _ => none

/-- Operand-domain condition, separate from the unused-field convention. -/
def G1Request.operandsInBounds (r : G1Request) : Prop :=
  match r.tag with
  | .const => True
  | .input | .not => r.arg1 < r.vals.length
  | .and | .or => r.arg1 < r.vals.length ∧ r.arg2 < r.vals.length

/-- Canonical unused fields plus existing operands.  Canonicity alone does not
imply this predicate. -/
def G1Request.WellFormed (r : G1Request) : Prop :=
  r.Canonical ∧ r.operandsInBounds

instance (r : G1Request) : Decidable r.operandsInBounds := by
  unfold G1Request.operandsInBounds
  cases r.tag <;> infer_instance

instance (r : G1Request) : Decidable r.WellFormed :=
  instDecidableAnd

namespace G1Request

/-! ## Branch simplification -/

@[simp] theorem spec_input (i : Nat) (vals : List Bool) :
    (G1Request.mk .input i 0 vals).spec = vals[i]? := rfl

@[simp] theorem spec_const_false (vals : List Bool) :
    (G1Request.mk .const 0 0 vals).spec = some false := rfl

@[simp] theorem spec_const_true (vals : List Bool) :
    (G1Request.mk .const 1 0 vals).spec = some true := rfl

/-- A `const` field beyond the unary bit convention is not canonical. -/
theorem spec_const_out_of_convention (k : Nat) (hk : 2 ≤ k)
    (vals : List Bool) : (G1Request.mk .const k 0 vals).spec = none := by
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [spec, h0, h1]

@[simp] theorem spec_not (i : Nat) (vals : List Bool) :
    (G1Request.mk .not i 0 vals).spec = vals[i]?.map (!·) := rfl

theorem spec_and_of {i j : Nat} {vals : List Bool} {a b : Bool}
    (h1 : vals[i]? = some a) (h2 : vals[j]? = some b) :
    (G1Request.mk .and i j vals).spec = some (a && b) := by
  simp [spec, h1, h2]

theorem spec_or_of {i j : Nat} {vals : List Bool} {a b : Bool}
    (h1 : vals[i]? = some a) (h2 : vals[j]? = some b) :
    (G1Request.mk .or i j vals).spec = some (a || b) := by
  simp [spec, h1, h2]

theorem spec_and_oob {i j : Nat} {vals : List Bool}
    (h : vals[i]? = none ∨ vals[j]? = none) :
    (G1Request.mk .and i j vals).spec = none := by
  rcases h with h | h
  · simp [spec, h]
  · cases hi : vals[i]? <;> simp [spec, hi, h]

theorem spec_or_oob {i j : Nat} {vals : List Bool}
    (h : vals[i]? = none ∨ vals[j]? = none) :
    (G1Request.mk .or i j vals).spec = none := by
  rcases h with h | h
  · simp [spec, h]
  · cases hi : vals[i]? <;> simp [spec, hi, h]

/-- **Out-of-range selection is `none`.**  An index at or beyond the length of
the runtime value region never selects a value. -/
theorem getElem?_eq_none_of_length_le {i : Nat} {vals : List Bool}
    (h : vals.length ≤ i) : vals[i]? = none :=
  List.getElem?_eq_none h

/-- A violated arity-1 unused-field convention is `none`. -/
theorem spec_unused_field {t : G1Tag} (harity : t.arity = 1) (a1 a2 : Nat)
    (h : a2 ≠ 0) (vals : List Bool) :
    (G1Request.mk t a1 a2 vals).spec = none := by
  cases t <;> simp_all [spec, G1Tag.arity]

/-- **Non-canonical requests have no value.**  `spec` is `none` on every
request that violates the unused-field convention of its tag. -/
theorem spec_eq_none_of_not_canonical {r : G1Request} (h : ¬ r.Canonical) :
    r.spec = none := by
  rw [G1Request.canonical_iff] at h
  cases r with
  | mk tag a1 a2 vals =>
      cases tag
      case const =>
        by_cases h2 : a2 = 0
        · subst h2
          have ha : 2 ≤ a1 := by
            by_contra hcon
            refine h ⟨fun _ => rfl, fun _ => ?_⟩
            show a1 ≤ 1
            omega
          exact spec_const_out_of_convention a1 ha vals
        · simp [spec, h2]
      case input => simp_all [spec, G1Tag.arity]
      case not => simp_all [spec, G1Tag.arity]
      case and => simp_all [G1Tag.arity]
      case or => simp_all [G1Tag.arity]

/-- Partial indexing returns a value exactly in range. -/
theorem getElem?_isSome_iff {i : Nat} {vals : List Bool} :
    vals[i]?.isSome = true ↔ i < vals.length := by
  constructor
  · intro h
    by_contra hn
    have hnone : vals[i]? = none := List.getElem?_eq_none (by omega)
    simp [hnone] at h
  · intro hi
    rw [List.getElem?_eq_getElem hi]
    rfl

/-- Exact domain characterization of the pure semantics. -/
theorem spec_isSome_iff (r : G1Request) : r.spec.isSome = true ↔ r.WellFormed := by
  rcases r with ⟨tag, a1, a2, vals⟩
  cases tag with
  | input =>
      by_cases h2 : a2 = 0
      · subst a2
        simpa [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity]
          using (getElem?_isSome_iff (i := a1) (vals := vals))
      · simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity, h2]
  | const =>
      by_cases h2 : a2 = 0
      · subst a2
        by_cases h0 : a1 = 0
        · subst a1; simp [spec, WellFormed, operandsInBounds, canonical_iff,
            G1Tag.arity]
        · by_cases h1 : a1 = 1
          · subst a1; simp [spec, WellFormed, operandsInBounds, canonical_iff,
              G1Tag.arity]
          · simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity,
              h0, h1]
            omega
      · simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity, h2]
  | not =>
      by_cases h2 : a2 = 0
      · subst a2
        simpa [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity]
          using (getElem?_isSome_iff (i := a1) (vals := vals))
      · simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity, h2]
  | and =>
      simp only [spec]
      by_cases h1 : a1 < vals.length
      · rw [List.getElem?_eq_getElem h1]
        by_cases h2 : a2 < vals.length
        · rw [List.getElem?_eq_getElem h2]
          simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity,
            h1, h2]
        · have hn : vals[a2]? = none := List.getElem?_eq_none (by omega)
          simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity,
            h1, h2, hn]
      · have hn : vals[a1]? = none := List.getElem?_eq_none (by omega)
        simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity,
          h1, hn]
  | or =>
      simp only [spec]
      by_cases h1 : a1 < vals.length
      · rw [List.getElem?_eq_getElem h1]
        by_cases h2 : a2 < vals.length
        · rw [List.getElem?_eq_getElem h2]
          simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity,
            h1, h2]
        · have hn : vals[a2]? = none := List.getElem?_eq_none (by omega)
          simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity,
            h1, h2, hn]
      · have hn : vals[a1]? = none := List.getElem?_eq_none (by omega)
        simp [spec, WellFormed, operandsInBounds, canonical_iff, G1Tag.arity,
          h1, hn]

end G1Request

/-! ## The operand-2 value, and the residual bridge

Everything here is pure: `G1Request`, `Option Bool` and `G1Residual`.  No
configuration, no head, no step count, no finite context, no `G1Ctx`. -/

/-- **The operand-2 value pass A would start from.**  A binary gate selects it
out of the runtime value region; an arity-1 gate does not use operand 2 at all,
and the convention here pins its unused operand-2 value to `false`.  A function
of the pure request: nothing is read from a tape here, and no register, latch
or state field is referred to. -/
def g1OperandB (r : G1Request) : Option Bool :=
  if r.tag.arity = 2 then r.vals[r.arg2]? else some false

@[simp] theorem g1OperandB_and (a1 a2 : Nat) (vals : List Bool) :
    g1OperandB (G1Request.mk .and a1 a2 vals) = vals[a2]? := rfl

@[simp] theorem g1OperandB_or (a1 a2 : Nat) (vals : List Bool) :
    g1OperandB (G1Request.mk .or a1 a2 vals) = vals[a2]? := rfl

@[simp] theorem g1OperandB_input (a1 a2 : Nat) (vals : List Bool) :
    g1OperandB (G1Request.mk .input a1 a2 vals) = some false := rfl

@[simp] theorem g1OperandB_not (a1 a2 : Nat) (vals : List Bool) :
    g1OperandB (G1Request.mk .not a1 a2 vals) = some false := rfl

@[simp] theorem g1OperandB_const (a1 a2 : Nat) (vals : List Bool) :
    g1OperandB (G1Request.mk .const a1 a2 vals) = some false := rfl

/-- An arity-1 gate never selects an operand-2 value. -/
theorem g1OperandB_of_arity_one {r : G1Request} (h : r.tag.arity = 1) :
    g1OperandB r = some false := by
  simp [g1OperandB, h]

/-- A binary gate selects its operand-2 value out of the runtime region. -/
theorem g1OperandB_of_arity_two {r : G1Request} (h : r.tag.arity = 2) :
    g1OperandB r = r.vals[r.arg2]? := by
  simp [g1OperandB, h]

/-- **A well-formed request always has an operand-2 value.**  Discharges the
`hb` hypothesis of the bridge below without any machine assumption. -/
theorem g1OperandB_isSome_of_wellFormed {r : G1Request} (h : r.WellFormed) :
    ∃ b : Bool, g1OperandB r = some b := by
  rcases r with ⟨tag, a1, a2, vals⟩
  cases tag
  case input => exact ⟨false, rfl⟩
  case const => exact ⟨false, rfl⟩
  case not => exact ⟨false, rfl⟩
  case and =>
      have hb : a1 < vals.length ∧ a2 < vals.length := h.2
      exact ⟨vals[a2], by
        rw [g1OperandB_and]; exact List.getElem?_eq_getElem hb.2⟩
  case or =>
      have hb : a1 < vals.length ∧ a2 < vals.length := h.2
      exact ⟨vals[a2], by
        rw [g1OperandB_or]; exact List.getElem?_eq_getElem hb.2⟩

/-- **A well-formed non-`const` request always selects an operand-1 value.**
`const` is excluded because its `arg1` is the literal bit, not an index into
`vals`, so `operandsInBounds` says nothing about it. -/
theorem g1OperandA_isSome_of_wellFormed {r : G1Request} (h : r.WellFormed)
    (ht : r.tag ≠ .const) : ∃ a : Bool, r.vals[r.arg1]? = some a := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht ⊢
  cases tag
  case const => exact absurd rfl ht
  case input =>
      have ha : a1 < vals.length := h.2
      exact ⟨vals[a1], List.getElem?_eq_getElem ha⟩
  case not =>
      have ha : a1 < vals.length := h.2
      exact ⟨vals[a1], List.getElem?_eq_getElem ha⟩
  case and =>
      have ha : a1 < vals.length ∧ a2 < vals.length := h.2
      exact ⟨vals[a1], List.getElem?_eq_getElem ha.1⟩
  case or =>
      have ha : a1 < vals.length ∧ a2 < vals.length := h.2
      exact ⟨vals[a1], List.getElem?_eq_getElem ha.1⟩

/-- **`input` and `not`: the residual is the whole gate**, for **every** `b`,
since an arity-1 residual ignores operand 2. -/
theorem g1Residual_apply_spec_unary {r : G1Request}
    (ht : r.tag = .input ∨ r.tag = .not) {a res : Bool} (b : Bool)
    (ha : r.vals[r.arg1]? = some a) (hs : r.spec = some res) :
    (g1Residual r.tag b).apply a = res := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht ha hs
  rcases ht with rfl | rfl <;>
    · simp only [G1Request.spec] at hs
      split_ifs at hs with h2
      rw [ha] at hs
      simpa [G1Residual.apply] using hs

/-- **`and` and `or`: the operand-2 value collapses the gate.**  Both operands
are pure selector hypotheses. -/
theorem g1Residual_apply_spec_binary {r : G1Request}
    (ht : r.tag = .and ∨ r.tag = .or) {a b res : Bool}
    (ha : r.vals[r.arg1]? = some a) (hb : r.vals[r.arg2]? = some b)
    (hs : r.spec = some res) :
    (g1Residual r.tag b).apply a = res := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht ha hb hs
  rcases ht with rfl | rfl
  · rw [G1Request.spec_and_of ha hb] at hs
    simpa using hs
  · rw [G1Request.spec_or_of ha hb] at hs
    simpa using hs

/-- **The residual bridge.**  For every pass-A tag — every tag but `const` —
the residual determined by the tag and the operand-2 value, applied to the
operand-1 value, is exactly the pure specification of the gate.  This is a
statement about `G1Request.spec`, `g1Residual` and list indexing only; that an
interpreter latches `g1Residual r.tag b` and reads `r.vals[r.arg1]` off a tape
is a deferred, control-level claim made nowhere in this slice. -/
theorem g1Residual_apply_spec {r : G1Request} (ht : r.tag ≠ .const)
    {a b res : Bool} (ha : r.vals[r.arg1]? = some a)
    (hb : g1OperandB r = some b) (hs : r.spec = some res) :
    (g1Residual r.tag b).apply a = res := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht ha hb hs
  cases tag with
  | const => exact absurd rfl ht
  | input => exact g1Residual_apply_spec_unary (Or.inl rfl) b ha hs
  | not => exact g1Residual_apply_spec_unary (Or.inr rfl) b ha hs
  | and =>
      exact g1Residual_apply_spec_binary (Or.inl rfl) ha
        (by simpa using hb) hs
  | or =>
      exact g1Residual_apply_spec_binary (Or.inr rfl) ha
        (by simpa using hb) hs

/-- **The converse direction.**  On a canonical non-`const` request whose
operand selectors both succeed, the specification *is* the residual applied to
the operand-1 value. -/
theorem g1Spec_eq_residual_apply {r : G1Request} (hc : r.Canonical)
    (ht : r.tag ≠ .const) {a b : Bool} (ha : r.vals[r.arg1]? = some a)
    (hb : g1OperandB r = some b) :
    r.spec = some ((g1Residual r.tag b).apply a) := by
  rw [G1Request.canonical_iff] at hc
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht ha hb hc ⊢
  cases tag with
  | const => exact absurd rfl ht
  | input =>
      rw [show a2 = 0 from hc.1 rfl]
      simpa using ha
  | not =>
      rw [show a2 = 0 from hc.1 rfl]
      simp only [G1Request.spec_not, g1Residual_not_apply, ha]
      rfl
  | and =>
      rw [g1Residual_and_apply]
      exact G1Request.spec_and_of ha (by simpa using hb)
  | or =>
      rw [g1Residual_or_apply]
      exact G1Request.spec_or_of ha (by simpa using hb)

/-! ### Selection is not an external input

`a` is whatever `r.vals[r.arg1]?` selected out of the *single on-tape runtime
value region*.  The two arity-1 rows below say exactly that the residual
returns that selected value (resp. its negation) — no circuit input, no
`SLGate.input` correspondence and no claim about where `vals` came from. -/

/-- **`input` copies the selected runtime value.** -/
theorem g1Residual_input_selects (i : Nat) (vals : List Bool) (b : Bool)
    {a : Bool} (ha : vals[i]? = some a) :
    (g1Residual .input b).apply a = a ∧
      (G1Request.mk .input i 0 vals).spec = some a := by
  refine ⟨rfl, ?_⟩
  simp [G1Request.spec_input, ha]

/-- **`not` negates the selected runtime value.** -/
theorem g1Residual_not_selects (i : Nat) (vals : List Bool) (b : Bool)
    {a : Bool} (ha : vals[i]? = some a) :
    (g1Residual .not b).apply a = !a ∧
      (G1Request.mk .not i 0 vals).spec = some (!a) := by
  refine ⟨rfl, ?_⟩
  simp [G1Request.spec_not, ha]

/-- **The `const` exclusion is load-bearing, not decoration.**  On the canonical
`const` request `⟨const, 1, 0, [false, false]⟩` all three selector hypotheses of
`g1Residual_apply_spec` hold with `a = b = false` and `res = true`, yet the
filler `const` row of `g1Residual` gives `false`.  Dropping `r.tag ≠ .const`
from the bridge would therefore make it false. -/
theorem g1Residual_const_apply_ne_spec :
    (G1Request.mk .const 1 0 [false, false]).Canonical ∧
      (G1Request.mk .const 1 0 [false, false]).vals[
        (G1Request.mk .const 1 0 [false, false]).arg1]? = some false ∧
      g1OperandB (G1Request.mk .const 1 0 [false, false]) = some false ∧
      (G1Request.mk .const 1 0 [false, false]).spec = some true ∧
      (g1Residual (G1Request.mk .const 1 0 [false, false]).tag false).apply
        false ≠ true := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- **The pure S1a capstone: all five tags, exactly.**  There is no machine-run
capstone available in a pure slice, so this is the capstone: the bridge for
every pass-A tag, the four exact truth-table rows it composes to, the `const`
filler row, and the concrete canonical `const` request that shows the filler
would be *wrong* if the fifth tag were ever admitted.  Every conjunct is an
equation between `G1Request.spec`, `g1Residual` and list indexing; none of them
mentions a configuration, a step, a head or a state. -/
theorem g1Residual_spec_capstone :
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
  ⟨fun _ _ _ _ ht ha hb hs => g1Residual_apply_spec ht ha hb hs,
    g1Residual_apply_table, g1Residual_const_filler,
    ⟨G1Request.mk .const 1 0 [false, false], rfl, rfl, rfl, rfl, rfl,
      by decide⟩⟩

namespace G1Request

/-! ## Named examples

Every tag, a successful `false` result, an out-of-range rejection and a
non-canonical rejection. -/

theorem g1_example_const_false :
    (G1Request.mk .const 0 0 []).spec = some false := rfl

theorem g1_example_const_true :
    (G1Request.mk .const 1 0 []).spec = some true := rfl

/-- A successful `false` result from a two-operand gate. -/
theorem g1_example_and_false :
    (G1Request.mk .and 0 1 [true, false]).spec = some false := rfl

theorem g1_example_and_true :
    (G1Request.mk .and 0 1 [true, true]).spec = some true := rfl

theorem g1_example_or_true :
    (G1Request.mk .or 0 1 [false, true]).spec = some true := rfl

theorem g1_example_or_false :
    (G1Request.mk .or 0 1 [false, false]).spec = some false := rfl

theorem g1_example_input_false :
    (G1Request.mk .input 1 0 [true, false]).spec = some false := rfl

theorem g1_example_not_false :
    (G1Request.mk .not 0 0 [true]).spec = some false := rfl

/-- Out-of-range operand. -/
theorem g1_example_oob : (G1Request.mk .input 5 0 [true, false]).spec = none :=
  rfl

/-- Canonical unused fields do not make an out-of-range operand meaningful. -/
theorem g1_example_canonical_oob_not_wellFormed :
    (G1Request.mk .input 5 0 [true, false]).Canonical ∧
      ¬ (G1Request.mk .input 5 0 [true, false]).WellFormed := by
  constructor
  · rfl
  · simp [WellFormed, operandsInBounds]

/-- Violated unused-field convention. -/
theorem g1_example_unused :
    (G1Request.mk .not 0 1 [true]).spec = none := rfl

/-- A `const` field outside the unary bit convention. -/
theorem g1_example_const_noncanonical :
    (G1Request.mk .const 2 0 []).spec = none := rfl

end G1Request

end Pnp3.Internal.PsubsetPpoly.TM
