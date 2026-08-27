import Complexity.TMVerifier.TuringToolkit.GateOneEncoding

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
