import Pnp2.Boolcube
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Classical
open Finset
open Boolcube (Point Subcube)

/-!
This module isolates the arithmetic bounds used in the cover construction.
Moving these numeric lemmas out of `cover2.lean` keeps the main file focused
on the combinatorial aspects.  The central quantity is `mBound`, an explicit
function controlling the size of intermediate rectangle sets.  The lemmas
below collect basic estimates and monotonicity properties which are heavily
used throughout the cover development.
-/

namespace Cover2

/--
`mBound n h` is a coarse upper bound on the number of rectangles generated
when covering a family of Boolean functions on `n` variables with entropy
budget `h`.  It intentionally grows very quickly; the factor `2^(10*h)` keeps
the arithmetic simple while still dominating all combinatorial overheads.
-/
@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

/-- `mBound` is trivially nonnegative. -/
lemma mBound_nonneg (n h : ℕ) : 0 ≤ mBound n h := by
  exact Nat.zero_le _

/-- A linear upper bound showing that `mBound` dominates `2*h + n` when
`n` is positive.  The proof performs a case split on `h` and massages the
result using basic arithmetic reasoning. -/
lemma numeric_bound (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ mBound n h := by
  classical
  cases h with
  | zero =>
      have h0 : 2 * 0 + n ≤ mBound n 0 := by
        have hmul := Nat.mul_le_mul_left n (show (1 : ℕ) ≤ 2 from by decide)
        simpa [mBound, two_mul, Nat.mul_comm, one_mul] using hmul
      simpa using h0
  | succ h =>
      have hlinear : (2 * (h + 1) + n : ℕ) ≤ 2 * n * (h + 1 + 2) := by
        nlinarith [hn]
      have hpow : (2 : ℕ) ≤ 2 ^ (10 * (h + 1)) := by
        have hbase : (2 : ℕ) ≤ 2 ^ 10 := by decide
        have hexp : 10 ≤ 10 * (h + 1) := by
          have hx : (1 : ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le _)
          have hx' : (10 : ℕ) * 1 ≤ 10 * (h + 1) := Nat.mul_le_mul_left 10 hx
          set_option linter.unnecessarySimpa false in
          simpa [Nat.mul_one] using hx'
        exact hbase.trans (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hexp)
      have : 2 * (h + 1) + n ≤ n * (h + 1 + 2) * 2 ^ (10 * (h + 1)) := by
        calc
          2 * (h + 1) + n ≤ 2 * n * (h + 1 + 2) := hlinear
          _ = (n * (h + 1 + 2)) * 2 := by ring
          _ ≤ (n * (h + 1 + 2)) * 2 ^ (10 * (h + 1)) :=
            Nat.mul_le_mul_left _ hpow
      simpa [mBound] using this

/-- A convenience wrapper around `numeric_bound` for positive `n`. -/
lemma numeric_bound_pos (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ mBound n h :=
  numeric_bound (n := n) (h := h) hn

/-- The exponential factor `2^(10*h)` is at most `mBound`. -/
lemma pow_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ^ (10 * h) ≤ mBound n h := by
  have hpos : 0 < n * (h + 2) := by
    have hpos' : 0 < h + 2 := Nat.succ_pos _
    exact Nat.mul_pos hn hpos'
  have hfactor : 1 ≤ n * (h + 2) := Nat.succ_le_of_lt hpos
  have := Nat.mul_le_mul_left (2 ^ (10 * h)) hfactor
  simpa [mBound, one_mul] using this

/-- A simpler power bound obtained by weakening the exponent. -/
lemma pow_le_mBound_simple (n h : ℕ) (hn : 0 < n) :
    2 ^ h ≤ mBound n h := by
  -- The exponent `10 * h` dominates `h`, so `2 ^ h ≤ 2 ^ (10 * h)`.
  have hexp : h ≤ 10 * h := by
    have hbase : (1 : ℕ) ≤ 10 := by decide
    have := Nat.mul_le_mul_left h hbase
    simpa [Nat.mul_comm] using this
  have hpow : 2 ^ h ≤ 2 ^ (10 * h) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hexp
  -- Combine with the main bound on the power factor.
  exact hpow.trans (pow_le_mBound (n := n) (h := h) hn)

/-- `mBound` is positive whenever `n` is positive. -/
lemma mBound_pos (n h : ℕ) (hn : 0 < n) :
    0 < mBound n h := by
  -- Each factor in the definition is positive.
  have hpos₁ : 0 < h + 2 := Nat.succ_pos _
  have hpos₂ : 0 < 2 ^ (10 * h) := pow_pos (by decide) _
  have hmul : 0 < n * (h + 2) := Nat.mul_pos hn hpos₁
  have := Nat.mul_pos hmul hpos₂
  simpa [mBound] using this

/-- The bound always exceeds `2` once the dimension is positive. -/
lemma two_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hh2 : 2 ≤ h + 2 := by
    have := Nat.zero_le h
    exact Nat.succ_le_succ (Nat.succ_le_succ this)
  have hfactor : 2 ≤ n * (h + 2) := by
    have := Nat.mul_le_mul hn1 hh2
    simpa [one_mul] using this
  have hpow : 1 ≤ 2 ^ (10 * h) :=
    Nat.succ_le_of_lt (pow_pos (by decide) _)
  have := Nat.mul_le_mul hfactor hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-- For `h ≥ 1` the bound also dominates `3`. -/
lemma three_le_mBound (n h : ℕ) (hn : 0 < n) (hh : 1 ≤ h) :
    3 ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  -- Establish `3 ≤ n * (h + 2)` using `hn` and `hh`.
  have h3 : 3 ≤ h + 2 := by
    have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
    have : (3 : ℤ) ≤ h + 2 := by nlinarith
    exact_mod_cast this
  have hfac1 : h + 2 ≤ n * (h + 2) := by
    have := Nat.mul_le_mul_right (h + 2) hn1
    simpa [one_mul] using this
  have hfac : 3 ≤ n * (h + 2) := le_trans h3 hfac1
  -- Multiply by the positive power factor.
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have := Nat.mul_le_mul hfac hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-- `mBound` vanishes when there are no variables. -/
@[simp] lemma mBound_zero (h : ℕ) : mBound 0 h = 0 := by
  simp [mBound]

/-- `mBound` collapses to zero iff the dimension vanishes. -/
lemma mBound_eq_zero_iff {n h : ℕ} : mBound n h = 0 ↔ n = 0 := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have hpos : 0 < mBound (Nat.succ n) h :=
        mBound_pos (n := Nat.succ n) (h := h) (Nat.succ_pos _)
      have hneq : mBound (Nat.succ n) h ≠ 0 := ne_of_gt hpos
      constructor
      · intro hzero; exact False.elim (hneq hzero)
      · intro hfalse; cases hfalse

/-- `mBound` grows monotonically in the entropy budget. -/
lemma mBound_mono {n : ℕ} : Monotone (mBound n) := by
  intro h₁ h₂ hh
  dsimp [mBound]
  have hfac : n * (h₁ + 2) ≤ n * (h₂ + 2) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right hh 2)
  have hpow : 2 ^ (10 * h₁) ≤ 2 ^ (10 * h₂) := by
    have := Nat.mul_le_mul_left 10 hh
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) this
  exact Nat.mul_le_mul hfac hpow

/-- Monotonicity in the dimension parameter. -/
lemma mBound_mono_left {n₁ n₂ h : ℕ} (hn : n₁ ≤ n₂) :
    mBound n₁ h ≤ mBound n₂ h := by
  dsimp [mBound]
  have hfac : n₁ * (h + 2) ≤ n₂ * (h + 2) :=
    Nat.mul_le_mul_right (h + 2) hn
  exact Nat.mul_le_mul hfac (le_rfl)

/-- Increasing the budget by one never decreases the bound. -/
lemma mBound_le_succ (n h : ℕ) : mBound n h ≤ mBound n (h + 1) :=
  mBound_mono (n := n) (Nat.le_succ h)

/-- Doubling the bound for budget `h` stays below the bound for `h + 1`. -/
lemma two_mul_mBound_le_succ (n h : ℕ) :
    2 * mBound n h ≤ mBound n (h + 1) := by
  -- We compare the factors of `mBound` for budgets `h` and `h + 1`.
  -- The linear factor grows monotonically with `h`.
  have hfac : h + 2 ≤ h + 3 := Nat.le_succ (h + 2)
  -- The exponential term grows by a factor of at least `2 ^ 9`.
  have hexp : 10 * h + 1 ≤ 10 * h + 10 := by
    -- `1 ≤ 10` lets us shift by `10 * h` on both sides.
    have h1 : (1 : ℕ) ≤ 10 := by decide
    exact add_le_add_left h1 (10 * h)
  -- Use monotonicity of exponentiation with a positive base.
  have hpow : 2 ^ (10 * h + 1) ≤ 2 ^ (10 * h + 10) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp
  -- Combine growth of both factors.
  have hmul := Nat.mul_le_mul hfac hpow
  -- Multiply by the common dimension factor.
  have hmain := Nat.mul_le_mul_left n hmul
  -- Rewrite both sides into the desired `mBound` form.
  have lhs_eq : n * ((h + 2) * 2 ^ (10 * h + 1)) = 2 * mBound n h := by
    simp [mBound, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have rhs_eq : n * ((h + 3) * 2 ^ (10 * h + 10)) = mBound n (h + 1) := by
    have : 10 * (h + 1) = 10 * h + 10 := by ring
    -- `Nat.mul_left_comm` is unnecessary here; removing it satisfies the
    -- linter without altering the simplification.
    simp [mBound, pow_add, this, Nat.mul_comm, Nat.mul_assoc]
  simpa [lhs_eq, rhs_eq] using hmain

/--
If two finite sets of rectangles each respect the current budget, then their
union respects the next budget.  This numeric helper underpins the recursive
construction of covers.
-/
lemma card_union_mBound_succ {n h : ℕ} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : R₁.card ≤ mBound n h) (h₂ : R₂.card ≤ mBound n h) :
    (R₁ ∪ R₂).card ≤ mBound n (h + 1) := by
  classical
  have hsum : (R₁ ∪ R₂).card ≤ R₁.card + R₂.card := by
    simpa using (Finset.card_union_le (s := R₁) (t := R₂))
  have hdouble : R₁.card + R₂.card ≤ 2 * mBound n h := by
    have := add_le_add h₁ h₂
    simpa [two_mul] using this
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hsum.trans <| hdouble.trans hstep

/-- Adding one extra rectangle keeps us within the next budget. -/
lemma one_add_mBound_le_succ {n h : ℕ} (hn : 0 < n) :
    mBound n h + 1 ≤ mBound n (h + 1) := by
  have hpos : 1 ≤ mBound n h := by
    have := mBound_pos (n := n) (h := h) hn
    exact Nat.succ_le_of_lt this
  have hdouble : mBound n h + 1 ≤ 2 * mBound n h := by
    have htwice : mBound n h + 1 ≤ mBound n h + mBound n h :=
      Nat.add_le_add_left hpos (mBound n h)
    simpa [two_mul] using htwice
  have hstep := two_mul_mBound_le_succ (n := n) (h := h)
  exact hdouble.trans hstep

/-- Convenient wrapper around `card_union_mBound_succ` for adding a singleton. -/
lemma card_union_singleton_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R}).card ≤ mBound n (h + 1) := by
  classical
  have hsum : (Rset ∪ {R}).card ≤ Rset.card + 1 := by
    simpa using (Finset.card_union_le (s := Rset) (t := ({R} : Finset (Subcube n))) )
  have hbound : Rset.card + 1 ≤ mBound n h + 1 :=
    Nat.add_le_add_right hcard 1
  have hstep := one_add_mBound_le_succ (n := n) (h := h) hn
  exact hsum.trans <| hbound.trans hstep

/-- Inserting an element into a set of rectangles grows the bound appropriately. -/
lemma card_insert_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (insert R Rset).card ≤ mBound n (h + 1) := by
  classical
  have hunion : insert R Rset = Rset ∪ {R} := by
    ext x; by_cases hx : x = R <;> by_cases hxset : x ∈ Rset <;>
      simp [hx, hxset, Finset.mem_insert, Finset.mem_union]
  simpa [hunion] using
    (card_union_singleton_mBound_succ (n := n) (h := h)
      (Rset := Rset) (R := R) hcard hn)

/-- A small helper: inserting two rectangles still fits into the next budget. -/
lemma card_union_pair_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) :
    (Rset ∪ {R₁, R₂}).card ≤ mBound n (h + 1) := by
  classical
  let Rpair : Finset (Subcube n) := {R₁, R₂}
  have hpair_le_two : Rpair.card ≤ 2 := by
    by_cases h : R₁ = R₂
    · subst h; simp [Rpair]
    · simp [Rpair, h]
  have hpair_bound : Rpair.card ≤ mBound n h :=
    le_trans hpair_le_two (two_le_mBound (n := n) (h := h) hn)
  have := card_union_mBound_succ (n := n) (h := h)
      (R₁ := Rset) (R₂ := Rpair) hcard hpair_bound
  simpa [Rpair, Finset.union_comm, Finset.union_assoc] using this

/-- And similarly for inserting three rectangles at once. -/
lemma card_union_triple_mBound_succ {n h : ℕ}
    {Rset : Finset (Subcube n)} {R₁ R₂ R₃ : Subcube n}
    (hcard : Rset.card ≤ mBound n h) (hn : 0 < n) (hh : 1 ≤ h) :
    (Rset ∪ {R₁, R₂, R₃}).card ≤ mBound n (h + 1) := by
  classical
  let Rtriple : Finset (Subcube n) := {R₁, R₂, R₃}
  have htriple_le_three : Rtriple.card ≤ 3 := by
    have hcard_insert := Finset.card_insert_le (s := {R₁, R₂}) (a := R₃)
    have hpair_le_two : ({R₁, R₂} : Finset (Subcube n)).card ≤ 2 := by
      by_cases h : R₁ = R₂
      · subst h; simp
      · simp [h]
    have h := le_trans hcard_insert (Nat.add_le_add_right hpair_le_two 1)
    have hrepr : insert R₃ ({R₁, R₂} : Finset (Subcube n)) = {R₁, R₂, R₃} := by
      ext x; by_cases hx : x = R₃ <;> by_cases hx1 : x = R₁ <;> by_cases hx2 : x = R₂ <;>
        simp [hx, hx1, hx2, Finset.mem_insert, Finset.mem_singleton, or_comm]
    simpa [Rtriple, hrepr] using h
  have htriple_bound : Rtriple.card ≤ mBound n h :=
    le_trans htriple_le_three (three_le_mBound (n := n) (h := h) hn hh)
  have := card_union_mBound_succ (n := n) (h := h)
      (R₁ := Rset) (R₂ := Rtriple) hcard htriple_bound
  simpa [Rtriple, Finset.union_comm, Finset.union_assoc] using this

end Cover2

namespace Cover2

/-- The family of subcubes on `n` variables has cardinality `3^n`.  Each
subcube is described by choosing, for every coordinate, either `none`
(coordinate is free) or `some b` (coordinate fixed to `b`). -/
lemma card_subcube (n : ℕ) :
    Fintype.card (Boolcube.Subcube n) = 3 ^ n := by
  classical
  -- Equip `Subcube n` with the obvious equivalence to functions `Fin n → Option Bool`.
  let e : Boolcube.Subcube n ≃ (Fin n → Option Bool) :=
    { toFun := fun C => C.fix,
      invFun := fun f => ⟨f⟩,
      left_inv := by intro C; cases C; rfl,
      right_inv := by intro f; rfl }
  have hcard := Fintype.card_congr e
  have hpow : Fintype.card (Fin n → Option Bool) = 3 ^ n := by
    classical
    simpa [Fintype.card_fin, Fintype.card_option] using
      Fintype.card_fun (Fin n) (Option Bool)
  simpa [hpow] using hcard

/-- A coarse arithmetic bound showing that the total number of subcubes is
dominated by `mBound` once the entropy budget `h` grows linearly with the
dimension.  The factor `5` is deliberately slack to keep the argument simple. -/
lemma card_subcube_le_mBound {n h : ℕ}
    (hn : 0 < n) (hlarge : n ≤ 5 * h) :
    Fintype.card (Boolcube.Subcube n) ≤ mBound n h := by
  classical
  -- Rewrite the cardinality via the explicit formula `3^n`.
  have hcard := card_subcube (n := n)
  -- `3^n ≤ 4^n = 2^(2*n)` since `3 ≤ 4`.
  have h3le4 : (3 : ℕ) ≤ 4 := by decide
  have hpow1 : 3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left h3le4 n
  -- Rewrite `4^n` as `2^(2*n)` using `pow_mul`.
  have h4 : 4 ^ n = 2 ^ (2 * n) := by
    have : (4 : ℕ) = 2 ^ 2 := by decide
    simpa [this, Nat.mul_comm] using (pow_mul (2 : ℕ) 2 n).symm
  have hpow1' : 3 ^ n ≤ 2 ^ (2 * n) := by simpa [h4] using hpow1
  -- Relate the exponents `2*n` and `10*h` using the assumption `n ≤ 5*h`.
  have hineq : 2 * n ≤ 10 * h := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_left 2 hlarge
  have hpow2 : 2 ^ (2 * n) ≤ 2 ^ (10 * h) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hineq
  have hpow : 3 ^ n ≤ 2 ^ (10 * h) := hpow1'.trans hpow2
  -- Finally invoke the generic bound `2^(10*h) ≤ mBound n h`.
  have hmb : 2 ^ (10 * h) ≤ mBound n h := pow_le_mBound (n := n) (h := h) hn
  have hfinal : 3 ^ n ≤ mBound n h := hpow.trans hmb
  simpa [hcard] using hfinal

end Cover2

