import Pnp.BoolFunc
import Pnp.Boolcube
import Pnp.Agreement
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Classical
open BoolFunc
open Finset
open Agreement

namespace Cover

/-! ## Numeric bound -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

/-- A very rough numeric bound used in the roadmap.  Since `mBound n h`
grows exponentially in `h`, it trivially dominates `2 * h + n` as soon as
`n` is non‑zero.  The proof splits on `h = 0` and `h ≥ 1` and then uses
basic arithmetic and `nlinarith` for the linear part. -/
lemma numeric_bound (n h : ℕ) (hn : 0 < n) : 2 * h + n ≤ mBound n h := by
  classical
  cases h with
  | zero =>
      -- `mBound n 0 = 2 * n` and `n ≤ 2 * n`
      have h0 : 2 * 0 + n ≤ mBound n 0 := by
        have hmul := Nat.mul_le_mul_left n (show (1 : ℕ) ≤ 2 from by decide)
        simpa [mBound, two_mul, Nat.mul_comm, one_mul] using hmul
      simpa using h0
  | succ h =>
      -- For `h + 1`, first bound `2 * (h + 1) + n` by `2 * n * (h + 1 + 2)`
      have hlinear : (2 * (h + 1) + n : ℕ) ≤ 2 * n * (h + 1 + 2) := by
        nlinarith [hn]
      -- Next, use that `2 ≤ 2 ^ (10 * (h + 1))`
      have hpow : (2 : ℕ) ≤ 2 ^ (10 * (h + 1)) := by
        have hbase : (2 : ℕ) ≤ 2 ^ 10 := by decide
        have hexp : 10 ≤ 10 * (h + 1) := by
          have hx : (1 : ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le _)
          have hx' : (10 : ℕ) * 1 ≤ 10 * (h + 1) := Nat.mul_le_mul_left 10 hx
          set_option linter.unnecessarySimpa false in
          simpa [Nat.mul_one] using hx'
        exact hbase.trans (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hexp)
      -- Putting everything together
      have :
        2 * (h + 1) + n ≤ n * (h + 1 + 2) * 2 ^ (10 * (h + 1)) := by
        calc
          2 * (h + 1) + n ≤ 2 * n * (h + 1 + 2) := hlinear
          _ = (n * (h + 1 + 2)) * 2 := by
            ring
          _ ≤ (n * (h + 1 + 2)) * 2 ^ (10 * (h + 1)) := by
            exact Nat.mul_le_mul_left _ hpow
      simp at this
      exact this

/-! ## Auxiliary predicates -/

variable {n : ℕ} (F : Family n)

/-- `x` is **not yet covered** by `Rset`. -/
def NotCovered (Rset : Finset (Subcube n)) (x : Point n) : Prop :=
  ∀ R ∈ Rset, ¬ x ∈ₛ R

@[simp] lemma notCovered_empty (x : Point n) :
    NotCovered (Rset := (∅ : Finset (Subcube n))) x := by
  intro R hR
  -- `hR` is impossible since the set is empty
  simp at hR

lemma NotCovered.monotone {R₁ R₂ : Finset (Subcube n)} (hsub : R₁ ⊆ R₂)
    {x : Point n} (hx : NotCovered (Rset := R₂) x) :
    NotCovered (Rset := R₁) x := by
  intro R hR
  exact hx R (hsub hR)

/-- The set of all uncovered 1-inputs (together with their functions). -/
@[simp]
def uncovered (F : Family n) (Rset : Finset (Subcube n)) : Set ((BFunc n) × Point n) :=
  {p | p.1 ∈ F ∧ p.1 p.2 = true ∧ NotCovered (Rset := Rset) p.2}

/-- Optionally returns the *first* uncovered ⟨f, x⟩. -/
noncomputable
def firstUncovered (F : Family n) (Rset : Finset (Subcube n)) : Option ((BFunc n) × Point n) :=
  if h : (uncovered (F := F) (Rset := Rset)).Nonempty then
    some h.some
  else
    none

set_option linter.unusedSimpArgs false in
@[simp] lemma firstUncovered_none_iff (R : Finset (Subcube n)) :
    firstUncovered (F := F) R = none ↔ uncovered (F := F) R = ∅ := by
  classical
  by_cases h : (uncovered (F := F) (Rset := R)).Nonempty
  · simp [firstUncovered, h, Set.nonempty_iff_ne_empty]
  · simp [firstUncovered, h, Set.nonempty_iff_ne_empty]

/-- All `1`-inputs of `F` lie in some rectangle of `Rset`. -/
@[simp] def AllOnesCovered (F : Family n) (Rset : Finset (Subcube n)) : Prop :=
  ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R

lemma AllOnesCovered.superset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered F R₁) (hsub : R₁ ⊆ R₂) :
    AllOnesCovered F R₂ := by
  intro f hf x hx
  rcases h₁ f hf x hx with ⟨R, hR, hxR⟩
  exact ⟨R, hsub hR, hxR⟩

lemma AllOnesCovered.union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (_h₁ : AllOnesCovered F R₁) (h₂ : AllOnesCovered F R₂) :
    AllOnesCovered F (R₁ ∪ R₂) := by
  intro f hf x hx
  by_cases hx1 : ∃ R ∈ R₁, x ∈ₛ R
  · rcases hx1 with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union] using Or.inl hR, hxR⟩
  · rcases h₂ f hf x hx with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union, hx1] using Or.inr hR, hxR⟩

lemma mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F) (hsub : R₂ ⊆ R₁) :
    ∀ R ∈ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  exact h₁ R (hsub hR)

lemma mono_union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (h₂ : ∀ R ∈ R₂, Subcube.monochromaticForFamily R F) :
    ∀ R ∈ R₁ ∪ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  rcases Finset.mem_union.mp hR with h | h
  · exact h₁ R h
  · exact h₂ R h

@[simp] lemma AllOnesCovered.empty {F : Family n} :
    AllOnesCovered (F := F) (∅ : Finset (Subcube n)) ↔
      ∀ f ∈ F, ∀ x, f x = true → False := by
  classical
  constructor
  · intro h f hf x hx
    rcases h f hf x hx with ⟨R, hR, _hxR⟩
    simp at hR
  · intro h f hf x hx
    exact False.elim (h f hf x hx)

/-! ### Uncovered inputs and a simple measure

The following lemmas are ports of helper results from the legacy
development.  They will be useful for the inductive analysis of the
cover construction. -/


/-- A coarse termination measure used in the cover recursion.  The
first component tracks the remaining entropy budget `h`, while the
second counts currently uncovered `1`-inputs. -/

lemma uncovered_subset_of_union_singleton {F : Family n}
    {Rset : Finset (Subcube n)} {R : Subcube n} :
    uncovered F (Rset ∪ {R}) ⊆ uncovered F Rset := by
  classical
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  intro S hS
  exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)



end Cover
