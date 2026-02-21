import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Models.Model_PartialMCSP

/-!
  pnp3/Counting/CircuitCounting.lean

  Enumerates tree-shaped circuits of bounded size and provides cardinality bounds.
  Used by the Shannon counting argument in MCSPGapLocality.
-/

namespace Pnp3
namespace Counting

open Models

/-!
  ### Circuit enumeration

  `circuitsOfSizeAtMost n s` is a Finset containing every `Circuit n` of size ≤ s.
  It may also contain circuits of larger size (overapproximation), but the
  membership lemma guarantees the inclusion direction we need.
-/

/-- Finset overapproximating all circuits of size ≤ `s` on `n` inputs. -/
def circuitsOfSizeAtMost (n s : Nat) : Finset (Circuit n) :=
  match s with
  | 0 => ∅
  | s + 1 =>
    let prev := circuitsOfSizeAtMost n s
    prev
    ∪ (Finset.univ.image Circuit.input
       ∪ ({Circuit.const true, Circuit.const false} : Finset _))
    ∪ (prev.image Circuit.not
       ∪ ((prev ×ˢ prev).image (fun (p : Circuit n × Circuit n) => Circuit.and p.1 p.2))
       ∪ ((prev ×ˢ prev).image (fun (p : Circuit n × Circuit n) => Circuit.or p.1 p.2)))

/-- Every circuit of size ≤ s is in `circuitsOfSizeAtMost n s`. -/
theorem mem_circuitsOfSizeAtMost {n : Nat} (C : Circuit n) (s : Nat)
    (hs : C.size ≤ s) : C ∈ circuitsOfSizeAtMost n s := by
  induction C generalizing s with
  | input i =>
    cases s with
    | zero => simp [Circuit.size] at hs
    | succ s =>
      unfold circuitsOfSizeAtMost
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  | const b =>
    cases s with
    | zero => simp [Circuit.size] at hs
    | succ s =>
      unfold circuitsOfSizeAtMost
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      cases b with
      | true => exact Finset.mem_insert.mpr (Or.inl rfl)
      | false => exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  | not c ih =>
    cases s with
    | zero => simp [Circuit.size] at hs
    | succ s =>
      have hc : c.size ≤ s := by simp [Circuit.size] at hs; omega
      unfold circuitsOfSizeAtMost
      apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨c, ih s hc, rfl⟩
  | and c₁ c₂ ih₁ ih₂ =>
    cases s with
    | zero => simp [Circuit.size] at hs
    | succ s =>
      have h₁ : c₁.size ≤ s := by simp [Circuit.size] at hs; omega
      have h₂ : c₂.size ≤ s := by simp [Circuit.size] at hs; omega
      unfold circuitsOfSizeAtMost
      apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(c₁, c₂),
        Finset.mem_product.mpr ⟨ih₁ s h₁, ih₂ s h₂⟩, rfl⟩
  | or c₁ c₂ ih₁ ih₂ =>
    cases s with
    | zero => simp [Circuit.size] at hs
    | succ s =>
      have h₁ : c₁.size ≤ s := by simp [Circuit.size] at hs; omega
      have h₂ : c₂.size ≤ s := by simp [Circuit.size] at hs; omega
      unfold circuitsOfSizeAtMost
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(c₁, c₂),
        Finset.mem_product.mpr ⟨ih₁ s h₁, ih₂ s h₂⟩, rfl⟩

/-!
  ### Cardinality bound

  The cardinality of `circuitsOfSizeAtMost n s` is bounded by `circuitCountBound n s`.
-/

private lemma card_union3_le {α : Type*} [DecidableEq α]
    (A B C : Finset α) :
    (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := by
  have h1 := Finset.card_union_le (A ∪ B) C
  have h2 := Finset.card_union_le A B
  linarith

theorem card_circuitsOfSizeAtMost_le (n s : Nat) :
    (circuitsOfSizeAtMost n s).card ≤ circuitCountBound n s := by
  induction s with
  | zero =>
    simp [circuitsOfSizeAtMost, circuitCountBound]
  | succ s ih =>
    unfold circuitsOfSizeAtMost circuitCountBound
    set prev := circuitsOfSizeAtMost n s with hprev_def
    -- The structure is (prev ∪ base) ∪ (nots ∪ ands ∪ ors)
    set base := Finset.univ.image Circuit.input
      ∪ ({Circuit.const true, Circuit.const false} : Finset _)
    set nots := prev.image Circuit.not
    set ands := (prev ×ˢ prev).image (fun (p : Circuit n × Circuit n) => Circuit.and p.1 p.2)
    set ors := (prev ×ˢ prev).image (fun (p : Circuit n × Circuit n) => Circuit.or p.1 p.2)
    -- Bound each piece
    have h_base : base.card ≤ n + 2 := by
      have h_inp : (Finset.univ.image Circuit.input (α := Fin n)).card ≤ n := by
        calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
          _ = n := by simp
      have h_con : ({Circuit.const true, Circuit.const false} : Finset (Circuit n)).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      linarith [Finset.card_union_le
        (Finset.univ.image Circuit.input (α := Fin n))
        ({Circuit.const true, Circuit.const false} : Finset (Circuit n))]
    have h_nots : nots.card ≤ prev.card :=
      Finset.card_image_le
    have h_ands : ands.card ≤ prev.card ^ 2 := by
      calc ands.card ≤ (prev ×ˢ prev).card := Finset.card_image_le
        _ = prev.card * prev.card := Finset.card_product prev prev
        _ = prev.card ^ 2 := (sq prev.card).symm
    have h_ors : ors.card ≤ prev.card ^ 2 := by
      calc ors.card ≤ (prev ×ˢ prev).card := Finset.card_image_le
        _ = prev.card * prev.card := Finset.card_product prev prev
        _ = prev.card ^ 2 := (sq prev.card).symm
    -- Combine: use explicit upper bounds at each step
    have h_prev_base : (prev ∪ base).card ≤ prev.card + base.card :=
      Finset.card_union_le prev base
    have h_nao : (nots ∪ ands ∪ ors).card ≤ nots.card + ands.card + ors.card :=
      card_union3_le nots ands ors
    have h_total : (prev ∪ base ∪ (nots ∪ ands ∪ ors)).card
        ≤ prev.card + base.card + nots.card + ands.card + ors.card := by
      have := Finset.card_union_le (prev ∪ base) (nots ∪ ands ∪ ors)
      linarith
    calc (prev ∪ base ∪ (nots ∪ ands ∪ ors)).card
        ≤ prev.card + base.card + nots.card + ands.card + ors.card := h_total
      _ ≤ circuitCountBound n s + (n + 2) + circuitCountBound n s
          + circuitCountBound n s ^ 2 + circuitCountBound n s ^ 2 := by
          have := ih  -- prev.card ≤ circuitCountBound n s
          nlinarith [h_base, h_nots, h_ands, h_ors]
      _ = 2 * circuitCountBound n s ^ 2 + 2 * circuitCountBound n s + (n + 2) := by ring

end Counting
end Pnp3
