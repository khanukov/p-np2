--
--  Pnp2/Sunflower/Sunflower.lean
--
--  Classical sunflower lemma: axiomatized with the standard threshold
--  `(p - 1)^w * w!`.  We provide the basic definitions together with a
--  direct proof for the two-petal case; the general combinatorial lemma
--  is recorded as an axiom for now.
--
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card
import Pnp2.Boolcube

open Classical Finset

set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

noncomputable section

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-- A `p`-sunflower inside a family `𝓢` consists of a subfamily `𝓣` of
cardinality `p` whose pairwise intersections all coincide with a set
`core`. -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : 𝓣.card = p
  pairwise_inter :
    ∀ ⦃A⦄, A ∈ 𝓣 → ∀ ⦃B⦄, B ∈ 𝓣 → A ≠ B → A ∩ B = core

/-- A family `𝓢` has a `p`-sunflower of width `w` if it contains a
subfamily with the sunflower property and all petals have size `w`. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, ∃ core, IsSunflower (α := α) p 𝓣 core ∧ ∀ A ∈ 𝓣, A.card = w

/-! ### Two petals: explicit proof -/

/-- For two petals the sunflower lemma becomes completely elementary: any
family containing at least two sets already forms a `2`-sunflower.  We
record this special case with a direct proof so that small instances do
not depend on the general combinatorial argument. -/
lemma sunflower_exists_two
    (𝓢 : Finset (Finset α)) (w : ℕ) (hw : 0 < w)
    (h_large : 1 < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w 2 := by
  classical
  -- Choose two distinct members of the family.
  have hpos : 0 < 𝓢.card := lt_trans Nat.zero_lt_one h_large
  obtain ⟨A, hA⟩ := Finset.card_pos.mp hpos
  obtain ⟨B, hB, hAB⟩ := Finset.exists_ne_of_one_lt_card h_large A
  -- The petals of the sunflower are the two chosen sets.
  refine ⟨{A, B}, ?_, ?_⟩
  · intro X hX
    have hx : X = A ∨ X = B := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hX
    cases hx with
    | inl hXA => simpa [hXA] using hA
    | inr hXB => simpa [hXB] using hB
  · refine ⟨A ∩ B, ?_, ?_⟩
    · -- Proof of the sunflower structure.
      have hA_notB : A ∉ ({B} : Finset (Finset α)) := by
        simpa [Finset.mem_singleton] using hAB.symm
      refine ⟨by
        simpa [Finset.card_singleton, hA_notB] using
          (Finset.card_insert_of_notMem hA_notB), ?_⟩
      -- The pairwise intersection property is immediate.
      intro X hX Y hY hXY
      have hX' : X = A ∨ X = B := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hX
      have hY' : Y = A ∨ Y = B := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hY
      cases hX' with
      | inl hx =>
          cases hY' with
          | inl hy => cases hXY (by simpa [hx, hy])
          | inr hy => simpa [hx, hy, Finset.inter_comm]
      | inr hx =>
          cases hY' with
          | inl hy => simpa [hx, hy, Finset.inter_comm]
          | inr hy => cases hXY (by simpa [hx, hy])
    · -- Finally each petal has cardinality `w`.
      intro X hX
      have hx : X = A ∨ X = B := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hX
      cases hx with
      | inl hx => simpa [hx] using h_w A hA
      | inr hx => simpa [hx] using h_w B hB

/-! ### Classical sunflower lemma (axiomatized) -/

/-- **Erdős–Rado sunflower lemma** (axiom).  If a finite family of
`w`-sets has more than `(p - 1)^w * w!` members, then it contains a
`p`-sunflower.  A complete combinatorial proof will be provided in a
future revision. -/
axiom sunflower_exists_classic
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : (p - 1) ^ w * Nat.factorial w < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w p

/-- Convenient wrapper for the sunflower lemma when the family is
already known to consist of `w`-sets. -/
lemma sunflower_exists_of_fixedSize
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_cards : ∀ A ∈ 𝓢, A.card = w)
    (h_big  : 𝓢.card > (p - 1) ^ w * Nat.factorial w) :
    HasSunflower 𝓢 w p :=
  sunflower_exists_classic 𝓢 w p hw hp
    (by simpa using h_big) h_cards

/-! ## Structures for the cover algorithm -/

open Boolcube

abbrev Petal (n : ℕ) := Finset (Fin n)

/-- Data of a sunflower family in the Boolean cube. -/
structure SunflowerFam (n t : ℕ) where
  petals : Finset (Petal n)
  tsize  : petals.card = t
  core   : Petal n
  sub_core : ∀ P ∈ petals, core ⊆ P
  pairwise_core :
    ∀ P₁ ∈ petals, ∀ P₂ ∈ petals, P₁ ≠ P₂ → P₁ ∩ P₂ = core

namespace SunflowerFam

variable {n w t : ℕ}

/-- From a sufficiently large family of `w`-subsets we can extract a
`t`-sunflower.  This is a thin wrapper around the classical lemma above
adapted to the `SunflowerFam` structure. -/
lemma exists_of_large_family_classic
    {F : Finset (Petal n)}
    (hw : 0 < w) (ht : 2 ≤ t)
    (hcard : ∀ S ∈ F, S.card = w)
    (hbig : F.card > (t - 1) ^ w * Nat.factorial w) :
    ∃ S : SunflowerFam n t, S.petals ⊆ F := by
  classical
  -- obtain the abstract sunflower using the axiom
  have hsun : HasSunflower (α := Fin n) F w t :=
    sunflower_exists_classic (𝓢 := F) (w := w) (p := t) hw ht hbig hcard
  rcases hsun with ⟨pet, hsub, core, hSun, hcards⟩
  rcases hSun with ⟨hsize, hpair⟩
  -- show the core is contained in every petal
  have hsub_core : ∀ P ∈ pet, core ⊆ P := by
    intro P hP
    have h_two : 1 < pet.card := by
      have : 2 ≤ pet.card := by simpa [hsize] using ht
      exact lt_of_lt_of_le (by decide : 1 < 2) this
    obtain ⟨Q, hQ, hne⟩ := Finset.exists_ne_of_one_lt_card h_two P
    have hPQ := hpair (A := P) hP (B := Q) hQ (Ne.symm hne)
    simpa [hPQ] using (Finset.inter_subset_left : P ∩ Q ⊆ P)
  refine ⟨⟨pet, hsize, core, hsub_core, ?_⟩, hsub⟩
  intro P₁ h₁ P₂ h₂ hne
  exact hpair (A := P₁) h₁ (B := P₂) h₂ hne

/-! ### Auxiliary facts about sunflower families -/

lemma petals_nonempty {S : SunflowerFam n t} (ht : 0 < t) :
    S.petals.Nonempty := by
  rw [← Finset.card_pos]
  rw [S.tsize]
  exact ht

/-- If a sunflower family contains two distinct petals of equal
cardinality, then the core is strictly smaller than each of those petals. -/
lemma core_card_lt_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    S.core.card < P₁.card := by
  classical
  have hsub : S.core ⊆ P₁ := S.sub_core _ h₁
  have hle : S.core.card ≤ P₁.card := Finset.card_le_card hsub
  have hneq : S.core.card ≠ P₁.card := by
    intro hEq
    have hcore_eq : S.core = P₁ :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hEq])
    have hsubset : P₁ ⊆ P₂ := by
      have htmp : P₁ ∩ P₂ = P₁ := by
        simpa [hcore_eq] using S.pairwise_core P₁ h₁ P₂ h₂ hne
      have hsubset_inter : P₁ ∩ P₂ ⊆ P₂ := Finset.inter_subset_right
      simpa [htmp] using hsubset_inter
    have hcardle : P₂.card ≤ P₁.card := by simpa [hcard]
    have : P₁ = P₂ := Finset.eq_of_subset_of_card_le hsubset hcardle
    exact hne this
  exact lt_of_le_of_ne hle hneq

/-- Reformulation of the previous lemma as a strict subset. -/
lemma core_ssubset_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    S.core ⊂ P₁ := by
  classical
  have hsub : S.core ⊆ P₁ := S.sub_core _ h₁
  have hneq : S.core ≠ P₁ := by
    intro hEq
    have hlt := core_card_lt_of_two_petals (S := S)
      (P₁ := P₁) (P₂ := P₂) h₁ h₂ hcard hne
    simpa [hEq] using hlt
  exact (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hneq⟩

/-- If a sunflower family contains two distinct petals of equal
cardinality, there exists an element of one petal outside the core. -/
lemma exists_coord_not_core_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    ∃ i ∈ P₁, i ∉ S.core := by
  classical
  have hssub : S.core ⊂ P₁ :=
    core_ssubset_of_two_petals (S := S)
      (P₁ := P₁) (P₂ := P₂) h₁ h₂ hcard hne
  rcases Finset.exists_of_ssubset hssub with ⟨i, hiP₁, hiNot⟩
  exact ⟨i, hiP₁, hiNot⟩

end SunflowerFam

end Sunflower

end

