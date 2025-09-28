import Pnp2.BoolFunc
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support
import Pnp2.Sunflower.RSpread
import Pnp2.Boolcube

open Classical
open Finset
open Agreement
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)
open Sunflower

namespace Cover2

lemma support_subset_core_of_agree_on_core
    {n t : ℕ} (S : SunflowerFam n t)
    {f : BFunc n}
    (hAgree : ∀ x y : Boolcube.Point n,
        (∀ i ∈ S.core, x i = y i) → f x = f y) :
    BoolFunc.support f ⊆ S.core := by
  classical
  intro i hi
  by_contra hi_core
  rcases BoolFunc.mem_support_iff.mp hi with ⟨x, hx⟩
  let y : Boolcube.Point n := BoolFunc.Point.update (n := n) x i (!(x i))
  have hagree : ∀ j ∈ S.core, x j = y j := by
    intro j hj
    by_cases hji : j = i
    · have hj' : i ∈ S.core := by simpa [hji] using hj
      exact (hi_core hj').elim
    · simpa [y, BoolFunc.Point.update, hji]
  have hxy : f x = f y := hAgree x y hagree
  have hx' : f x ≠ f y := by simpa [y] using hx
  exact hx' hxy

lemma eval_agree_of_support_subset_core
    {n t : ℕ} (S : SunflowerFam n t)
    {f : BFunc n} {x y : Boolcube.Point n}
    (h_support : BoolFunc.support f ⊆ S.core)
    (hxy : ∀ i ∈ S.core, x i = y i) :
    f x = f y := by
  classical
  have h_agree : ∀ i ∈ BoolFunc.support f, x i = y i := by
    intro i hi
    exact hxy i (h_support hi)
  simpa using
    (BoolFunc.eval_eq_of_agree_on_support (f := f) (x := x) (y := y) h_agree)

lemma sunflower_step {n : ℕ} (F : Family n) (p t : ℕ)
    (hp : 0 < p) (ht : 2 ≤ t)
    (h_big : Sunflower.threshold p t < (Family.supports F).card)
    (h_support : ∀ f ∈ F, (BoolFunc.support f).card = p)
    (h_agree :
      ∀ (S : SunflowerFam n t), S.petals ⊆ Family.supports F →
        ∀ A ∈ S.petals,
          ∃ f ∈ F, BoolFunc.support f = A ∧
            (∀ x y : Boolcube.Point n,
                (∀ i ∈ S.core, x i = y i) → f x = f y))
    (h_true : ∀ f ∈ F, f (fun _ : Fin n => false) = true) :
    ∃ (R : Boolcube.Subcube n),
      ((F.filter fun f => ∀ x : Boolcube.Point n,
          Boolcube.Subcube.Mem R x → f x = true).card ≥ t) ∧
      1 ≤ Boolcube.Subcube.dim R := by
  classical
  let 𝓢 : Finset (Finset (Fin n)) := Family.supports F
  have h_sizes : ∀ s ∈ 𝓢, s.card = p := by
    intro s hs
    rcases Family.mem_supports.mp hs with ⟨f, hf, rfl⟩
    exact h_support f hf
  obtain ⟨S, hSsub⟩ : ∃ S : SunflowerFam n t, S.petals ⊆ 𝓢 := by
    have hbig' : 𝓢.card > Sunflower.threshold p t := by
      simpa [Sunflower.threshold] using h_big
    exact SunflowerFam.exists_of_large_family_classic
      (F := 𝓢) (w := p) (t := t) hp ht h_sizes hbig'
  have exists_f :
      ∀ A ∈ S.petals, ∃ f ∈ F, BoolFunc.support f = A ∧
        (∀ x y : Boolcube.Point n,
            (∀ i ∈ S.core, x i = y i) → f x = f y) :=
    h_agree S hSsub
  classical
  choose f hfF hfSupp hfAgree using exists_f
  let x₀ : Boolcube.Point n := fun _ => false
  let R : Boolcube.Subcube n := Boolcube.Subcube.fromPoint x₀ S.core
  have h_filter_ge :
      (F.filter fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true).card ≥ t := by
    let im :=
      S.petals.attach.image (fun a : {A // A ∈ S.petals} => f a.1 a.2)
    have h_inj_aux :
        Function.Injective (fun a : {A // A ∈ S.petals} => f a.1 a.2) := by
      intro a₁ a₂ h_eq
      have hsup := congrArg BoolFunc.support h_eq
      have hA : a₁.1 = a₂.1 := by
        simpa [hfSupp _ a₁.2, hfSupp _ a₂.2] using hsup
      exact Subtype.ext hA
    have h_im_card : im.card = t := by
      have hcard :=
        Finset.card_image_of_injective
          (s := S.petals.attach)
          (f := fun a : {A // A ∈ S.petals} => f a.1 a.2)
          h_inj_aux
      simpa [im, Finset.card_attach, S.tsize] using hcard
    have h_sub :
        im ⊆ F.filter (fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true) := by
      intro g hg
      rcases Finset.mem_image.1 hg with ⟨a, ha, rfl⟩
      have hgF : f a.1 a.2 ∈ F := hfF _ a.2
      have htrue : ∀ x : Boolcube.Point n, R.Mem x → (f a.1 a.2) x = true := by
        intro x hx
        have h_agree_core : ∀ i ∈ S.core, x i = x₀ i := by
          intro i hi
          have hx' := hx i
          simpa [R, Boolcube.Subcube.fromPoint, hi] using hx'
        have hx_eq : (f a.1 a.2) x = (f a.1 a.2) x₀ :=
          hfAgree _ a.2 x x₀ h_agree_core
        have hx0_true : (f a.1 a.2) x₀ = true := by
          have hfmem : f a.1 a.2 ∈ F := hfF _ a.2
          simpa [x₀] using h_true _ hfmem
        simpa [hx_eq] using hx0_true
      have : f a.1 a.2 ∈ F.filter
          (fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true) := by
        have : f a.1 a.2 ∈ F ∧
            (∀ x : Boolcube.Point n, R.Mem x → (f a.1 a.2) x = true) :=
          ⟨hgF, htrue⟩
        simpa using this
      simpa using this
    have h_le := Finset.card_le_card h_sub
    have :
        t ≤ (F.filter fun g => ∀ x : Boolcube.Point n, R.Mem x → g x = true).card := by
      simpa [im, h_im_card] using h_le
    exact this
  have h_dim : 1 ≤ Boolcube.Subcube.dim R := by
    have hpet_card : ∀ P ∈ S.petals, P.card = p := by
      intro P hP; exact h_sizes P (hSsub hP)
    have h_one_lt : 1 < S.petals.card :=
      let htwo : 2 ≤ S.petals.card := by simpa [S.tsize] using ht
      lt_of_lt_of_le (by decide : 1 < 2) htwo
    obtain ⟨P₁, hP₁, P₂, hP₂, hP₁P₂⟩ := Finset.one_lt_card.mp h_one_lt
    have hcoord : ∃ i ∈ P₁, i ∉ S.core := by
      have hcard : P₂.card = P₁.card := by
        simpa [hpet_card P₁ hP₁, hpet_card P₂ hP₂]
      exact SunflowerFam.exists_coord_not_core_of_two_petals
        (S := S) (P₁ := P₁) (P₂ := P₂) hP₁ hP₂ hcard hP₁P₂
    rcases hcoord with ⟨i, hiP₁, hi_not⟩
    have h_core_lt_n : S.core.card < n := by
      have hsubset : S.core ⊆ (Finset.univ : Finset (Fin n)) := by simp
      have hne : S.core ≠ (Finset.univ : Finset (Fin n)) := by
        intro h; exact hi_not (by simpa [h] using (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      have hssub : S.core ⊂ (Finset.univ : Finset (Fin n)) :=
        (Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hne⟩
      simpa using (Finset.card_lt_card hssub)
    have hpos : 0 < n - S.core.card := Nat.sub_pos_of_lt h_core_lt_n
    have hdim' : 1 ≤ n - S.core.card := Nat.succ_le_of_lt hpos
    have hdim_eq : Boolcube.Subcube.dim R = n - S.core.card := by
      simpa [R] using (Boolcube.Subcube.dim_fromPoint (x := x₀) (K := S.core))
    exact hdim_eq.symm ▸ hdim'
  exact ⟨R, h_filter_ge, h_dim⟩

end Cover2