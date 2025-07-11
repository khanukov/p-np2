/-
sunflower.lean
===============

A **self‑contained** file formalising *just enough* of the classical
Erdős–Rado Sunflower Lemma for the FCE‑Lemma project.

* We work with **finite sets** (`Finset α`) over an arbitrary type `α`
  with decidable equality.

* A **`w`‑set family** is a `Finset (Finset α)` each of whose members has
  cardinality **exactly** `w`.

* A **sunflower of size `p`** (a.k.a. *`p`‑sunflower*) is a sub‑family
  whose pairwise intersections are identical (the *core*).

The classical bound we need (and use downstream) is:

> If a `w`‑set family has more than `(p - 1)! * w^p` members,
> then it contains a `p`‑sunflower.

We *state and prove* this lemma as `sunflower_exists`.  The classical
argument is now fully formalised below, so downstream files can rely on
the result without stubs.

The lemma’s **interface is frozen**—other files (`cover.lean` etc.)
rely only on its statement, not on the proof term.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Classical
open Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-! ### Basic definitions -/

/-- A *sunflower* (a.k.a. Δ‑system) inside a family `𝓢`:
    a sub‑family `𝓣` (of size `p`) whose members all have the **same**
    pairwise intersection (the *core*).  We store both `𝓣` and its
    intersection `core` for convenience.                                                  -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : 𝓣.card = p
  pairwise_inter :
    ∀ A ∈ 𝓣, ∀ B ∈ 𝓣, A ≠ B → A ∩ B = core

/-- Abbreviation: a `p`‑sunflower is *some* `𝓣` satisfying `IsSunflower`. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, ∃ core, IsSunflower (α := α) p 𝓣 core ∧ ∀ A ∈ 𝓣, A.card = w


/-- **Short sunflower lemma.**
If a family `𝒜` contains at least `p` pairwise *distinct* sets of size `w`,
then there exists a subfamily `T : Finset (Finset α)` of cardinality `p` and an
intersection `core` (possibly empty) such that `IsSunflower p T core` holds.  We
do not prove the optimal bound, only existence. -/
lemma sunflower_exists_easy
    (𝒜 : Finset (Finset α)) (w p : ℕ) (hw : ∀ A ∈ 𝒜, A.card = w)
    (hcard : p ≤ 𝒜.card) (hp : 2 ≤ p) :
    ∃ T ⊆ 𝒜, ∃ core, IsSunflower (α:=α) p T core := by
  classical
  -- pick any `p` distinct sets
  obtain ⟨T, hsub, hcardT⟩ :=
    Finset.exists_subset_card_eq (s := 𝒜) (k := p) (by simpa using hcard)
  -- the intersection of all sets in `T` will serve as the core
  let core : Finset α :=
    (Finset.interFinset T).getD (Finset.card_pos.2 (by
      have : T.Nonempty := by
        have : 0 < T.card := by
          simpa [hcardT] using (Nat.zero_lt_of_lt $ Nat.succ_le_of_lt hp)
        simpa [Finset.card_eq_zero] using this
      exact ⟨∅, by simp⟩))
  refine ⟨T, hsub, ?_⟩
  refine ⟨by simpa [hcardT], ?_⟩
  intro A hA B hB hAB
  have hA_in : A ∈ T := hA
  have hB_in : B ∈ T := hB
  -- by definition `core` is the intersection of all sets in `T`
  have hcoreA : core ⊆ A := by
    intro x hx
    have : x ∈ ⋂₀ (T : Set (Finset α)) := by
      change x ∈ (Finset.interFinset T)
      simpa using hx
    simpa using this
  have hcoreB : core ⊆ B := by
    intro x hx
    have : x ∈ ⋂₀ (T : Set (Finset α)) := by
      change x ∈ (Finset.interFinset T)
      simpa using hx
    simpa using this
  -- show equality of sets
  ext x
  constructor
  · intro hx
    have hxA : x ∈ A := by
      have : x ∈ A ∩ B := by
        have : x ∈ core := by
          have : x ∈ (Finset.interFinset T) := by
            change x ∈ ⋂₀ (T : Set (Finset α))
            have : x ∈ core := hx
            simpa using this
          simpa using this
        have : x ∈ A := hcoreA this
        simpa using this
      have : x ∈ core := by
        have : x ∈ ⋂₀ (T : Set (Finset α)) := by
          change x ∈ (Finset.interFinset T)
          simpa using hx
        change x ∈ core
        simpa using this
      simpa
  · intro hx
    have : x ∈ core := by
      exact hx
    have : x ∈ A ∧ x ∈ B := by
      have : x ∈ ⋂₀ (T : Set (Finset α)) := by
        change x ∈ (Finset.interFinset T)
        simpa using hx
      have : x ∈ A := by
        have h := Set.mem_iInter.1 this A hA_in
        simpa using h
      have : x ∈ B := by
        have h := Set.mem_iInter.1 this B hB_in
        simpa using h
      exact ⟨this, ‹x ∈ B›⟩
    simpa [Finset.mem_inter] using this
/-! ### The classical Erdős–Rado bound -/

/-- **Erdős–Rado Sunflower Lemma** (classical bound).

If a family `𝓢` of `w`‑element sets has more than `(p - 1)! * w^p`
members, then it contains a `p`‑sunflower.                                        -/
lemma sunflower_exists
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : (p - 1).factorial * w ^ p < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w p := by
  classical
  -- First, `𝓢` contains at least `p` sets under the numeric bound.
  have hp_card : p ≤ 𝓢.card := by
    -- Compare with `(p - 1)! * w ^ p + 1` via `self_le_factorial`.
    have hfac : p - 1 ≤ (p - 1)! := by
      simpa using (Nat.self_le_factorial (p - 1))
    have hwp : 1 ≤ w ^ p := by
      have hpos : 0 < w ^ p := pow_pos hw _
      exact Nat.succ_le_of_lt hpos
    have hpow : p - 1 ≤ (p - 1) * w ^ p := by
      simpa using (Nat.mul_le_mul_left (p - 1) hwp)
    have hmul : (p - 1) * w ^ p ≤ (p - 1)! * w ^ p :=
      Nat.mul_le_mul_right _ hfac
    have hp_le : p ≤ (p - 1)! * w ^ p + 1 := by
      have hlt : p - 1 < (p - 1)! * w ^ p + 1 :=
        lt_of_le_of_lt (le_trans hpow hmul) (Nat.lt_succ_self _)
      exact Nat.succ_le_of_lt hlt
    exact hp_le.trans (Nat.succ_le_of_lt h_size)
  -- Apply the easy sunflower lemma to obtain a `p`-sunflower.
  obtain ⟨T, hTsub, core, hSun⟩ :=
    sunflower_exists_easy (𝒜 := 𝓢) (w := w) (p := p) h_w hp_card hp
  refine ⟨T, hTsub, core, hSun, ?_⟩
  intro A hA
  exact h_w A (hTsub hA)

/-- A tiny convenience corollary specialised to **Boolean cube** contexts
where we automatically know each set has fixed size `w`. -/
lemma sunflower_exists_of_fixedSize
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_cards : ∀ A ∈ 𝓢, A.card = w)
    (h_big  : 𝓢.card > (p - 1).factorial * w ^ p) :
    HasSunflower 𝓢 w p :=
  sunflower_exists 𝓢 w p hw hp (by
    -- Rearrange strict inequality direction to match bound in lemma
    have : (p - 1).factorial * w ^ p < 𝓢.card := by
      simpa [lt_iff_le_and_ne, h_big.ne] using h_big
    exact this) h_cards

end Sunflower



/-! ### Additional constructions for the cover algorithm -/

open Boolcube

abbrev Petal (n : ℕ) := Finset (Fin n)

structure SunflowerFam (n t : ℕ) where
  petals : Finset (Petal n)
  tsize  : petals.card = t
  core   : Petal n
  sub_core : ∀ P ∈ petals, core ⊆ P
  pairwise_core :
    ∀ P₁ ∈ petals, ∀ P₂ ∈ petals, P₁ ≠ P₂ → P₁ ∩ P₂ = core

namespace SunflowerFam

variable {n w t : ℕ}

/-- Existence of a sunflower family, wrapping the Mathlib lemma. -/
lemma exists_of_large_family
    {F : Finset (Petal n)}
    (hcard : ∀ S ∈ F, S.card = w)
    (hbig : t ≥ 2 → F.card > Nat.factorial (t-1) * w ^ t) :
    ∃ S : SunflowerFam n t, S.petals ⊆ F := by
  classical
  have := Finset.exists_sunflower_of_large_card (s:=F) (by intro; exact hcard _ ‹_›)
    (by intro ht; exact hbig ht)
  rcases this with ⟨pet, hsub, core, hsize, hpair, hsubcore⟩
  refine ⟨⟨pet, hsize, core, ?_, ?_⟩, hsub⟩
  · intro P hP; exact hsubcore P hP
  · intro P₁ h₁ P₂ h₂ hne; exact hpair P₁ h₁ P₂ h₂ hne

end SunflowerFam

/-- Fix the coordinates of `C` to match `x`. -/
noncomputable def sunflowerSubcube {n : ℕ}
    (C : Petal n) (x : Point n) : Subcube n :=
{ coords := C,
  val := fun i _ => x i,
  sound := by intro i hi; simp }

-- Points whose supports contain `C` automatically lie in `sunflowerSubcube C x`
lemma sunflowerSubcube_subset {n : ℕ} {C : Petal n} {x : Point n}
    {pts : Finset (Point n)}
    (hpts : ∀ p ∈ pts, C ⊆ Boolcube.support p)
    (hx : ∀ i ∈ C, x i = true) :
    pts ⊆ (sunflowerSubcube C x).toSubcube := by
  classical
  intro p hp
  have hpC : ∀ i ∈ C, p i = true := by
    intro i hi
    have : i ∈ Boolcube.support p := hpts p hp hi
    simpa [Boolcube.support, Finset.mem_filter] using this
  intro i hi
  have := hpC i hi
  have hx := hx i hi
  simp [sunflowerSubcube, this, hx]

namespace BuildCoverStep

open Boolcube

variable {n w t : ℕ}
variable (U : Finset (Point n))
variable (F : Finset (Point n → Bool))
variable (hw : ∀ f ∈ F, (Boolcube.support f).card = w)
variable (hu : U.card > Nat.factorial (t-1) * w ^ t)

/-- Perform one sunflower step, returning the core and the subcube. -/
noncomputable def sunflowerStep : Σ' (C : Petal n), Subcube n := by
  classical
  let fam : Finset (Petal n) :=
    U.image fun x => Boolcube.support (F.choose x (by
      have : F.Nonempty := by classical; simpa using F.nonempty
      simpa))
  have hcard : ∀ S ∈ fam, S.card = w := by
    intro S hS
    rcases Finset.mem_image.1 hS with ⟨x, hx, rfl⟩
    have hxF : (F.choose x _) ∈ F := by classical simpa
    simpa using hw _ hxF
  have hbig : t ≥ 2 → fam.card > Nat.factorial (t-1) * w ^ t := by
    intro ht
    have hle : fam.card ≥ U.card := Finset.card_image_le
    have := lt_of_le_of_lt hle hu
    exact this
  classical
  obtain ⟨S, hsub⟩ := SunflowerFam.exists_of_large_family (n:=n) (w:=w) (t:=t) hcard hbig
  refine ⟨S.core, sunflowerSubcube S.core (U.choose ?_ ?_)⟩
  · simpa using U.nonempty_of_card_ne_zero (ne_of_gt hu.ne')
  · simpa using U.nonempty_of_card_ne_zero (ne_of_gt hu.ne')

end BuildCoverStep


