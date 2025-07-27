-- acc_mcsp_sat.lean
-- ==================
--
-- Outline of the meet-in-the-middle SAT algorithm for `ACC⁰ ∘ MCSP`.
-- This module gathers a few definitions and lemma stubs that would
-- connect the cover from the Family Collision–Entropy Lemma
-- (Lemma B) with a subexponential SAT algorithm.
-- All statements are currently placeholders and the proofs are omitted.

import Pnp2.BoolFunc
import Pnp2.canonical_circuit
import Mathlib.Data.MvPolynomial
import Mathlib.Data.ZMod.Basic

open Classical

namespace ACCSAT

-- Placeholder type for polynomials over `𝔽₂` in `n` variables.
-- In a finished development this would be replaced by the
-- actual `Polynomial` type from `Mathlib` instantiated with
-- the finite field `𝔽₂`.
/-- Polynomials in `n` variables over `𝔽₂`. -/
abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

/-- Razborov–Smolensky: every `ACC⁰` circuit can be expressed as a
    low-degree polynomial over `𝔽₂`.  The bound on the degree is
    schematic and stated in big‑O form. -/
lemma acc_circuit_poly {n d : ℕ} (C : Boolcube.Circuit n)
    (hdepth : True := by trivial) :
    ∃ P : Polynomial n, True := by
  -- A real proof would translate `C` into a polynomial and
  -- bound the degree.  We merely return the zero polynomial.
  refine ⟨0, ?_⟩
  trivial

/-- Split an `N`‑bit vector into `k` left bits and `ℓ` right bits
    (`N = k + ℓ`).  The helper functions merely project the
    appropriate coordinates. -/
def leftBits (N k ℓ : ℕ) (h : N = k + ℓ)
    (x : Fin N → Bool) : Fin k → Bool :=
  fun i => x (Fin.castAdd ℓ i)

def rightBits (N k ℓ : ℕ) (h : N = k + ℓ)
    (x : Fin N → Bool) : Fin ℓ → Bool := by
  subst h
  have hcomm : ℓ + k = k + ℓ := Nat.add_comm _ _
  exact fun j => x (Fin.cast hcomm (j.addNat k))

/-- Merge a left and a right bit vector into a single vector of length
    `k + ℓ`.  The result places the `k` left bits first followed by the
    `ℓ` right bits. -/
def mergeBits (k ℓ : ℕ) (xL : Fin k → Bool) (xR : Fin ℓ → Bool) :
    Fin (k + ℓ) → Bool :=
  fun i =>
    if h : (i : ℕ) < k then
      xL ⟨i, h⟩
    else
      let hle : k ≤ (i : ℕ) := le_of_not_lt h
      let hlt : (i : ℕ) - k < ℓ := by
        have hi : (i : ℕ) < k + ℓ := i.is_lt
        have hi' : k + ((i : ℕ) - k) < k + ℓ := by
          simpa [Nat.add_sub_of_le hle] using hi
        exact Nat.lt_of_add_lt_add_left hi'
      xR ⟨(i : ℕ) - k, hlt⟩

/-- Taking the left half of a merged vector recovers the original left
    component. -/
lemma leftBits_mergeBits {k ℓ : ℕ} (xL : Fin k → Bool) (xR : Fin ℓ → Bool) :
    leftBits (N := k + ℓ) k ℓ rfl (mergeBits k ℓ xL xR) = xL := by
  funext i
  dsimp [leftBits, mergeBits]
  have hi : ((Fin.castAdd ℓ i : Fin (k + ℓ)) : ℕ) < k := by
    simpa using i.is_lt
  simp [hi]

/-- Taking the right half of a merged vector recovers the original right
    component. -/
lemma rightBits_mergeBits {k ℓ : ℕ} (xL : Fin k → Bool) (xR : Fin ℓ → Bool) :
    rightBits (N := k + ℓ) k ℓ rfl (mergeBits k ℓ xL xR) = xR := by
  funext j
  dsimp [rightBits, mergeBits]
  have hnot : ¬((Fin.cast (Nat.add_comm ℓ k) (j.addNat k) : Fin (k + ℓ)) : ℕ) < k :=
    by
      -- The value of `j.addNat k` is `j + k`, hence not `< k`.
      simpa using not_lt_of_ge (Nat.le_add_left k j)
  have hsub :
      ((Fin.cast (Nat.add_comm ℓ k) (j.addNat k) : Fin (k + ℓ)) : ℕ) - k = j := by
    -- Casting does not change the underlying value.
    simp [Fin.addNat]
  have hlt :
      ((Fin.cast (Nat.add_comm ℓ k) (j.addNat k) : Fin (k + ℓ)) : ℕ) - k < ℓ := by
    -- Bounds follow from the definition of `addNat`.
    simpa [hsub] using j.is_lt
  simp [hnot, hsub, hlt]

/-! Merging the results of `leftBits` and `rightBits` reconstructs the
original vector.  This lemma complements `leftBits_mergeBits` and
`rightBits_mergeBits` and will be useful for sanity checks. -/
lemma mergeBits_left_right {k ℓ : ℕ} (x : Fin (k + ℓ) → Bool) :
    mergeBits k ℓ
      (leftBits (N := k + ℓ) k ℓ rfl x)
      (rightBits (N := k + ℓ) k ℓ rfl x) = x := by
  funext i
  dsimp [mergeBits, leftBits, rightBits]
  by_cases h : (i : ℕ) < k
  · have hcast : Fin.castAdd ℓ ⟨i, h⟩ = i := by
      ext; simp
    simp [h, hcast]
  · have hle : k ≤ (i : ℕ) := le_of_not_lt h
    have hlt : (i : ℕ) - k < ℓ := by
      have hi : (i : ℕ) < k + ℓ := i.is_lt
      have hi' : k + ((i : ℕ) - k) < k + ℓ := by
        simpa [Nat.add_sub_of_le hle] using hi
      exact Nat.lt_of_add_lt_add_left hi'
    have hcast :
        (Fin.cast (Nat.add_comm ℓ k)
          (Fin.addNat ⟨(i : ℕ) - k, hlt⟩ k) : Fin (k + ℓ)) = i := by
      ext; simp [Fin.addNat, Nat.sub_add_cancel hle]
    simp [h, hcast, hle]


/-! ## SAT search via rectangle covers

`satSearchList` iterates over a list of subcubes and evaluates a Boolean
function on the canonical `sample` point of each cube.  If any evaluation
returns `true`, that witness is returned.  The wrapper `satSearch` applies
this procedure to a `Finset` of rectangles.  When the rectangles form a
monochromatic cover, this realises the shortened brute‑force SAT search
from the project overview. -/

open Boolcube

def satSearchList {n : ℕ} (f : BoolFun n) :
    List (Subcube n) → Option (Point n)
  | [] => none
  | R :: Rs =>
      if f (Subcube.sample R) then
        some (Subcube.sample R)
      else
        satSearchList Rs

/-- Search for a satisfying assignment using a rectangular cover.  The
    cubes are examined in an arbitrary order until a `true` evaluation is
    found.  Returns `none` if no sampled point satisfies `f`. -/
def satSearch {n : ℕ} (f : BoolFun n) (cover : Finset (Subcube n)) :
    Option (Point n) :=
  satSearchList f cover.toList

/-!
`satSearchList` simply scans the list of rectangles and returns the sample
point of the first cube whose colour under `f` is `true`.  The following
lemmas record the basic correctness properties used by `SATViaCover`.
-/

lemma satSearchList_sound {n : ℕ} {f : BoolFun n} {Rs : List (Subcube n)}
    {x : Point n} (hx : satSearchList f Rs = some x) :
    f x = true := by
  induction Rs with
  | nil =>
      -- The empty list cannot yield a witness.
      cases hx
  | cons R Rs ih =>
      dsimp [satSearchList] at hx
      by_cases hR : f (Subcube.sample R)
      · simp [hR] at hx; cases hx; simpa
      · simp [hR] at hx; exact ih hx

lemma satSearchList_exists_of_mem {n : ℕ} {f : BoolFun n}
    (Rs : List (Subcube n)) (R : Subcube n)
    (hmem : R ∈ Rs) (htrue : f (Subcube.sample R) = true) :
    ∃ x, satSearchList f Rs = some x := by
  induction Rs with
  | nil => cases hmem
  | cons R' Rs ih =>
      dsimp [satSearchList] at hmem
      by_cases h : f (Subcube.sample R') = true
      · -- The head cube already satisfies the predicate.
        exact ⟨Subcube.sample R', by simp [satSearchList, h]⟩
      · -- Continue searching in the tail.
        cases hmem with
        | head =>
            -- Contradiction with `htrue` since `R = R'`.
            exact absurd htrue h
        | tail hmem' =>
            obtain ⟨x, hx⟩ := ih hmem'
            exact ⟨x, by simp [satSearchList, h, hx]⟩

lemma satSearch_sound {n : ℕ} {f : BoolFun n}
    {cover : Finset (Subcube n)} {x : Point n}
    (hx : satSearch f cover = some x) : f x = true := by
  unfold satSearch at hx
  exact satSearchList_sound hx

lemma satSearch_complete {n : ℕ} {f : BoolFun n}
    (cover : Finset (Subcube n))
    (hmono : ∀ R ∈ cover, Subcube.monochromaticFor R f)
    (hcov : ∀ x, f x = true → ∃ R ∈ cover, x ∈ₛ R)
    (hx : ∃ x, f x = true) :
    ∃ x, satSearch f cover = some x ∧ f x = true := by
  classical
  rcases hx with ⟨x, hxtrue⟩
  obtain ⟨R, hR, hxR⟩ := hcov x hxtrue
  have htrue : f (Subcube.sample R) = true := by
    rcases hmono R hR with ⟨b, hb⟩
    have hb' : b = true := by
      have := hb x hxR
      simpa [hxtrue] using this
    have hxmem : Subcube.sample R ∈ₛ R := Subcube.sample_mem R
    have := hb (Subcube.sample R) hxmem
    simpa [hb'] using this
  have hmem := (List.mem_toList).2 hR
  obtain ⟨y, hy⟩ := satSearchList_exists_of_mem cover.toList R hmem htrue
  refine ⟨y, ?_, satSearchList_sound hy⟩
  simpa [satSearch] using hy



/-- Schematic definition of the meet‑in‑the‑middle SAT algorithm using
    a rectangular cover of the MCSP truth tables.  The algorithm loops
    over the rectangles and computes partial sums on the left and right
    halves.  Whenever a non‑zero product is detected the circuit is
    satisfiable.  This stub merely returns `false`. -/
noncomputable
def SATViaCover {N : ℕ}
    (Φ : Boolcube.Circuit N)
    (cover : Finset (Subcube N)) : Bool :=
  match satSearch (fun x => Circuit.eval Φ x) cover with
  | some _ => true
  | none   => false

lemma SATViaCover_correct {N : ℕ} (Φ : Boolcube.Circuit N)
    (cover : Finset (Subcube N))
    (hmono : ∀ R ∈ cover, Subcube.monochromaticFor R (Circuit.eval Φ))
    (hcov : ∀ x, Circuit.eval Φ x = true → ∃ R ∈ cover, x ∈ₛ R) :
    SATViaCover Φ cover = true ↔ ∃ x, Circuit.eval Φ x = true := by
  classical
  constructor
  · intro h
    unfold SATViaCover at h
    cases hx : satSearch (fun x => Circuit.eval Φ x) cover with
    | none =>
        simp [hx] at h
    | some x =>
        have hxtrue : (fun x => Circuit.eval Φ x) x = true :=
          satSearch_sound (f := fun x => Circuit.eval Φ x) (cover := cover) hx
        simp [hx] at h
        exact ⟨x, hxtrue⟩
  · intro hx
    obtain ⟨x, hxtrue⟩ := hx
    rcases satSearch_complete (cover := cover) (f := fun x => Circuit.eval Φ x)
        hmono hcov ⟨x, hxtrue⟩ with ⟨y, hy, _⟩
    unfold SATViaCover
    have := satSearch_sound (f := fun x => Circuit.eval Φ x) (cover := cover) hy
    simp [hy]

def SATViaCover_time {N : ℕ} (cover : Finset (Subcube N)) : ℕ :=
  cover.card

lemma SATViaCover_time_bound {N : ℕ} (cover : Finset (Subcube N)) :
    SATViaCover_time (cover := cover) ≤ cover.card := by
  rfl

/-!  A minimal reduction lemma showing how a hypothetical rectangular
cover could solve SAT for `ACC⁰ ∘ MCSP`.  The statement simply returns
an empty cover as a placeholder.  The legacy development included this
lemma; we port it here so that downstream files no longer depend on the
old namespace. -/
lemma sat_reduction {N : ℕ} (Φ : Boolcube.Circuit N)
    (hn : N ≥ Bound.n₀ 0) :
    ∃ cover : Finset (Subcube N),
      (∀ R ∈ cover, Subcube.monochromaticFor R (Circuit.eval Φ)) ∧
      (∀ x, Circuit.eval Φ x = true → ∃ R ∈ cover, x ∈ₛ R) ∧
      cover.card ≤ Nat.pow 2 (N / 100) := by
  classical
  let F : Boolcube.Family N := {fun x => Circuit.eval Φ x}
  have hcard : F.card = 1 := by simp [F]
  have hH : Entropy.H₂ F ≤ (0 : ℝ) := by simpa [Entropy.H₂_card_one, hcard]
  obtain ⟨cover, hmono, hcov, hbound⟩ :=
    Bound.family_collision_entropy_lemma (F := F) (h := 0) (hH := hH) (hn := hn)
  refine ⟨cover, ?_, ?_, hbound⟩
  · intro R hR
    rcases hmono R hR with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro x hx
    have hf : (fun x => Circuit.eval Φ x) ∈ F := by simp [F]
    simpa [F] using hb (fun x => Circuit.eval Φ x) hf hx
  · intro x hx
    have hf : (fun x => Circuit.eval Φ x) ∈ F := by simp [F]
    rcases hcov (fun x => Circuit.eval Φ x) hf x hx with ⟨R, hR, hxR⟩
    exact ⟨R, hR, hxR⟩

end ACCSAT

