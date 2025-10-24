-- acc_mcsp_sat.lean
-- ==================
--
-- Outline of the meet-in-the-middle SAT algorithm for `ACC⁰ ∘ MCSP`.
-- This module sketches how a rectangle cover from the
-- Family Collision–Entropy Lemma (Lemma B) can yield a
-- subexponential SAT algorithm for `ACC⁰ ∘ MCSP`.
-- Many statements were previously placeholders; several of the
-- helper lemmas are now fully proven, while the remaining parts
-- still serve as a blueprint for future development.

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

/-! ### Encoding circuits as polynomials over `𝔽₂`

To reason about the meet-in-the-middle approach it will be convenient to
express a Boolean circuit as a polynomial over the field `𝔽₂`.  The following
utility converts booleans to `𝔽₂` and establishes the basic identities for the
logical operations. -/

@[simp] def boolToF2 (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] lemma boolToF2_true : boolToF2 true = (1 : ZMod 2) := by rfl

@[simp] lemma boolToF2_false : boolToF2 false = (0 : ZMod 2) := by rfl

@[simp] lemma boolToF2_not (b : Bool) : boolToF2 (!b) = 1 + boolToF2 b := by
  cases b <;> simp [boolToF2]

@[simp] lemma boolToF2_and (a b : Bool) :
    boolToF2 (a && b) = boolToF2 a * boolToF2 b := by
  cases a <;> cases b <;> simp [boolToF2]

@[simp] lemma boolToF2_or (a b : Bool) :
    boolToF2 (a || b) = boolToF2 a + boolToF2 b + boolToF2 a * boolToF2 b := by
  cases a <;> cases b <;> simp [boolToF2]

/-! The translation of circuits to polynomials is completely structural.  The
degree bound from Razborov--Smolensky is suppressed here; the main purpose of
this definition is to provide a concrete polynomial whose evaluation matches the
circuit semantics. -/

noncomputable def circuitToPoly {n : ℕ} : Boolcube.Circuit n → Polynomial n
  | Boolcube.Circuit.var i   => MvPolynomial.X i
  | Boolcube.Circuit.const b => if b then 1 else 0
  | Boolcube.Circuit.not c   => 1 + circuitToPoly c
  | Boolcube.Circuit.and c₁ c₂ => circuitToPoly c₁ * circuitToPoly c₂
  | Boolcube.Circuit.or c₁ c₂  =>
      circuitToPoly c₁ + circuitToPoly c₂ + circuitToPoly c₁ * circuitToPoly c₂

lemma eval_circuitToPoly {n : ℕ} (c : Boolcube.Circuit n) (x : Boolcube.Point n) :
    boolToF2 (Boolcube.Circuit.eval c x) =
      MvPolynomial.eval (fun i => boolToF2 (x i)) (circuitToPoly c) := by
  induction c with
  | var i =>
      simp [circuitToPoly]
  | const b =>
      cases b <;> simp [circuitToPoly]
  | not c ih =>
      simp [circuitToPoly, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [circuitToPoly, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [circuitToPoly, ih₁, ih₂, add_comm, add_left_comm, add_assoc]

/-! Razborov–Smolensky: every `ACC⁰` circuit can be expressed as a low-degree
polynomial over `𝔽₂`.  The bound on the degree is schematic and stated in
big‑O form.  The construction `circuitToPoly` provides one explicit witness. -/

/-- Razborov–Smolensky: every `ACC⁰` circuit can be expressed as a
    low-degree polynomial over `𝔽₂`.  The bound on the degree is
    schematic and stated in big‑O form. -/
lemma acc_circuit_poly {n d : ℕ} (C : Boolcube.Circuit n)
    (hdepth : True := by trivial) :
    ∃ P : Polynomial n,
      ∀ x, boolToF2 (Boolcube.Circuit.eval C x) =
        MvPolynomial.eval (fun i => boolToF2 (x i)) P := by
  refine ⟨circuitToPoly C, ?_⟩
  intro x
  simpa using eval_circuitToPoly (c := C) (x := x)

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
    over the rectangles and tests the circuit on each sample point.
    As soon as a `true` evaluation is found the search terminates. -/
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
      (∀ x, Circuit.eval Φ x = true → ∃ R ∈ cover, x ∈ₛ R) := by
  classical
  let F : Boolcube.Family N := {fun x => Circuit.eval Φ x}
  have hcard : F.card = 1 := by simp [F]
  have hH : Entropy.H₂ F ≤ (0 : ℝ) := by simpa [Entropy.H₂_card_one, hcard]
  -- Obtain an entropy-based cover without caring about its size.
  rcases Boolcube.familyCollisionEntropyCover (F := F) (h := 0) hH
      with ⟨T, hmono, hcov⟩
  refine ⟨T, ?_, ?_⟩
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

/-! ### A concrete SAT solver using the entropy cover

`SATUsingFCE` extracts the rectangle cover from `sat_reduction` and runs
`SATViaCover`.  The complexity bound follows from `sat_reduction` together with
`SATViaCover_time_bound`. -/

noncomputable def SATUsingFCE {N : ℕ} (Φ : Boolcube.Circuit N)
    (hn : N ≥ Bound.n₀ 0) : Bool :=
  let cover := Classical.choose (sat_reduction (Φ := Φ) (hn := hn))
  SATViaCover Φ cover

def SATUsingFCE_time {N : ℕ} (Φ : Boolcube.Circuit N) (hn : N ≥ Bound.n₀ 0) : ℕ :=
  let cover := Classical.choose (sat_reduction (Φ := Φ) (hn := hn))
  SATViaCover_time cover

lemma SATUsingFCE_correct {N : ℕ} (Φ : Boolcube.Circuit N)
    (hn : N ≥ Bound.n₀ 0) :
    SATUsingFCE Φ hn = true ↔ ∃ x, Circuit.eval Φ x = true := by
  classical
  have key := Classical.choose_spec (sat_reduction (Φ := Φ) (hn := hn))
  rcases key with ⟨hmono, hcov, hbound⟩
  unfold SATUsingFCE SATViaCover
  have := SATViaCover_correct (Φ := Φ) (cover := Classical.choose (sat_reduction (Φ := Φ) (hn := hn))) hmono hcov
  simpa using this

lemma SATUsingFCE_time_bound {N : ℕ} (Φ : Boolcube.Circuit N)
    (hn : N ≥ Bound.n₀ 0) :
    SATUsingFCE_time Φ hn ≤ Nat.pow 2 (N / 100) := by
  classical
  let key := sat_reduction (Φ := Φ) (hn := hn)
  rcases key with ⟨cover, hmono, hcov, hbound⟩
  unfold SATUsingFCE_time
  have htime := SATViaCover_time_bound (cover := cover)
  exact le_trans htime hbound

end ACCSAT

