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



/-- Schematic definition of the meet‑in‑the‑middle SAT algorithm using
    a rectangular cover of the MCSP truth tables.  The algorithm loops
    over the rectangles and computes partial sums on the left and right
    halves.  Whenever a non‑zero product is detected the circuit is
    satisfiable.  This stub merely returns `false`. -/
noncomputable
def SATViaCover {N : ℕ}
    (Φ : Boolcube.Circuit N)
    (cover : Finset (Finset (Fin N) × Finset (Fin N))) : Bool :=
  -- Real code would iterate over `cover` and evaluate the partial
  -- sums derived from `Φ`.  Here we only sketch the structure.
  false

/-!  A minimal reduction lemma showing how a hypothetical rectangular
cover could solve SAT for `ACC⁰ ∘ MCSP`.  The statement simply returns
an empty cover as a placeholder.  The legacy development included this
lemma; we port it here so that downstream files no longer depend on the
old `pnp` namespace. -/
lemma sat_reduction {N : ℕ} (Φ : Boolcube.Circuit N)
    (hdepth : True := by trivial) :
    ∃ cover : Finset (Finset (Fin N) × Finset (Fin N)), True := by
  -- A real implementation would build `cover` using the polynomial
  -- representation of `Φ` and the cover guaranteed by the FCE Lemma.
  -- We simply return the empty cover as a placeholder.
  exact ⟨∅, trivial⟩

end ACCSAT

