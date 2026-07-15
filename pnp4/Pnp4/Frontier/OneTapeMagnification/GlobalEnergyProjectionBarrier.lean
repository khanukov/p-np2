import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A finite global-energy obstruction after homogeneous projection

This file records a two-coordinate exact instance of the obstruction to removing
the vertex-count factor from the current uFBDD restriction bound by a bare
pointwise-disjointness argument.  Two prefix cylinders are disjoint before
projection.  Their degree-one Walsh slices overlap with opposite signs; after
pairing with opposite suffix characters, the two products collide perfectly.

The example is purely a Fourier-energy obstruction.  It refutes exact
diagonal subadditivity after homogeneous projection, but does not by itself
rule out a universal constant-factor estimate.  Nor does it rule out a
stronger estimate that uses additional transition geometry of the canonical
one-tape selector.
-/

namespace GlobalEnergyProjectionBarrier

open scoped BigOperators
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanFourierEnergy

/-- Linearity helper for the exact normalized finite average. -/
theorem finiteAverage_add {Seed : Type*} [Fintype Seed]
    (f g : Seed -> ℚ) :
    finiteAverage (fun seed => f seed + g seed) =
      finiteAverage f + finiteAverage g := by
  unfold finiteAverage
  rw [Finset.sum_add_distrib]
  ring

/-- Subtractive form of finite-average linearity. -/
theorem finiteAverage_sub {Seed : Type*} [Fintype Seed]
    (f g : Seed -> ℚ) :
    finiteAverage (fun seed => f seed - g seed) =
      finiteAverage f - finiteAverage g := by
  unfold finiteAverage
  rw [Finset.sum_sub_distrib]
  ring

/-- Indicator of the `false` cylinder on the first coordinate. -/
def leftPrefix (input : Fin 2 -> Bool) : ℚ :=
  if input 0 then 0 else 1

/-- Indicator of the complementary `true` cylinder on the first coordinate. -/
def rightPrefix (input : Fin 2 -> Bool) : ℚ :=
  if input 0 then 1 else 0

/-- A half-scaled character on the second coordinate. -/
def leftSuffix (input : Fin 2 -> Bool) : ℚ :=
  (1 / 2 : ℚ) * character {1} input

/-- The opposite half-scaled character on the second coordinate. -/
def rightSuffix (input : Fin 2 -> Bool) : ℚ :=
  -(1 / 2 : ℚ) * character {1} input

/-- The original prefix cylinders are pointwise disjoint. -/
theorem prefix_disjoint (input : Fin 2 -> Bool) :
    leftPrefix input * rightPrefix input = 0 := by
  cases h : input 0 <;> simp [leftPrefix, rightPrefix, h]

/-- Fourier expansion of the left cylinder before taking a homogeneous
slice. -/
theorem leftPrefix_fourier_expansion (input : Fin 2 -> Bool) :
    leftPrefix input =
      (1 / 2 : ℚ) *
        (character ∅ input + character {0} input) := by
  cases h : input 0 <;>
    norm_num [leftPrefix, character, boolSign, h]

/-- Fourier expansion of the complementary cylinder. -/
theorem rightPrefix_fourier_expansion (input : Fin 2 -> Bool) :
    rightPrefix input =
      (1 / 2 : ℚ) *
        (character ∅ input - character {0} input) := by
  cases h : input 0 <;>
    norm_num [rightPrefix, character, boolSign, h]

/-- On the two-coordinate cube, the degree-one supports are exactly the two
singleton coordinates. -/
theorem degreeSupports_two_one :
    degreeSupports 2 1 =
      ({{0}, {1}} : Finset (Finset (Fin 2))) := by
  ext alpha
  rw [mem_degreeSupports]
  constructor
  · intro hdegree
    obtain ⟨coordinate, rfl⟩ := Finset.card_eq_one.mp hdegree
    fin_cases coordinate <;> simp
  · intro hmember
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with hmember | hmember <;>
      subst alpha <;> simp

/-- Degree-one coefficients of the left cylinder. -/
theorem leftPrefix_coefficient_degreeOne
    (alpha : Finset (Fin 2)) (hdegree : alpha.card = 1) :
    coefficient leftPrefix alpha =
      if alpha = {0} then (1 / 2 : ℚ) else 0 := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin 2 -> Bool =>
        leftPrefix input * character alpha input) =
        finiteAverage (fun input : Fin 2 -> Bool =>
          (1 / 2 : ℚ) *
            (character ∅ input * character alpha input +
              character {0} input * character alpha input)) := by
      apply finiteAverage_congr
      intro input
      rw [leftPrefix_fourier_expansion]
      ring
    _ =
        (1 / 2 : ℚ) *
          (finiteAverage (fun input : Fin 2 -> Bool =>
              character ∅ input * character alpha input) +
            finiteAverage (fun input : Fin 2 -> Bool =>
              character {0} input * character alpha input)) := by
      rw [finiteAverage_const_mul, finiteAverage_add]
    _ = (1 / 2 : ℚ) *
          ((if (∅ : Finset (Fin 2)) = alpha then 1 else 0) +
            (if ({0} : Finset (Fin 2)) = alpha then 1 else 0)) := by
      rw [finiteAverage_character_mul_character,
        finiteAverage_character_mul_character]
    _ = if alpha = {0} then (1 / 2 : ℚ) else 0 := by
      have hnonempty : alpha ≠ ∅ := by
        intro heq
        subst alpha
        simp at hdegree
      by_cases heq : alpha = {0}
      · subst alpha
        have hemptySingleton :
            (∅ : Finset (Fin 2)) ≠ ({0} : Finset (Fin 2)) :=
          Ne.symm hnonempty
        rw [if_neg hemptySingleton, if_pos rfl, if_pos rfl]
        norm_num
      · have hempty : (∅ : Finset (Fin 2)) ≠ alpha := Ne.symm hnonempty
        have hsingleton : ({0} : Finset (Fin 2)) ≠ alpha := by
          intro hreverse
          exact heq hreverse.symm
        rw [if_neg hempty, if_neg hsingleton, if_neg heq]
        norm_num

/-- Degree-one coefficients of the right cylinder. -/
theorem rightPrefix_coefficient_degreeOne
    (alpha : Finset (Fin 2)) (hdegree : alpha.card = 1) :
    coefficient rightPrefix alpha =
      if alpha = {0} then -(1 / 2 : ℚ) else 0 := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin 2 -> Bool =>
        rightPrefix input * character alpha input) =
        finiteAverage (fun input : Fin 2 -> Bool =>
          (1 / 2 : ℚ) *
            (character ∅ input * character alpha input -
              character {0} input * character alpha input)) := by
      apply finiteAverage_congr
      intro input
      rw [rightPrefix_fourier_expansion]
      ring
    _ =
        (1 / 2 : ℚ) *
          (finiteAverage (fun input : Fin 2 -> Bool =>
              character ∅ input * character alpha input) -
            finiteAverage (fun input : Fin 2 -> Bool =>
              character {0} input * character alpha input)) := by
      rw [finiteAverage_const_mul, finiteAverage_sub]
    _ = (1 / 2 : ℚ) *
          ((if (∅ : Finset (Fin 2)) = alpha then 1 else 0) -
            (if ({0} : Finset (Fin 2)) = alpha then 1 else 0)) := by
      rw [finiteAverage_character_mul_character,
        finiteAverage_character_mul_character]
    _ = if alpha = {0} then -(1 / 2 : ℚ) else 0 := by
      have hnonempty : alpha ≠ ∅ := by
        intro heq
        subst alpha
        simp at hdegree
      by_cases heq : alpha = {0}
      · subst alpha
        have hemptySingleton :
            (∅ : Finset (Fin 2)) ≠ ({0} : Finset (Fin 2)) :=
          Ne.symm hnonempty
        rw [if_neg hemptySingleton, if_pos rfl, if_pos rfl]
        norm_num
      · have hempty : (∅ : Finset (Fin 2)) ≠ alpha := Ne.symm hnonempty
        have hsingleton : ({0} : Finset (Fin 2)) ≠ alpha := by
          intro hreverse
          exact heq hreverse.symm
        rw [if_neg hempty, if_neg hsingleton, if_neg heq]
        norm_num

/-- The degree-one slice of the left cylinder is `χ_0 / 2`. -/
theorem leftPrefix_degreeOne (input : Fin 2 -> Bool) :
    homogeneousPolynomial 1 (coefficient leftPrefix) input =
      (1 / 2 : ℚ) * character {0} input := by
  classical
  unfold homogeneousPolynomial
  rw [degreeSupports_two_one]
  simp [leftPrefix_coefficient_degreeOne]

/-- The degree-one slice of the right cylinder is `-χ_0 / 2`. -/
theorem rightPrefix_degreeOne (input : Fin 2 -> Bool) :
    homogeneousPolynomial 1 (coefficient rightPrefix) input =
      -(1 / 2 : ℚ) * character {0} input := by
  classical
  unfold homogeneousPolynomial
  rw [degreeSupports_two_one]
  simp [rightPrefix_coefficient_degreeOne]

/-- The two projected prefix/suffix terms agree pointwise. -/
theorem projected_terms_collide (input : Fin 2 -> Bool) :
    homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input =
      homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input := by
  rw [leftPrefix_degreeOne, rightPrefix_degreeOne]
  simp [leftSuffix, rightSuffix]

/-- Each projected component has squared average exactly `1/16`. -/
theorem left_component_energy :
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient leftPrefix) input *
        leftSuffix input) ^ 2) = (1 / 16 : ℚ) := by
  calc
    finiteAverage (fun input : Fin 2 -> Bool =>
        (homogeneousPolynomial 1 (coefficient leftPrefix) input *
          leftSuffix input) ^ 2) =
        finiteAverage (fun _input : Fin 2 -> Bool => (1 / 16 : ℚ)) := by
      apply finiteAverage_congr
      intro input
      rw [leftPrefix_degreeOne]
      have hzero : character ({0} : Finset (Fin 2)) input ^ 2 = 1 := by
        rw [pow_two]
        exact character_square ({0} : Finset (Fin 2)) input
      have hone : character ({1} : Finset (Fin 2)) input ^ 2 = 1 := by
        rw [pow_two]
        exact character_square ({1} : Finset (Fin 2)) input
      rw [show
        ((1 / 2 : ℚ) * character {0} input * leftSuffix input) ^ 2 =
          (1 / 16 : ℚ) * character {0} input ^ 2 * character {1} input ^ 2 by
            simp [leftSuffix]
            ring]
      rw [hzero, hone]
      norm_num
    _ = (1 / 16 : ℚ) := by
      simp [finiteAverage]

/-- The right projected component has the same energy. -/
theorem right_component_energy :
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient rightPrefix) input *
        rightSuffix input) ^ 2) = (1 / 16 : ℚ) := by
  calc
    finiteAverage (fun input : Fin 2 -> Bool =>
        (homogeneousPolynomial 1 (coefficient rightPrefix) input *
          rightSuffix input) ^ 2) =
        finiteAverage (fun _input : Fin 2 -> Bool => (1 / 16 : ℚ)) := by
      apply finiteAverage_congr
      intro input
      rw [rightPrefix_degreeOne]
      have hzero : character ({0} : Finset (Fin 2)) input ^ 2 = 1 := by
        rw [pow_two]
        exact character_square ({0} : Finset (Fin 2)) input
      have hone : character ({1} : Finset (Fin 2)) input ^ 2 = 1 := by
        rw [pow_two]
        exact character_square ({1} : Finset (Fin 2)) input
      rw [show
        (-(1 / 2 : ℚ) * character {0} input * rightSuffix input) ^ 2 =
          (1 / 16 : ℚ) * character {0} input ^ 2 * character {1} input ^ 2 by
            simp [rightSuffix]
            ring]
      rw [hzero, hone]
      norm_num
    _ = (1 / 16 : ℚ) := by
      simp [finiteAverage]

/-- Perfect coherence doubles amplitude and quadruples energy: the energy of
the sum is `1/4`, twice the sum of the individual energies (`1/8`). -/
theorem aggregate_and_component_energies_exact :
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input +
        homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input) ^ 2) =
      (1 / 4 : ℚ) ∧
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input) ^ 2) +
      finiteAverage (fun input : Fin 2 -> Bool =>
        (homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input) ^ 2) =
      (1 / 8 : ℚ) := by
  constructor
  · calc
      finiteAverage (fun input : Fin 2 -> Bool =>
          (homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input +
            homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input) ^ 2) =
          finiteAverage (fun _input : Fin 2 -> Bool => (1 / 4 : ℚ)) := by
        apply finiteAverage_congr
        intro input
        rw [projected_terms_collide, rightPrefix_degreeOne]
        have hzero : character ({0} : Finset (Fin 2)) input ^ 2 = 1 := by
          rw [pow_two]
          exact character_square ({0} : Finset (Fin 2)) input
        have hone : character ({1} : Finset (Fin 2)) input ^ 2 = 1 := by
          rw [pow_two]
          exact character_square ({1} : Finset (Fin 2)) input
        rw [show
          (-(1 / 2 : ℚ) * character {0} input * rightSuffix input +
              -(1 / 2 : ℚ) * character {0} input * rightSuffix input) ^ 2 =
            (1 / 4 : ℚ) * character {0} input ^ 2 * character {1} input ^ 2 by
              simp [rightSuffix]
              ring]
        rw [hzero, hone]
        norm_num
      _ = (1 / 4 : ℚ) := by
        simp [finiteAverage]
  · rw [left_component_energy, right_component_energy]
    norm_num

/-- In particular, the frame-style inequality suggested by the original
pointwise disjointness is false: the sum has strictly more energy than the
sum of the two component energies. -/
theorem sum_component_energies_lt_aggregate_energy :
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input) ^ 2) +
      finiteAverage (fun input : Fin 2 -> Bool =>
        (homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input) ^ 2) <
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input +
        homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input) ^ 2) := by
  rw [aggregate_and_component_energies_exact.1,
    aggregate_and_component_energies_exact.2]
  norm_num

/-- Bundled capstone: pointwise-disjoint prefix cylinders do not force
diagonal subadditivity of the projected prefix/suffix energy. -/
theorem disjoint_prefixes_and_energy_subadditivity_fails :
    (∀ input : Fin 2 -> Bool,
      leftPrefix input * rightPrefix input = 0) ∧
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input) ^ 2) +
      finiteAverage (fun input : Fin 2 -> Bool =>
        (homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input) ^ 2) <
    finiteAverage (fun input : Fin 2 -> Bool =>
      (homogeneousPolynomial 1 (coefficient leftPrefix) input * leftSuffix input +
        homogeneousPolynomial 1 (coefficient rightPrefix) input * rightSuffix input) ^ 2) :=
  ⟨prefix_disjoint, sum_component_energies_lt_aggregate_energy⟩

end GlobalEnergyProjectionBarrier
end OneTapeMagnification
end Frontier
end Pnp4
