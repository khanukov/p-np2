import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NonVacuity
import Mathlib.Tactic

/-!
# V2-A structural-normalisation meta-barrier

Progress classification: side-track audit formalization.

This module isolates the structural-recursion framework discussed in the
`fp3b3_4` M2 dispatch.  A normaliser in this framework is assembled from local
constructor replacements and is therefore forbidden, by explicit fields, from
manufacturing mixed OR/NOT gates while folding an AND-only formula.  The main
barrier theorem shows that any such normaliser that also eliminates the V2-A
seed gate and simplifies `C ∧ true` makes the restored V2-A seeded-prefix
witness fail V2-A's own mixed-gate clause.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_NormaliseMetaBarrier

open Pnp3.ComplexityInterfaces
open V2_A_gpt55
open V2_A_gpt55.FormulaShape

abbrev prefixAndLW (n k : Nat) (h : k ≤ n) : FormulaCircuit n :=
  Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd n k h

/--
Local replacements for Boolean constructors used by `foldFormula`.

The evaluation and size fields make the fold a genuine normalisation pass, not
an arbitrary semantic rewrite.  The two `mkAnd_*_pres` fields are the explicit
operator-review strengthening: folding an AND node whose children are already
OR-free/NOT-free may not invent OR/NOT syntax.
-/
structure LocalFormulaOps where
  mkNot : ∀ {n : Nat}, FormulaCircuit n → FormulaCircuit n
  mkAnd : ∀ {n : Nat}, FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  mkOr : ∀ {n : Nat}, FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  mkNot_eval : ∀ {n : Nat} (C : FormulaCircuit n) (x : Bitstring n),
    FormulaCircuit.eval (mkNot C) x = FormulaCircuit.eval (FormulaCircuit.not C) x
  mkAnd_eval : ∀ {n : Nat} (A B : FormulaCircuit n) (x : Bitstring n),
    FormulaCircuit.eval (mkAnd A B) x = FormulaCircuit.eval (FormulaCircuit.and A B) x
  mkOr_eval : ∀ {n : Nat} (A B : FormulaCircuit n) (x : Bitstring n),
    FormulaCircuit.eval (mkOr A B) x = FormulaCircuit.eval (FormulaCircuit.or A B) x
  mkNot_size_le : ∀ {n : Nat} (C : FormulaCircuit n),
    FormulaCircuit.size (mkNot C) ≤ FormulaCircuit.size (FormulaCircuit.not C)
  mkAnd_size_le : ∀ {n : Nat} (A B : FormulaCircuit n),
    FormulaCircuit.size (mkAnd A B) ≤ FormulaCircuit.size (FormulaCircuit.and A B)
  mkOr_size_le : ∀ {n : Nat} (A B : FormulaCircuit n),
    FormulaCircuit.size (mkOr A B) ≤ FormulaCircuit.size (FormulaCircuit.or A B)
  mkAnd_orGateCount_pres : ∀ {n : Nat} (A B : FormulaCircuit n),
    orGateCount A = 0 → orGateCount B = 0 → orGateCount (mkAnd A B) = 0
  mkAnd_notGateCount_pres : ∀ {n : Nat} (A B : FormulaCircuit n),
    notGateCount A = 0 → notGateCount B = 0 → notGateCount (mkAnd A B) = 0

/-- Structural fold induced by local constructor replacements. -/
def foldFormula (ops : LocalFormulaOps) : ∀ {n : Nat}, FormulaCircuit n → FormulaCircuit n
  | _, FormulaCircuit.const b => FormulaCircuit.const b
  | _, FormulaCircuit.input i => FormulaCircuit.input i
  | _, FormulaCircuit.not C => ops.mkNot (foldFormula ops C)
  | _, FormulaCircuit.and A B => ops.mkAnd (foldFormula ops A) (foldFormula ops B)
  | _, FormulaCircuit.or A B => ops.mkOr (foldFormula ops A) (foldFormula ops B)

/-- A structural normaliser is extensionally its local structural fold. -/
structure StructuralNormaliser where
  ops : LocalFormulaOps
  normalise : ∀ {n : Nat}, FormulaCircuit n → FormulaCircuit n
  normalise_eq_fold : ∀ {n : Nat} (C : FormulaCircuit n), normalise C = foldFormula ops C

/-- Folding preserves formula semantics. -/
theorem foldFormula_eval (ops : LocalFormulaOps) {n : Nat} (C : FormulaCircuit n)
    (x : Bitstring n) :
    FormulaCircuit.eval (foldFormula ops C) x = FormulaCircuit.eval C x := by
  induction C with
  | const b => simp [foldFormula, FormulaCircuit.eval]
  | input i => simp [foldFormula, FormulaCircuit.eval]
  | not C ih => simp [foldFormula, FormulaCircuit.eval, ops.mkNot_eval, ih]
  | and A B ihA ihB => simp [foldFormula, FormulaCircuit.eval, ops.mkAnd_eval, ihA, ihB]
  | or A B ihA ihB => simp [foldFormula, FormulaCircuit.eval, ops.mkOr_eval, ihA, ihB]

/-- Structural normalisation preserves formula semantics. -/
theorem normalise_eval (𝒩 : StructuralNormaliser) {n : Nat} (C : FormulaCircuit n)
    (x : Bitstring n) :
    FormulaCircuit.eval (𝒩.normalise C) x = FormulaCircuit.eval C x := by
  rw [𝒩.normalise_eq_fold]
  exact foldFormula_eval 𝒩.ops C x

/-- Folding does not increase formula size. -/
theorem foldFormula_size_le (ops : LocalFormulaOps) {n : Nat} (C : FormulaCircuit n) :
    FormulaCircuit.size (foldFormula ops C) ≤ FormulaCircuit.size C := by
  induction C with
  | const b => simp [foldFormula, FormulaCircuit.size]
  | input i => simp [foldFormula, FormulaCircuit.size]
  | not C ih =>
      have hLocal := ops.mkNot_size_le (foldFormula ops C)
      simp [foldFormula, FormulaCircuit.size] at hLocal ⊢
      omega
  | and A B ihA ihB =>
      have hLocal := ops.mkAnd_size_le (foldFormula ops A) (foldFormula ops B)
      simp [foldFormula, FormulaCircuit.size] at hLocal ⊢
      omega
  | or A B ihA ihB =>
      have hLocal := ops.mkOr_size_le (foldFormula ops A) (foldFormula ops B)
      simp [foldFormula, FormulaCircuit.size] at hLocal ⊢
      omega

/-- Structural normalisation does not increase formula size. -/
theorem normalise_size_le (𝒩 : StructuralNormaliser) {n : Nat} (C : FormulaCircuit n) :
    FormulaCircuit.size (𝒩.normalise C) ≤ FormulaCircuit.size C := by
  rw [𝒩.normalise_eq_fold]
  exact foldFormula_size_le 𝒩.ops C

/-- The language displayed by a pointwise-normalised witness. -/
def normalisedLanguage {L : Language} (𝒩 : StructuralNormaliser) (w : InPpolyFormula L) : Language :=
  fun n x => FormulaCircuit.eval (𝒩.normalise (w.family n)) x

/-- Apply a structural normaliser pointwise to a strict formula witness. -/
def normalisedWitness {L : Language} (𝒩 : StructuralNormaliser) (w : InPpolyFormula L) :
    InPpolyFormula (normalisedLanguage 𝒩 w) where
  polyBound := w.polyBound
  polyBound_poly := w.polyBound_poly
  family := fun n => 𝒩.normalise (w.family n)
  family_size_le := fun n => le_trans (normalise_size_le 𝒩 (w.family n)) (w.family_size_le n)
  correct := fun _ _ => rfl

/-- Folding the concrete prefix conjunction does not introduce OR gates. -/
theorem foldFormula_prefixAnd_orGateCount_zero (ops : LocalFormulaOps) (n k : Nat) (h : k ≤ n) :
    orGateCount (foldFormula ops (prefixAndLW n k h)) = 0 := by
  induction k with
  | zero => simp [prefixAndLW, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, foldFormula, orGateCount]
  | succ k ih =>
      have hk : k ≤ n := Nat.le_of_succ_le h
      simp [prefixAndLW, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, foldFormula]
      exact ops.mkAnd_orGateCount_pres _ _ rfl (ih hk)

/-- Folding the concrete prefix conjunction does not introduce NOT gates. -/
theorem foldFormula_prefixAnd_notGateCount_zero (ops : LocalFormulaOps) (n k : Nat) (h : k ≤ n) :
    notGateCount (foldFormula ops (prefixAndLW n k h)) = 0 := by
  induction k with
  | zero => simp [prefixAndLW, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, foldFormula, notGateCount]
  | succ k ih =>
      have hk : k ≤ n := Nat.le_of_succ_le h
      simp [prefixAndLW, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, foldFormula]
      exact ops.mkAnd_notGateCount_pres _ _ rfl (ih hk)

private def allTrue2 : Bitstring 2 := fun _ => true

private def falseAt2 (i : Fin 2) : Bitstring 2 := fun j => if j = i then false else true


private theorem prefixAnd_two_eval_allTrue :
    FormulaCircuit.eval (prefixAndLW 2 2 (Nat.le_refl 2)) allTrue2 = true := by
  simp [prefixAndLW, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, allTrue2, FormulaCircuit.eval]

private theorem prefixAnd_two_eval_falseAt_zero :
    FormulaCircuit.eval (prefixAndLW 2 2 (Nat.le_refl 2)) (falseAt2 ⟨0, by decide⟩) = false := by
  simp [prefixAndLW, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, falseAt2, FormulaCircuit.eval]

private theorem prefixAnd_two_eval_falseAt_one :
    FormulaCircuit.eval (prefixAndLW 2 2 (Nat.le_refl 2)) (falseAt2 ⟨1, by decide⟩) = false := by
  simp [prefixAndLW, Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary.prefixAnd, falseAt2, FormulaCircuit.eval]

/-- Semantic preservation forces both variables to remain syntactically present
in the normalised two-variable prefix conjunction. -/
theorem support_foldFormula_prefixAnd_two (ops : LocalFormulaOps) :
    2 ≤ (FormulaCircuit.support (foldFormula ops (prefixAndLW 2 2 (Nat.le_refl 2)))).card := by
  let C := foldFormula ops (prefixAndLW 2 2 (Nat.le_refl 2))
  have hEval : ∀ x : Bitstring 2,
      FormulaCircuit.eval C x =
        FormulaCircuit.eval (prefixAndLW 2 2 (Nat.le_refl 2)) x := by
    intro x
    exact foldFormula_eval ops (prefixAndLW 2 2 (Nat.le_refl 2)) x
  have h0 : (⟨0, by decide⟩ : Fin 2) ∈ FormulaCircuit.support C := by
    by_contra hnot
    have hAgree : ∀ j ∈ FormulaCircuit.support C, allTrue2 j = falseAt2 ⟨0, by decide⟩ j := by
      intro j hj
      simp [allTrue2, falseAt2]
      intro hj0
      exact hnot (by simpa [hj0] using hj)
    have hSame := FormulaCircuit.eval_eq_of_eq_on_support C hAgree
    rw [hEval allTrue2, hEval (falseAt2 ⟨0, by decide⟩),
      prefixAnd_two_eval_allTrue, prefixAnd_two_eval_falseAt_zero] at hSame
    cases hSame
  have h1 : (⟨1, by decide⟩ : Fin 2) ∈ FormulaCircuit.support C := by
    by_contra hnot
    have hAgree : ∀ j ∈ FormulaCircuit.support C, allTrue2 j = falseAt2 ⟨1, by decide⟩ j := by
      intro j hj
      simp [allTrue2, falseAt2]
      intro hj1
      exact hnot (by simpa [hj1] using hj)
    have hSame := FormulaCircuit.eval_eq_of_eq_on_support C hAgree
    rw [hEval allTrue2, hEval (falseAt2 ⟨1, by decide⟩),
      prefixAnd_two_eval_allTrue, prefixAnd_two_eval_falseAt_one] at hSame
    cases hSame
  have hne : (⟨0, by decide⟩ : Fin 2) ≠ ⟨1, by decide⟩ := by decide
  have hpair : ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin 2)) ⊆ FormulaCircuit.support C := by
    intro j hj
    simp at hj
    rcases hj with rfl | rfl
    · exact h0
    · exact h1
  have hcard := Finset.card_le_card hpair
  simpa [hne] using hcard

/-- Concrete support lower bound used by the barrier theorem. -/
theorem support_normalise_seededPrefixAnd_two
    (𝒩 : StructuralNormaliser)
    (hSeed : ∀ {n : Nat} (h : 1 ≤ n),
      𝒩.normalise (seedGate n h) = FormulaCircuit.const true)
    (hAndTrue : ∀ {n : Nat} (C : FormulaCircuit n),
      𝒩.ops.mkAnd C (FormulaCircuit.const true) = C) :
    2 ≤ (FormulaCircuit.support (𝒩.normalise (seededPrefixAndFamily 2))).card := by
  have hNorm : 𝒩.normalise (seededPrefixAndFamily 2) =
      foldFormula 𝒩.ops (prefixAndLW 2 2 (Nat.le_refl 2)) := by
    have hSeedFold : foldFormula 𝒩.ops (seedGate 2 (by decide : 1 ≤ 2)) = FormulaCircuit.const true := by
      rw [← 𝒩.normalise_eq_fold (seedGate 2 (by decide : 1 ≤ 2))]
      exact hSeed (by decide : 1 ≤ 2)
    rw [𝒩.normalise_eq_fold]
    simp [seededPrefixAndFamily, foldFormula, prefixAndLW, hSeedFold, hAndTrue]
  rw [hNorm]
  exact support_foldFormula_prefixAnd_two 𝒩.ops

/-- The normalised seeded family member at `n = 2` has no OR gates. -/
theorem normalise_seededPrefixAnd_two_orGateCount_zero
    (𝒩 : StructuralNormaliser)
    (hSeed : ∀ {n : Nat} (h : 1 ≤ n),
      𝒩.normalise (seedGate n h) = FormulaCircuit.const true)
    (hAndTrue : ∀ {n : Nat} (C : FormulaCircuit n),
      𝒩.ops.mkAnd C (FormulaCircuit.const true) = C) :
    orGateCount (𝒩.normalise (seededPrefixAndFamily 2)) = 0 := by
  have hNorm : 𝒩.normalise (seededPrefixAndFamily 2) =
      foldFormula 𝒩.ops (prefixAndLW 2 2 (Nat.le_refl 2)) := by
    have hSeedFold : foldFormula 𝒩.ops (seedGate 2 (by decide : 1 ≤ 2)) = FormulaCircuit.const true := by
      rw [← 𝒩.normalise_eq_fold (seedGate 2 (by decide : 1 ≤ 2))]
      exact hSeed (by decide : 1 ≤ 2)
    rw [𝒩.normalise_eq_fold]
    simp [seededPrefixAndFamily, foldFormula, prefixAndLW, hSeedFold, hAndTrue]
  rw [hNorm]
  exact foldFormula_prefixAnd_orGateCount_zero 𝒩.ops 2 2 (Nat.le_refl 2)

/-- The normalised seeded family member at `n = 2` has no NOT gates. -/
theorem normalise_seededPrefixAnd_two_notGateCount_zero
    (𝒩 : StructuralNormaliser)
    (hSeed : ∀ {n : Nat} (h : 1 ≤ n),
      𝒩.normalise (seedGate n h) = FormulaCircuit.const true)
    (hAndTrue : ∀ {n : Nat} (C : FormulaCircuit n),
      𝒩.ops.mkAnd C (FormulaCircuit.const true) = C) :
    notGateCount (𝒩.normalise (seededPrefixAndFamily 2)) = 0 := by
  have hNorm : 𝒩.normalise (seededPrefixAndFamily 2) =
      foldFormula 𝒩.ops (prefixAndLW 2 2 (Nat.le_refl 2)) := by
    have hSeedFold : foldFormula 𝒩.ops (seedGate 2 (by decide : 1 ≤ 2)) = FormulaCircuit.const true := by
      rw [← 𝒩.normalise_eq_fold (seedGate 2 (by decide : 1 ≤ 2))]
      exact hSeed (by decide : 1 ≤ 2)
    rw [𝒩.normalise_eq_fold]
    simp [seededPrefixAndFamily, foldFormula, prefixAndLW, hSeedFold, hAndTrue]
  rw [hNorm]
  exact foldFormula_prefixAnd_notGateCount_zero 𝒩.ops 2 2 (Nat.le_refl 2)

/--
V2-A.1 structural-normalisation meta-barrier: seed elimination plus `AND true`
reduction is incompatible with preserving V2-A acceptance of the normalised
seeded-prefix witness within the structural no-mixed-gate-invention framework.
-/
theorem v2_a_structural_normalisation_meta_barrier
    (𝒩 : StructuralNormaliser)
    (hSeed : ∀ {n : Nat} (h : 1 ≤ n),
      𝒩.normalise (seedGate n h) = FormulaCircuit.const true)
    (hAndTrue : ∀ {n : Nat} (C : FormulaCircuit n),
      𝒩.ops.mkAnd C (FormulaCircuit.const true) = C) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
        (normalisedWitness 𝒩 seededPrefixAndWitness) := by
  intro hFilter
  obtain ⟨_hUnbounded, _hGate, _hDepth, hMix⟩ := hFilter
  have hSupport := support_normalise_seededPrefixAnd_two 𝒩 hSeed hAndTrue
  have hOrPos := (hMix 2 hSupport).1
  have hOrZero := normalise_seededPrefixAnd_two_orGateCount_zero 𝒩 hSeed hAndTrue
  change 0 < orGateCount (𝒩.normalise (seededPrefixAndFamily 2)) at hOrPos
  rw [hOrZero] at hOrPos
  exact Nat.lt_irrefl 0 hOrPos

/-- The structural-normaliser framework is inhabited by the identity normaliser. -/
theorem identity_structuralNormaliser_exists :
    ∃ (𝒩 : StructuralNormaliser),
      ∀ {n : Nat} (C : FormulaCircuit n), 𝒩.normalise C = C := by
  let ops : LocalFormulaOps := {
    mkNot := fun C => FormulaCircuit.not C
    mkAnd := fun A B => FormulaCircuit.and A B
    mkOr := fun A B => FormulaCircuit.or A B
    mkNot_eval := by intro n C x; rfl
    mkAnd_eval := by intro n A B x; rfl
    mkOr_eval := by intro n A B x; rfl
    mkNot_size_le := by intro n C; rfl
    mkAnd_size_le := by intro n A B; rfl
    mkOr_size_le := by intro n A B; rfl
    mkAnd_orGateCount_pres := by intro n A B hA hB; simp [orGateCount, hA, hB]
    mkAnd_notGateCount_pres := by intro n A B hA hB; simp [notGateCount, hA, hB]
  }
  refine ⟨{
    ops := ops
    normalise := fun C => C
    normalise_eq_fold := ?_
  }, ?_⟩
  · intro n C
    induction C with
    | const b => simp [foldFormula]
    | input i => simp [foldFormula]
    | not C ih =>
        rw [foldFormula]
        simp [ops]
        exact ih
    | and A B ihA ihB =>
        rw [foldFormula]
        simp [ops]
        exact ⟨ihA, ihB⟩
    | or A B ihA ihB =>
        rw [foldFormula]
        simp [ops]
        exact ⟨ihA, ihB⟩
  · intro n C
    rfl

end V2_A_NormaliseMetaBarrier
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
