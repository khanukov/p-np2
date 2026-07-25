import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP

/-!
# Exact padding for the MCSP size parameter

The gap between the published unconditional lower bound and the published
magnification threshold is a gap **in the size parameter**, not in the time
exponent:

* Cheraghchi–Hirahara–Myrisiotis–Yoshida (STACS 2021 / ECCC TR20-103,
  Theorem 2) prove `MCSP[2 ^ (μ₂ · n)] ∉ BPTIME₁[N ^ 1.99]` with `μ₂` close
  to `1`;
* McKay–Murray–Williams (STOC 2019), as restated in the same paper
  (Theorem 1 / Theorem 47), need `MCSP[2 ^ (μ₁ · n)] ∉ DTIME₁[N ^ 1.01]` with
  `μ₁` small.

The authors state the frontier explicitly: *"what is missing for proving
P ≠ NP is to decrease the size parameter from `2 ^ ((1 - o(1)) · n)` to
`2 ^ (o(n))` in Theorem 2, or to increase the size parameter from `2 ^ (o(n))`
to `2 ^ ((1 - o(1)) · n)` in Theorem 1."*

The first idea anybody has is to move between the two regimes by **padding**:
extend a function `f` on `n` variables to `g` on `n' ≥ n` variables by ignoring
the extra inputs.  Since `g` and `f` have the *same* circuit complexity, the
same absolute threshold `s` becomes a different *relative* exponent
`log s / n'`, which is what the two theorems disagree about.

This module proves the padding lemma exactly (both directions, with exact size
preservation).  `MuGapNoGo.lean` then shows, also by kernel-checked arithmetic,
that this idea nevertheless cannot close the gap.

Everything here is unconditional.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

open Pnp3.Models hiding truthTableFunction
open Pnp4.AlgorithmsToLowerBounds

/-!
### Coordinate maps between `n` and `n'` variables
-/

/-- Restrict a point on `n'` coordinates to its first `n` coordinates. -/
def projPoint {n n' : Nat} (h : n ≤ n') (y : Pnp3.Core.BitVec n') :
    Pnp3.Core.BitVec n :=
  fun i => y ⟨i.1, lt_of_lt_of_le i.2 h⟩

/-- Extend a point on `n` coordinates by zeros to `n'` coordinates. -/
def extendPoint {n n' : Nat} (x : Pnp3.Core.BitVec n) : Pnp3.Core.BitVec n' :=
  fun j => if hj : j.1 < n then x ⟨j.1, hj⟩ else false

@[simp] lemma projPoint_extendPoint {n n' : Nat} (h : n ≤ n')
    (x : Pnp3.Core.BitVec n) :
    projPoint h (extendPoint (n' := n') x) = x := by
  funext i
  simp [projPoint, extendPoint, i.2]

/-!
### Reindexing circuits
-/

/-- Reindex a circuit into a larger variable set (dummy variables added). -/
def liftCircuit {n n' : Nat} (h : n ≤ n') : Circuit n → Circuit n'
  | Circuit.input i => Circuit.input ⟨i.1, lt_of_lt_of_le i.2 h⟩
  | Circuit.const b => Circuit.const b
  | Circuit.not c => Circuit.not (liftCircuit h c)
  | Circuit.and c₁ c₂ => Circuit.and (liftCircuit h c₁) (liftCircuit h c₂)
  | Circuit.or c₁ c₂ => Circuit.or (liftCircuit h c₁) (liftCircuit h c₂)

/-- Fix every variable outside the first `n` coordinates to `false`. -/
def restrictCircuit {n n' : Nat} : Circuit n' → Circuit n
  | Circuit.input j => if hj : j.1 < n then Circuit.input ⟨j.1, hj⟩
      else Circuit.const false
  | Circuit.const b => Circuit.const b
  | Circuit.not c => Circuit.not (restrictCircuit c)
  | Circuit.and c₁ c₂ => Circuit.and (restrictCircuit c₁) (restrictCircuit c₂)
  | Circuit.or c₁ c₂ => Circuit.or (restrictCircuit c₁) (restrictCircuit c₂)

@[simp] lemma size_liftCircuit {n n' : Nat} (h : n ≤ n') (c : Circuit n) :
    (liftCircuit h c).size = c.size := by
  induction c with
  | input i => simp [liftCircuit, Circuit.size]
  | const b => simp [liftCircuit, Circuit.size]
  | not c ih => simp [liftCircuit, Circuit.size, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [liftCircuit, Circuit.size, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [liftCircuit, Circuit.size, ih₁, ih₂]

@[simp] lemma size_restrictCircuit {n n' : Nat} (c : Circuit n') :
    (restrictCircuit (n := n) c).size = c.size := by
  induction c with
  | input j =>
      by_cases hj : j.1 < n <;> simp [restrictCircuit, Circuit.size, hj]
  | const b => simp [restrictCircuit, Circuit.size]
  | not c ih => simp [restrictCircuit, Circuit.size, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [restrictCircuit, Circuit.size, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [restrictCircuit, Circuit.size, ih₁, ih₂]

@[simp] lemma eval_liftCircuit {n n' : Nat} (h : n ≤ n') (c : Circuit n)
    (y : Pnp3.Core.BitVec n') :
    (liftCircuit h c).eval y = c.eval (projPoint h y) := by
  induction c with
  | input i => simp [liftCircuit, Circuit.eval, projPoint]
  | const b => simp [liftCircuit, Circuit.eval]
  | not c ih => simp [liftCircuit, Circuit.eval, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [liftCircuit, Circuit.eval, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [liftCircuit, Circuit.eval, ih₁, ih₂]

@[simp] lemma eval_restrictCircuit {n n' : Nat} (c : Circuit n')
    (x : Pnp3.Core.BitVec n) :
    (restrictCircuit (n := n) c).eval x = c.eval (extendPoint x) := by
  induction c with
  | input j =>
      by_cases hj : j.1 < n <;>
        simp [restrictCircuit, Circuit.eval, extendPoint, hj]
  | const b => simp [restrictCircuit, Circuit.eval]
  | not c ih => simp [restrictCircuit, Circuit.eval, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [restrictCircuit, Circuit.eval, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [restrictCircuit, Circuit.eval, ih₁, ih₂]

/-!
### The padding lemma
-/

/--
**Exact padding lemma.**

Adding dummy input variables changes neither the circuit complexity of a
function nor the witnessing circuit size: `f` has a circuit of size `≤ s` on
`n` variables if and only if its dummy extension has one of size `≤ s` on
`n' ≥ n` variables.

Both directions are witnessed by size-preserving syntactic transformations
(`liftCircuit` / `restrictCircuit`), so the equivalence holds for *every*
threshold `s`, not just asymptotically.
-/
theorem padding_preserves_circuit_size {n n' : Nat} (h : n ≤ n') (s : Nat)
    (f : Pnp3.Core.BitVec n → Bool) :
    (∃ c : Circuit n, c.size ≤ s ∧ ∀ x, c.eval x = f x) ↔
      (∃ c' : Circuit n', c'.size ≤ s ∧
        ∀ y, c'.eval y = f (projPoint h y)) := by
  constructor
  · rintro ⟨c, hsize, hcorrect⟩
    refine ⟨liftCircuit h c, ?_, ?_⟩
    · simpa using hsize
    · intro y
      simpa using hcorrect (projPoint h y)
  · rintro ⟨c', hsize, hcorrect⟩
    refine ⟨restrictCircuit (n := n) c', ?_, ?_⟩
    · simpa using hsize
    · intro x
      have := hcorrect (extendPoint (n' := n') x)
      simpa using this

/--
The padding lemma transported to the repository's MCSP predicate.

`hcompat` says that `tt'` is the truth table of the dummy extension of the
function whose truth table is `tt`; under that hypothesis the two MCSP slices
have literally the same answer at every threshold `s`.
-/
theorem circuitComplexityLE_padding {n n' s : Nat} (h : n ≤ n')
    (tt : TruthTable n) (tt' : TruthTable n')
    (hcompat : ∀ y, truthTableFunction tt' y
      = truthTableFunction tt (projPoint h y)) :
    circuitComplexityLE treeCircuitClass n s tt ↔
      circuitComplexityLE treeCircuitClass n' s tt' := by
  have hmain := padding_preserves_circuit_size h s (truthTableFunction tt)
  simp only [circuitComplexityLE, ComputesTruthTable, treeCircuitClass]
  constructor
  · rintro ⟨c, hsize, hcorrect⟩
    obtain ⟨c', hsize', hcorrect'⟩ := hmain.mp ⟨c, hsize, hcorrect⟩
    exact ⟨c', hsize', fun y => by rw [hcorrect' y, ← hcompat y]⟩
  · rintro ⟨c', hsize', hcorrect'⟩
    have hc' : ∀ y, Circuit.eval c' y
        = truthTableFunction tt (projPoint h y) := by
      intro y; rw [hcorrect' y, hcompat y]
    obtain ⟨c, hsize, hcorrect⟩ := hmain.mpr ⟨c', hsize', hc'⟩
    exact ⟨c, hsize, hcorrect⟩

end SequentialMagnification
end Frontier
end Pnp4
