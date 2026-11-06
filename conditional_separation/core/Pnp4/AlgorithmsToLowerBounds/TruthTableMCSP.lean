import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Models.Model_PartialMCSP

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Truth tables on `n` variables, represented using the existing `pnp3` table
length `2^n`.
-/
abbrev TruthTable (n : Nat) := Pnp3.Core.BitVec (Pnp3.Models.Partial.tableLen n)

/-- Boolean functions on `n` input bits. -/
abbrev BooleanFunction (n : Nat) := BitVec n → Bool

/--
Canonical tree-circuit class reused from `pnp3/Models/Model_PartialMCSP.lean`.

This keeps the first `pnp4` milestone lightweight while avoiding duplicate
syntax and truth-table arithmetic.
-/
def treeCircuitClass : CircuitFamilyClass where
  Family := Pnp3.Models.Circuit
  eval := fun {_} c => Pnp3.Models.Circuit.eval c
  size := fun {_} c => Pnp3.Models.Circuit.size c

/-- Convert a raw truth table into its extensional Boolean function. -/
def truthTableFunction {n : Nat} (tt : TruthTable n) : BooleanFunction n :=
  Pnp3.Models.truthTableFunction tt

/--
Circuit `c` computes the truth table `tt` if it agrees with the decoded Boolean
function on every input.
-/
def ComputesTruthTable
    (C : CircuitFamilyClass)
    {n : Nat}
    (c : C.Family n)
    (tt : TruthTable n) : Prop :=
  ∀ x : BitVec n, C.eval c x = truthTableFunction tt x

/--
Proof-level MCSP surface: there exists a size-`≤ s` circuit in class `C`
computing the truth table `tt`.

This first `pnp4` milestone keeps the surface propositional.  Executable
Boolean packaging can be added later once the relevant search procedure is
formalized.
-/
def circuitComplexityLE
    (C : CircuitFamilyClass)
    (n s : Nat)
    (tt : TruthTable n) : Prop :=
  ∃ c : C.Family n, C.size c ≤ s ∧ ComputesTruthTable C c tt

/-- Strict version of the same proof-level circuit-complexity surface. -/
def circuitComplexityLT
    (C : CircuitFamilyClass)
    (n s : Nat)
    (tt : TruthTable n) : Prop :=
  ∃ c : C.Family n, C.size c < s ∧ ComputesTruthTable C c tt

/-- Monotonicity of the proof-level MCSP surface in the size threshold. -/
theorem circuitComplexityLE_mono
    {C : CircuitFamilyClass}
    {n s₁ s₂ : Nat}
    {tt : TruthTable n}
    (hs : s₁ ≤ s₂) :
    circuitComplexityLE C n s₁ tt →
      circuitComplexityLE C n s₂ tt := by
  intro h
  rcases h with ⟨c, hcSize, hComp⟩
  exact ⟨c, Nat.le_trans hcSize hs, hComp⟩

/--
Parameterized proof-level MCSP predicate over raw truth tables.

The intended future specialization is the tree-circuit surface
`treeMCSPPredicate`.
-/
def MCSPPredicate
    (C : CircuitFamilyClass)
    (n s : Nat) : TruthTable n → Prop :=
  fun tt => circuitComplexityLE C n s tt

/-- Current concrete MCSP skeleton over the reused `pnp3` tree-circuit model. -/
def treeMCSPPredicate
    (n s : Nat) : TruthTable n → Prop :=
  MCSPPredicate treeCircuitClass n s

/-- Monotonicity of the concrete tree-circuit MCSP threshold predicate. -/
theorem treeMCSPPredicate_mono
    {n s₁ s₂ : Nat}
    (hs : s₁ ≤ s₂)
    {tt : TruthTable n} :
    treeMCSPPredicate n s₁ tt →
      treeMCSPPredicate n s₂ tt :=
  circuitComplexityLE_mono (C := treeCircuitClass) hs

end AlgorithmsToLowerBounds
end Pnp4
