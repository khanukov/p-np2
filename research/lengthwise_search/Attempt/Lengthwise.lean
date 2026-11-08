import Pnp4.Frontier.SearchMCSPMagnification

/-! Lengthwise normal forms for the existing nonuniform search contract.

Progress classification: Infrastructure. These theorems reorganize an exact
research obligation; they establish no new circuit lower bound. The generic
circuit carrier need not be finite, and this file supplies no enumerator.
-/

namespace Research.LengthwiseSearch

open Pnp4.AlgorithmsToLowerBounds Pnp4.Frontier

/-- A bounded search solver at one length; the bound is PER OUTPUT BIT. -/
structure SolverAt (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass) (n bound : Nat) where
  outputCircuit : Fin (problem.witnessBits n) → C.Family (problem.instanceBits n)
  size_le : ∀ i, C.size (outputCircuit i) ≤ bound
  solves : ∀ x, problem.promise n x →
    problem.relation n x
      (searchSolverOutput (problem := problem) (C := C) outputCircuit x)

/-- Every bounded output tuple fails on some promised input at this length.
The input may depend on the entire tuple; no common counterexample is assumed.
-/
def LowerBoundAt (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass) (n bound : Nat) : Prop :=
  ∀ outputCircuit : Fin (problem.witnessBits n) → C.Family (problem.instanceBits n),
    (∀ i, C.size (outputCircuit i) ≤ bound) →
    ∃ x, problem.promise n x ∧
      ¬ problem.relation n x
        (searchSolverOutput (problem := problem) (C := C) outputCircuit x)

/-- Restrict a single nonuniform family to an arbitrary length. -/
def BoundedSearchSolver.atLength {problem : SearchMCSPCompressionProblem}
    {C : CircuitFamilyClass} {bound : Nat → Nat}
    (solver : Pnp4.Frontier.BoundedSearchSolver problem C bound) (n : Nat) :
    SolverAt problem C n (bound n) where
  outputCircuit := solver.outputCircuit n
  size_le := solver.size_le n
  solves := solver.solves n

/-- Nonuniformity permits an independent choice of solver at every length. -/
theorem family_iff_all_lengths (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass) (bound : Nat → Nat) :
    Nonempty (Pnp4.Frontier.BoundedSearchSolver problem C bound) ↔
      ∀ n, Nonempty (SolverAt problem C n (bound n)) := by
  classical
  constructor
  · rintro ⟨solver⟩ n
    exact ⟨BoundedSearchSolver.atLength solver n⟩
  · intro h
    let solver : ∀ n, SolverAt problem C n (bound n) :=
      fun n => Classical.choice (h n)
    exact ⟨{
      outputCircuit := fun n => (solver n).outputCircuit
      size_le := fun n => (solver n).size_le
      solves := fun n => (solver n).solves
    }⟩

/-- Exact, also for empty promises, zero output width and empty circuit carriers. -/
theorem lowerBoundAt_iff_no_solver (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass) (n bound : Nat) :
    LowerBoundAt problem C n bound ↔ ¬ Nonempty (SolverAt problem C n bound) := by
  classical
  constructor
  · intro h ⟨solver⟩
    obtain ⟨x, hp, hbad⟩ := h solver.outputCircuit solver.size_le
    exact hbad (solver.solves x hp)
  · intro hNo outputCircuit hsize
    by_contra hNoBad
    apply hNo
    refine ⟨{ outputCircuit := outputCircuit, size_le := hsize, solves := ?_ }⟩
    intro x hp
    by_contra hNot
    exact hNoBad ⟨x, hp, hNot⟩

/-- A global family fails to exist exactly when one length defeats every tuple. -/
theorem no_family_iff_exists_lowerBoundAt (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass) (bound : Nat → Nat) :
    ¬ Nonempty (Pnp4.Frontier.BoundedSearchSolver problem C bound) ↔
      ∃ n, LowerBoundAt problem C n (bound n) := by
  classical
  constructor
  · intro hNo
    by_contra hNoLength
    apply hNo
    apply (family_iff_all_lengths problem C bound).mpr
    intro n
    by_contra hNoSolver
    exact hNoLength ⟨n, (lowerBoundAt_iff_no_solver problem C n (bound n)).mpr hNoSolver⟩
  · rintro ⟨n, h⟩ ⟨solver⟩
    exact (lowerBoundAt_iff_no_solver problem C n (bound n)).mp h
      ⟨BoundedSearchSolver.atLength solver n⟩

/-- A lower bound for a larger budget implies one for every smaller budget. -/
theorem lowerBoundAt_mono {problem : SearchMCSPCompressionProblem}
    {C : CircuitFamilyClass} {n small big : Nat} (hle : small ≤ big)
    (h : LowerBoundAt problem C n big) : LowerBoundAt problem C n small := by
  intro outputCircuit hsize
  exact h outputCircuit (fun i => Nat.le_trans (hsize i) hle)

end Research.LengthwiseSearch
