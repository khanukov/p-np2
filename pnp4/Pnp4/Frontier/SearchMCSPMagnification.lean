import Pnp4.Frontier.CompressionMagnification

namespace Pnp4
namespace Frontier

open AlgorithmsToLowerBounds

/--
Search/compression problem surface for the P-vs-NP mainline.

At length `n`, an instance has `instanceBits n` bits and a valid witness has
`witnessBits n` bits.  The relation is intentionally generic enough to cover
search-MCSP and resource-bounded-compression targets, but concrete enough that
weak lower bounds talk about circuit families producing witnesses.
-/
structure SearchMCSPCompressionProblem where
  instanceBits : Nat → Nat
  witnessBits : Nat → Nat
  promise :
    ∀ n : Nat,
      AlgorithmsToLowerBounds.BitVec (instanceBits n) →
        Prop
  relation :
    ∀ n : Nat,
      AlgorithmsToLowerBounds.BitVec (instanceBits n) →
        AlgorithmsToLowerBounds.BitVec (witnessBits n) →
          Prop
  totalOnPromise :
    ∀ n : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (instanceBits n),
      promise n x →
        ∃ w : AlgorithmsToLowerBounds.BitVec (witnessBits n),
          relation n x w

/-- Output vector produced by one Boolean circuit per witness bit. -/
def searchSolverOutput
    {problem : SearchMCSPCompressionProblem}
    {C : CircuitFamilyClass}
    {n : Nat}
    (solver : ∀ _ : Fin (problem.witnessBits n), C.Family (problem.instanceBits n))
    (x : AlgorithmsToLowerBounds.BitVec (problem.instanceBits n)) :
    AlgorithmsToLowerBounds.BitVec (problem.witnessBits n) :=
  fun i => C.eval (solver i) x

/--
A non-uniform bounded search solver.

The solver uses one circuit from `C` for each output bit and must produce a
valid witness for every input at every length.  `sizeBound` is the weak regime
under attack, e.g. near-linear size for a restricted circuit class.
-/
structure BoundedSearchSolver
    (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass)
    (sizeBound : Nat → Nat) where
  outputCircuit :
    ∀ n : Nat,
      Fin (problem.witnessBits n) →
        C.Family (problem.instanceBits n)
  size_le :
    ∀ n : Nat, ∀ i : Fin (problem.witnessBits n),
      C.size (outputCircuit n i) ≤ sizeBound n
  solves :
    ∀ n : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (problem.instanceBits n),
      problem.promise n x →
        problem.relation n x (searchSolverOutput (outputCircuit n) x)

/-- The weak lower-bound proposition: no bounded solver exists. -/
def SearchProblemNoBoundedSolver
    (problem : SearchMCSPCompressionProblem)
    (C : CircuitFamilyClass)
    (sizeBound : Nat → Nat) : Prop :=
  ¬ Nonempty (BoundedSearchSolver problem C sizeBound)

/--
Falsifiable target for the compression/search-MCSP magnification mainline.

Unlike the older `SearchMCSPWeakLowerBound.weakLowerBound : Prop` surface, this
records the search problem, circuit class, and size schedule that are actually
being ruled out.
-/
structure SearchMCSPWeakCircuitLowerBoundTarget where
  problem : SearchMCSPCompressionProblem
  circuitClass : CircuitFamilyClass
  sizeBound : Nat → Nat

/-- The target's concrete lower-bound proposition. -/
def SearchMCSPWeakCircuitLowerBoundTarget.noBoundedSolver
    (target : SearchMCSPWeakCircuitLowerBoundTarget) : Prop :=
  SearchProblemNoBoundedSolver
    target.problem
    target.circuitClass
    target.sizeBound

/-- A proved weak search/compression lower bound for a concrete target. -/
structure SearchMCSPWeakCircuitLowerBound
    (target : SearchMCSPWeakCircuitLowerBoundTarget) where
  noBoundedSolver : target.noBoundedSolver

/--
Published/theorem-facing magnification step.

This is the mainline source theorem shape: once the concrete weak lower bound
is proved, it must magnify to a verified `NP` language lower bound against
`PpolyDAG`.
-/
structure SearchMCSPMagnificationContract
    (target : SearchMCSPWeakCircuitLowerBoundTarget) where
  magnifiesToVerifiedDAGSource :
    target.noBoundedSolver → VerifiedNPDAGLowerBoundSource

/-- Convert the concrete weak-lower-bound target to the older package surface. -/
def SearchMCSPWeakLowerBound.of_weakCircuitLowerBound
    {target : SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : SearchMCSPWeakCircuitLowerBound target)
    (hMag : SearchMCSPMagnificationContract target) :
    SearchMCSPWeakLowerBound where
  weakLowerBound := target.noBoundedSolver
  weakLowerBoundProof := hWeak.noBoundedSolver
  magnifiesToVerifiedDAGSource := hMag.magnifiesToVerifiedDAGSource

/-- Extract the verified DAG source from a concrete weak lower-bound package. -/
def SearchMCSPWeakCircuitLowerBound.verifiedSource
    {target : SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : SearchMCSPWeakCircuitLowerBound target)
    (hMag : SearchMCSPMagnificationContract target) :
    VerifiedNPDAGLowerBoundSource :=
  (SearchMCSPWeakLowerBound.of_weakCircuitLowerBound hWeak hMag).verifiedSource

/-- Concrete weak search/compression lower bounds yield `NP not_subset P/poly`. -/
theorem NP_not_subset_Ppoly_of_weakCircuitLowerBound
    {target : SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : SearchMCSPWeakCircuitLowerBound target)
    (hMag : SearchMCSPMagnificationContract target) :
    NP_not_subset_Ppoly :=
  NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound
    (SearchMCSPWeakLowerBound.of_weakCircuitLowerBound hWeak hMag)

/-- Final consequence for the concrete compression/search-MCSP mainline source. -/
theorem P_ne_NP_of_weakCircuitLowerBound
    {target : SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : SearchMCSPWeakCircuitLowerBound target)
    (hMag : SearchMCSPMagnificationContract target) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_searchMCSPWeakLowerBound
    (SearchMCSPWeakLowerBound.of_weakCircuitLowerBound hWeak hMag)

/-- Concrete weak search/compression lower bounds are accepted mainline progress. -/
def PvsNPMainlineProgress.of_weakCircuitLowerBound
    {target : SearchMCSPWeakCircuitLowerBoundTarget}
    (hWeak : SearchMCSPWeakCircuitLowerBound target)
    (hMag : SearchMCSPMagnificationContract target) :
    PvsNPMainlineProgress where
  verifiedSource := hWeak.verifiedSource hMag

end Frontier
end Pnp4
