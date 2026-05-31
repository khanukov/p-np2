import Pnp4.Frontier.SearchMCSPMagnification

namespace Pnp4
namespace Frontier
namespace Tests

/--
Toy interface for encoding/decode/eval in the anti-evaluation diagonal search probe.
The evaluator remains abstract; this file only needs the algebraic contract.
-/
structure AntiEvalEncodingInterface where
  instanceBits : Nat → Nat
  witnessBits : Nat → Nat
  DecodedTuple : Nat → Type
  decodeTuple : ∀ n, AlgorithmsToLowerBounds.BitVec (instanceBits n) → Option (DecodedTuple n)
  evalTuple : ∀ n, DecodedTuple n → AlgorithmsToLowerBounds.BitVec (instanceBits n) → AlgorithmsToLowerBounds.BitVec (witnessBits n)

/-- Pointwise Boolean negation on witness vectors. -/
def bitwiseNot {k : Nat} (w : AlgorithmsToLowerBounds.BitVec k) : AlgorithmsToLowerBounds.BitVec k :=
  fun i => !(w i)

/--
Anti-eval relation at length `n`:
`w` must be exactly the bitwise negation of the decoded tuple's output on `x`.
-/
def antiEvalRelation
    (enc : AntiEvalEncodingInterface)
    (n : Nat)
    (x : AlgorithmsToLowerBounds.BitVec (enc.instanceBits n))
    (w : AlgorithmsToLowerBounds.BitVec (enc.witnessBits n)) : Prop :=
  ∃ G, enc.decodeTuple n x = some G ∧ w = bitwiseNot (enc.evalTuple n G x)

/--
Concrete search target used in this L0 sanity probe.
We keep witnesses one-bit wide so the final contradiction is a direct Bool case.
-/
def antiEvalTarget
    (enc : AntiEvalEncodingInterface)
    (C : AlgorithmsToLowerBounds.CircuitFamilyClass)
    (sizeBound : Nat → Nat)
    (hOneBit : ∀ n, enc.witnessBits n = 1) :
    SearchMCSPWeakCircuitLowerBoundTarget where
  problem :=
    { instanceBits := enc.instanceBits
      witnessBits := enc.witnessBits
      promise := fun n x => ∃ G, enc.decodeTuple n x = some G
      relation := antiEvalRelation enc
      totalOnPromise := by
        intro n x hx
        rcases hx with ⟨G, hDec⟩
        refine ⟨bitwiseNot (enc.evalTuple n G x), ?_⟩
        exact ⟨G, hDec, rfl⟩ }
  circuitClass := C
  sizeBound := sizeBound

/--
Self-encoding capacity hypothesis for anti-eval:
for every bounded solver, there is a promised input that decodes to some `G`
and where `evalTuple` matches the solver output on that same input.
-/
def SelfEncodingCapacity
    (enc : AntiEvalEncodingInterface)
    (C : AlgorithmsToLowerBounds.CircuitFamilyClass)
    (sizeBound : Nat → Nat)
    (hOneBit : ∀ n, enc.witnessBits n = 1) : Prop :=
  ∀ solver : BoundedSearchSolver (antiEvalTarget enc C sizeBound hOneBit).problem C sizeBound,
    ∃ n x G,
      enc.decodeTuple n x = some G ∧
      enc.evalTuple n G x = searchSolverOutput (solver.outputCircuit n) x

/--
Diagonal contradiction at one-bit width:
if `b = !b`, then contradiction.
-/
private theorem bool_not_fixed_point_false (b : Bool) (h : b = !b) : False := by
  cases b <;> simp at h

/--
L0 diagonal sanity theorem: self-encoding capacity rules out bounded solvers.
This is a test-local weak lower-bound probe only; no endpoint claims are made.
-/
theorem antiEval_noBoundedSolver_of_selfEncodingCapacity
    (enc : AntiEvalEncodingInterface)
    (C : AlgorithmsToLowerBounds.CircuitFamilyClass)
    (sizeBound : Nat → Nat)
    (hOneBit : ∀ n, enc.witnessBits n = 1) :
    SelfEncodingCapacity enc C sizeBound hOneBit →
    SearchProblemNoBoundedSolver
      (antiEvalTarget enc C sizeBound hOneBit).problem
      (antiEvalTarget enc C sizeBound hOneBit).circuitClass
      (antiEvalTarget enc C sizeBound hOneBit).sizeBound := by
  intro hCap hSolver
  rcases hSolver with ⟨solver⟩
  rcases hCap solver with ⟨n, x, G, hDec, hEvalEq⟩
  have hProm : (antiEvalTarget enc C sizeBound hOneBit).problem.promise n x := ⟨G, hDec⟩
  have hSolves := solver.solves n x hProm
  rcases hSolves with ⟨G', hDec', hRel⟩
  have hG : G' = G := by
    rw [hDec] at hDec'
    cases hDec'; rfl
  subst hG
  rw [hEvalEq] at hRel
  have hFixed :
      searchSolverOutput (solver.outputCircuit n) x =
        bitwiseNot (searchSolverOutput (solver.outputCircuit n) x) := hRel
  have hPos : 0 < enc.witnessBits n := by simpa [hOneBit n]
  let i0 : Fin (enc.witnessBits n) := ⟨0, hPos⟩
  have hAtZero :
      (searchSolverOutput (solver.outputCircuit n) x) i0 =
      !(searchSolverOutput (solver.outputCircuit n) x) i0 := by
    simpa [bitwiseNot, i0] using congrArg (fun v => v i0) hFixed
  exact bool_not_fixed_point_false _ hAtZero

end Tests
end Frontier
end Pnp4
