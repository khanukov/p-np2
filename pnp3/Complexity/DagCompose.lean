import Complexity.Interfaces
import Mathlib.Tactic

/-!
# DAG-circuit composition library (stage 1 of the decision→search extraction)

This module starts the circuit-composition infrastructure that the pnp4
decision→search *extraction theorem* needs and that the repository currently
lacks (the `DagCircuit` API previously had only `eval`, `size`, `support`).

Goal of the wider program (honest scope):

* stage 1 (**this file, in progress**): composition primitives for the
  dependent-indexed `DagCircuit` with `eval`- and `size`-lemmas;
* stage 2: greedy multi-output assembly of a `BoundedSearchSolver` from a
  prefix-extension-language decider;
* stage 3: `PpolyDAG (PrefixExtensionLanguage) → BoundedSearchSolver`, and its
  contrapositive `¬BoundedSearchSolver → ¬PpolyDAG (PrefixExtensionLanguage)`;
* stage 4: replace the abstract `SearchMCSPMagnificationContract` field by that
  proven chain (closes the audit hole flagged by the D0 review).

This file introduces **no** endpoint, source theorem, `PpolyDAG` bridge, or
`P ≠ NP` consequence; it is pure circuit plumbing.  The lower bound itself
(`¬BoundedSearchSolver`) is *not* addressed here and remains the open problem.

Stage-1 milestone 1: leaf primitives (`inputProj`, `constCircuit`) with their
`eval`/`size` lemmas — the certain base cases of any composition.
-/

namespace Pnp3
namespace ComplexityInterfaces
namespace DagCircuit

/-- The projection circuit: zero gates, output is input wire `j`. -/
def inputProj {n : Nat} (j : Fin n) : DagCircuit n where
  gates := 0
  gate := fun i => absurd i.2 (Nat.not_lt_zero i.1)
  output := DagWire.input j

@[simp] theorem eval_inputProj {n : Nat} (j : Fin n) (x : Bitstring n) :
    eval (inputProj j) x = x j := rfl

@[simp] theorem size_inputProj {n : Nat} (j : Fin n) :
    size (inputProj j) = 1 := rfl

/-- The constant circuit: one `const b` gate, output is that gate. -/
def constCircuit (n : Nat) (b : Bool) : DagCircuit n where
  gates := 1
  gate := fun _ => DagGate.const b
  output := DagWire.gate ⟨0, Nat.zero_lt_one⟩

@[simp] theorem eval_constCircuit {n : Nat} (b : Bool) (x : Bitstring n) :
    eval (constCircuit n b) x = b := by
  unfold eval
  unfold DagCircuit.eval.evalGateAt
  rfl

@[simp] theorem size_constCircuit (n : Nat) (b : Bool) :
    size (constCircuit n b) = 2 := rfl

end DagCircuit
end ComplexityInterfaces
end Pnp3
