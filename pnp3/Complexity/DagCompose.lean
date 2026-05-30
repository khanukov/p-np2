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

/-! ### Composition layer, step 1: input relabelling

`relabelInputs ρ C` reindexes the input wires of `C` by `ρ : Fin n → Fin m`
without touching the gate graph (same gates, same gate references).  This is the
smallest genuine composition primitive: it provides projection/field wiring for
later substitution, and its `eval` lemma is the first `evalGateAt`-induction of
the library (modelled on `evalGateAt_eq_of_eq_on_supportAt`).
-/

/-- Remap the input wires of a wire by `ρ` (gate references unchanged). -/
def mapWireInputs {n m k : Nat} (ρ : Fin n → Fin m) : DagWire n k → DagWire m k
  | .input j => .input (ρ j)
  | .gate g => .gate g

/-- Remap the input wires occurring in a gate by `ρ`. -/
def mapGateInputs {n m k : Nat} (ρ : Fin n → Fin m) : DagGate n k → DagGate m k
  | .const b => .const b
  | .not w => .not (mapWireInputs ρ w)
  | .and w₁ w₂ => .and (mapWireInputs ρ w₁) (mapWireInputs ρ w₂)
  | .or w₁ w₂ => .or (mapWireInputs ρ w₁) (mapWireInputs ρ w₂)

/-- Relabel the inputs of `C` by `ρ`, keeping the gate graph fixed. -/
def relabelInputs {n m : Nat} (ρ : Fin n → Fin m) (C : DagCircuit n) :
    DagCircuit m where
  gates := C.gates
  gate := fun i => mapGateInputs ρ (C.gate i)
  output := mapWireInputs ρ C.output

@[simp] theorem size_relabelInputs {n m : Nat} (ρ : Fin n → Fin m) (C : DagCircuit n) :
    size (relabelInputs ρ C) = size C := rfl

/-- Gate-level evaluation is preserved by input relabelling: evaluating the
relabelled gate at `x` equals evaluating the original gate at `x ∘ ρ`. -/
theorem evalGateAt_relabelInputs {n m : Nat} (ρ : Fin n → Fin m) (C : DagCircuit n) :
    ∀ {i : Nat} (hi : i < C.gates) (x : Bitstring m),
      DagCircuit.eval.evalGateAt (C := relabelInputs ρ C) (x := x) i hi =
        DagCircuit.eval.evalGateAt (C := C) (x := fun j => x (ρ j)) i hi
  | i, hi, x => by
      have hgate : (relabelInputs ρ C).gate ⟨i, hi⟩
            = mapGateInputs ρ (C.gate ⟨i, hi⟩) := rfl
      cases hOp : C.gate ⟨i, hi⟩ with
      | const b =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
          rw [hgate, hOp]
          rfl
      | not w =>
          cases w with
          | input j =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
              rw [hgate, hOp]
              rfl
          | gate j =>
              rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
              rw [hgate, hOp]
              simp only [mapGateInputs, mapWireInputs]
              rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j.2 hi) x]
      | and w₁ w₂ =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
          rw [hgate, hOp]
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ => rfl
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x]
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x,
                      evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
      | or w₁ w₂ =>
          rw [DagCircuit.eval.evalGateAt, DagCircuit.eval.evalGateAt]
          rw [hgate, hOp]
          cases w₁ with
          | input j₁ =>
              cases w₂ with
              | input j₂ => rfl
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
          | gate j₁ =>
              cases w₂ with
              | input j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x]
              | gate j₂ =>
                  simp only [mapGateInputs, mapWireInputs]
                  rw [evalGateAt_relabelInputs ρ C (Nat.lt_trans j₁.2 hi) x,
                      evalGateAt_relabelInputs ρ C (Nat.lt_trans j₂.2 hi) x]
  termination_by i => i

/-- **Input-relabelling correctness.**  Evaluating `relabelInputs ρ C` at `x`
equals evaluating `C` at the relabelled input `fun j => x (ρ j)`. -/
@[simp] theorem eval_relabelInputs {n m : Nat} (ρ : Fin n → Fin m)
    (C : DagCircuit n) (x : Bitstring m) :
    eval (relabelInputs ρ C) x = eval C (fun j => x (ρ j)) := by
  unfold eval
  cases hout : C.output with
  | input j =>
      simp [relabelInputs, mapWireInputs, hout]
  | gate g =>
      have h : (relabelInputs ρ C).output = DagWire.gate g := by
        simp [relabelInputs, mapWireInputs, hout]
      rw [h]
      exact evalGateAt_relabelInputs ρ C g.2 x

end DagCircuit
end ComplexityInterfaces
end Pnp3
