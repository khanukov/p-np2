import Complexity.Interfaces
import Mathlib.Tactic

/-!
# DAG-circuit composition library (for the decision→search extraction)

Circuit-composition infrastructure that the pnp4 decision→search *extraction
theorem* needs and that the repository previously lacked (the `DagCircuit` API
had only `eval`, `size`, `support`).

Composition layer — micro-step progress (one reusable primitive per commit):

* step 0 — leaf primitives `inputProj`, `constCircuit` (+ eval/size);  ✓
* step 1 — `relabelInputs` (input reindexing) with eval/size correctness;  ✓
* step 2 — index transport `weakenWireRight`/`shiftWireBy` (+ gate versions):
  the `Fin` arithmetic needed to concatenate gate lists;  ← this commit
* step 3 — `appendCircuit` / multi-output `DagBundle`;
* step 4 — `substInputs` (input substitution) with eval/size lemmas.

Downstream (separate files): greedy `BoundedSearchSolver` assembly →
`PpolyDAG (PrefixExtensionLanguage) → BoundedSearchSolver` and its
contrapositive → replace the abstract `SearchMCSPMagnificationContract` field
(closes the audit hole flagged by the D0 review).

This file introduces **no** endpoint, source theorem, `PpolyDAG` bridge, or
`P ≠ NP` consequence; it is pure circuit plumbing.  The lower bound itself
(`¬BoundedSearchSolver`) is *not* addressed here and remains the open problem.
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

/-! ### Composition layer, step 2: index transport

Two distinct `Fin`-index shifts on wires/gates, kept deliberately separate to
avoid `k + extra` vs `offset + k` arithmetic fights in `append`/`substInputs`:

* `weakenWireRight extra` embeds `Fin k ↪ Fin (k + extra)` (via `Fin.castAdd`) —
  keeps the *first* circuit's gate references valid after appending `extra`
  gates on the right;
* `shiftWireBy offset` embeds `Fin k ↪ Fin (offset + k)` (via `Fin.natAdd`) —
  moves the *second* circuit's local gate references to their global positions.

These are purely index transport: wires/gates have no standalone `eval`, so the
semantic lemmas appear later, with `append`/`substInputs`.
-/

/-- Keep a wire valid after `extra` gates are appended on the right. -/
def weakenWireRight {n k : Nat} (extra : Nat) : DagWire n k → DagWire n (k + extra)
  | .input j => .input j
  | .gate g => .gate (Fin.castAdd extra g)

@[simp] theorem weakenWireRight_input {n k : Nat} (extra : Nat) (j : Fin n) :
    weakenWireRight (n := n) (k := k) extra (DagWire.input j) = DagWire.input j := rfl

@[simp] theorem weakenWireRight_gate {n k : Nat} (extra : Nat) (g : Fin k) :
    weakenWireRight (n := n) extra (DagWire.gate g) = DagWire.gate (Fin.castAdd extra g) := rfl

/-- Shift a wire's gate reference by `offset` (the second circuit in `append`). -/
def shiftWireBy {n k : Nat} (offset : Nat) : DagWire n k → DagWire n (offset + k)
  | .input j => .input j
  | .gate g => .gate (Fin.natAdd offset g)

@[simp] theorem shiftWireBy_input {n k : Nat} (offset : Nat) (j : Fin n) :
    shiftWireBy (n := n) (k := k) offset (DagWire.input j) = DagWire.input j := rfl

@[simp] theorem shiftWireBy_gate {n k : Nat} (offset : Nat) (g : Fin k) :
    shiftWireBy (n := n) offset (DagWire.gate g) = DagWire.gate (Fin.natAdd offset g) := rfl

/-- Gate version of `weakenWireRight`. -/
def weakenGateRight {n k : Nat} (extra : Nat) : DagGate n k → DagGate n (k + extra)
  | .const b => .const b
  | .not w => .not (weakenWireRight extra w)
  | .and w₁ w₂ => .and (weakenWireRight extra w₁) (weakenWireRight extra w₂)
  | .or w₁ w₂ => .or (weakenWireRight extra w₁) (weakenWireRight extra w₂)

/-- Gate version of `shiftWireBy`. -/
def shiftGateBy {n k : Nat} (offset : Nat) : DagGate n k → DagGate n (offset + k)
  | .const b => .const b
  | .not w => .not (shiftWireBy offset w)
  | .and w₁ w₂ => .and (shiftWireBy offset w₁) (shiftWireBy offset w₂)
  | .or w₁ w₂ => .or (shiftWireBy offset w₁) (shiftWireBy offset w₂)

@[simp] theorem weakenGateRight_const {n k : Nat} (extra : Nat) (b : Bool) :
    weakenGateRight (n := n) (k := k) extra (DagGate.const b) = DagGate.const b := rfl

@[simp] theorem shiftGateBy_const {n k : Nat} (offset : Nat) (b : Bool) :
    shiftGateBy (n := n) (k := k) offset (DagGate.const b) = DagGate.const b := rfl

end DagCircuit
end ComplexityInterfaces
end Pnp3
