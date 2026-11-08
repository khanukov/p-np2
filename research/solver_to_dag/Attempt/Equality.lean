import Complexity.DagGadgets
import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP

namespace Research.SolverToDag
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit

/-- Five actual Boolean gates for inequality of two input bits. -/
def bitMismatch : DagCircuit 2 :=
  substInputs orCircuit ![
    substInputs andCircuit ![inputProj 0, substInputs notCircuit ![inputProj 1]],
    substInputs andCircuit ![substInputs notCircuit ![inputProj 0], inputProj 1]]

@[simp] theorem eval_bitMismatch (x : Bitstring 2) :
    eval bitMismatch x = !(x 0 == x 1) := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [bitMismatch, h0, h1]

@[simp] theorem bitMismatch_size : size bitMismatch = 6 := rfl

/-- Relabel the same fixed five-gate comparator, without copying input gates. -/
def pairMismatch {m : Nat} (a b : Fin m) : DagCircuit m :=
  relabelInputs ![a, b] bitMismatch

@[simp] theorem eval_pairMismatch {m : Nat} (a b : Fin m) (x : Bitstring m) :
    eval (pairMismatch a b) x = !(x a == x b) := by
  simp [pairMismatch]

@[simp] theorem pairMismatch_gates {m : Nat} (a b : Fin m) :
    (pairMismatch a b).gates = 5 := rfl

@[simp] theorem pairMismatch_size {m : Nat} (a b : Fin m) :
    size (pairMismatch a b) = 6 := rfl

/-- Compare two width-w vectors. Empty vectors compare equal. -/
def vectorEquality (w : Nat) : DagCircuit (w + w) :=
  substInputs notCircuit ![bigOrCircuit ((List.finRange w).map
    (fun i => pairMismatch (Fin.castAdd w i) (Fin.natAdd w i)))]

theorem vectorEquality_iff (w : Nat) (x : Bitstring (w + w)) :
    eval (vectorEquality w) x = true ↔
      ∀ i : Fin w, x (Fin.castAdd w i) = x (Fin.natAdd w i) := by
  simp [vectorEquality, List.any_eq_false]

theorem vectorEquality_size (w : Nat) :
    size (vectorEquality w) = 6 * w + 3 := by
  simp [vectorEquality, size_substInputs, bundleOfFamily_gates,
    bigOrCircuit_gates, Function.comp_def]
  omega

/-- Exact equality of two physical truth-table vectors, not tree verification. -/
def tableEquality (n : Nat) :
    DagCircuit (Pnp3.Models.Partial.tableLen n + Pnp3.Models.Partial.tableLen n) :=
  vectorEquality (Pnp3.Models.Partial.tableLen n)

theorem tableEquality_capstone (n : Nat)
    (tt predicted : Pnp4.AlgorithmsToLowerBounds.TruthTable n) :
    (eval (tableEquality n) (Fin.addCases tt predicted) = true ↔ tt = predicted) ∧
      size (tableEquality n) = 6 * Pnp3.Models.Partial.tableLen n + 3 := by
  constructor
  · rw [tableEquality, vectorEquality_iff]
    simp only [Fin.addCases_left, Fin.addCases_right]
    exact funext_iff.symm
  · exact vectorEquality_size _

end Research.SolverToDag
