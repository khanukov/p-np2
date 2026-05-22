import Pnp4.Frontier.SearchMCSPMagnification
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter

namespace Pnp4
namespace Frontier

open Pnp3.ComplexityInterfaces

/-- Direct input occurrence for one wire: only `.input` carries a coordinate. -/
def DagWireDirectInputOf
    {n k : Nat}
    (w : DagWire n k)
    (j : Fin n) : Prop :=
  match w with
  | .input i => i = j
  | .gate _ => False

/-- Direct input occurrence for one gate. -/
def DagGateDirectInputOf
    {n k : Nat}
    (g : DagGate n k)
    (j : Fin n) : Prop :=
  match g with
  | .const _ => False
  | .not w => DagWireDirectInputOf w j
  | .and w₁ w₂ => DagWireDirectInputOf w₁ j ∨ DagWireDirectInputOf w₂ j
  | .or w₁ w₂ => DagWireDirectInputOf w₁ j ∨ DagWireDirectInputOf w₂ j

/-- Direct input occurrence for the output wire itself. -/
def DagOutputDirectInputOf
    {n gates : Nat}
    (w : DagWire n gates)
    (j : Fin n) : Prop :=
  match w with
  | .input i => i = j
  | .gate _ => False

/-- Circuit-level direct input occurrence: output wire or one gate payload wire. -/
def DagCircuitDirectInputOf
    {n : Nat}
    (C : DagCircuit n)
    (j : Fin n) : Prop :=
  DagOutputDirectInputOf C.output j ∨
    ∃ i : Fin C.gates, DagGateDirectInputOf (C.gate i) j

/-- Gate-evaluation invariance under agreement on every circuit direct input. -/
theorem evalGateAt_eq_of_eq_on_direct_inputs
    {n : Nat}
    (C : DagCircuit n) :
    ∀ {i : Nat} (hi : i < C.gates) {x y : Bitstring n},
      (∀ j : Fin n, DagCircuitDirectInputOf C j → x j = y j) →
        DagCircuit.eval.evalGateAt (C := C) (x := x) i hi =
          DagCircuit.eval.evalGateAt (C := C) (x := y) i hi
  | i, hi, x, y, hxy => by
      classical
      cases hGate : C.gate ⟨i, hi⟩ with
      | const b =>
          simpa only [DagCircuit.eval.evalGateAt, hGate]
      | not w =>
          have hWire :
              match w with
              | .input j => x j = y j
              | .gate j =>
                  DagCircuit.eval.evalGateAt (C := C) (x := x) j.1 (Nat.lt_trans j.2 hi) =
                    DagCircuit.eval.evalGateAt (C := C) (x := y) j.1 (Nat.lt_trans j.2 hi) := by
            cases w with
            | input j =>
                have hOccGate : DagGateDirectInputOf (C.gate ⟨i, hi⟩) j := by
                  rw [hGate]
                  simp [DagGateDirectInputOf, DagWireDirectInputOf]
                have hOcc : DagCircuitDirectInputOf C j := by
                  exact Or.inr ⟨⟨i, hi⟩, hOccGate⟩
                exact hxy j hOcc
            | gate j =>
                exact evalGateAt_eq_of_eq_on_direct_inputs (C := C)
                  (hi := Nat.lt_trans j.2 hi) (x := x) (y := y) hxy
          cases w with
          | input j =>
              rw [DagCircuit.eval.evalGateAt, hGate]
              rw [DagCircuit.eval.evalGateAt, hGate]
              exact congrArg (fun b => !b) hWire
          | gate j =>
              rw [DagCircuit.eval.evalGateAt, hGate]
              rw [DagCircuit.eval.evalGateAt, hGate]
              simpa using hWire
      | and w₁ w₂ =>
          have hWire₁ :
              match w₁ with
              | .input j => x j = y j
              | .gate j =>
                  DagCircuit.eval.evalGateAt (C := C) (x := x) j.1 (Nat.lt_trans j.2 hi) =
                    DagCircuit.eval.evalGateAt (C := C) (x := y) j.1 (Nat.lt_trans j.2 hi) := by
            cases w₁ with
            | input j =>
                have hOccGate : DagGateDirectInputOf (C.gate ⟨i, hi⟩) j := by
                  rw [hGate]
                  simp [DagGateDirectInputOf, DagWireDirectInputOf]
                have hOcc : DagCircuitDirectInputOf C j := Or.inr ⟨⟨i, hi⟩, hOccGate⟩
                exact hxy j hOcc
            | gate j =>
                exact evalGateAt_eq_of_eq_on_direct_inputs (C := C)
                  (hi := Nat.lt_trans j.2 hi) (x := x) (y := y) hxy
          have hWire₂ :
              match w₂ with
              | .input j => x j = y j
              | .gate j =>
                  DagCircuit.eval.evalGateAt (C := C) (x := x) j.1 (Nat.lt_trans j.2 hi) =
                    DagCircuit.eval.evalGateAt (C := C) (x := y) j.1 (Nat.lt_trans j.2 hi) := by
            cases w₂ with
            | input j =>
                have hOccGate : DagGateDirectInputOf (C.gate ⟨i, hi⟩) j := by
                  rw [hGate]
                  simp [DagGateDirectInputOf, DagWireDirectInputOf]
                have hOcc : DagCircuitDirectInputOf C j := Or.inr ⟨⟨i, hi⟩, hOccGate⟩
                exact hxy j hOcc
            | gate j =>
                exact evalGateAt_eq_of_eq_on_direct_inputs (C := C)
                  (hi := Nat.lt_trans j.2 hi) (x := x) (y := y) hxy
          cases w₁ <;> cases w₂
          all_goals
            rw [DagCircuit.eval.evalGateAt, hGate]
            rw [DagCircuit.eval.evalGateAt, hGate]
            simp [hWire₁, hWire₂]
      | or w₁ w₂ =>
          have hWire₁ :
              match w₁ with
              | .input j => x j = y j
              | .gate j =>
                  DagCircuit.eval.evalGateAt (C := C) (x := x) j.1 (Nat.lt_trans j.2 hi) =
                    DagCircuit.eval.evalGateAt (C := C) (x := y) j.1 (Nat.lt_trans j.2 hi) := by
            cases w₁ with
            | input j =>
                have hOccGate : DagGateDirectInputOf (C.gate ⟨i, hi⟩) j := by
                  rw [hGate]
                  simp [DagGateDirectInputOf, DagWireDirectInputOf]
                have hOcc : DagCircuitDirectInputOf C j := Or.inr ⟨⟨i, hi⟩, hOccGate⟩
                exact hxy j hOcc
            | gate j =>
                exact evalGateAt_eq_of_eq_on_direct_inputs (C := C)
                  (hi := Nat.lt_trans j.2 hi) (x := x) (y := y) hxy
          have hWire₂ :
              match w₂ with
              | .input j => x j = y j
              | .gate j =>
                  DagCircuit.eval.evalGateAt (C := C) (x := x) j.1 (Nat.lt_trans j.2 hi) =
                    DagCircuit.eval.evalGateAt (C := C) (x := y) j.1 (Nat.lt_trans j.2 hi) := by
            cases w₂ with
            | input j =>
                have hOccGate : DagGateDirectInputOf (C.gate ⟨i, hi⟩) j := by
                  rw [hGate]
                  simp [DagGateDirectInputOf, DagWireDirectInputOf]
                have hOcc : DagCircuitDirectInputOf C j := Or.inr ⟨⟨i, hi⟩, hOccGate⟩
                exact hxy j hOcc
            | gate j =>
                exact evalGateAt_eq_of_eq_on_direct_inputs (C := C)
                  (hi := Nat.lt_trans j.2 hi) (x := x) (y := y) hxy
          cases w₁ <;> cases w₂
          all_goals
            rw [DagCircuit.eval.evalGateAt, hGate]
            rw [DagCircuit.eval.evalGateAt, hGate]
            simp [hWire₁, hWire₂]

/-- Whole-circuit evaluation invariance under direct-input agreement. -/
theorem DagCircuit_eval_eq_of_eq_on_direct_inputs
    {n : Nat}
    (C : DagCircuit n)
    {x y : Bitstring n}
    (hxy : ∀ j : Fin n, DagCircuitDirectInputOf C j → x j = y j) :
    DagCircuit.eval C x = DagCircuit.eval C y := by
  classical
  cases hOut : C.output with
  | input j =>
      have hOcc : DagCircuitDirectInputOf C j := Or.inl (by simp [DagOutputDirectInputOf, hOut])
      have hEq : x j = y j := hxy j hOcc
      simpa [DagCircuit.eval, hOut] using hEq
  | gate j =>
      simpa [DagCircuit.eval, hOut] using
        evalGateAt_eq_of_eq_on_direct_inputs (C := C) (hi := j.2) (x := x) (y := y) hxy

end Frontier
end Pnp4
