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

/-- Finite direct-input cover extracted from one wire. -/
def dagWireDirectInputCover
    {n k : Nat}
    (w : DagWire n k) : Finset (Fin n) :=
  match w with
  | .input j => {j}
  | .gate _ => ∅

/-- Finite direct-input cover extracted from one gate. -/
def dagGateDirectInputCover
    {n k : Nat}
    (g : DagGate n k) : Finset (Fin n) :=
  match g with
  | .const _ => ∅
  | .not w => dagWireDirectInputCover w
  | .and w₁ w₂ => dagWireDirectInputCover w₁ ∪ dagWireDirectInputCover w₂
  | .or w₁ w₂ => dagWireDirectInputCover w₁ ∪ dagWireDirectInputCover w₂

/-- Finite direct-input cover extracted from the output wire itself. -/
def dagOutputDirectInputCover
    {n gates : Nat}
    (w : DagWire n gates) : Finset (Fin n) :=
  match w with
  | .input j => {j}
  | .gate _ => ∅

/-- Finite circuit-level cover of all direct input occurrences. -/
def dagDirectInputCover
    {n : Nat}
    (C : DagCircuit n) : Finset (Fin n) :=
  dagOutputDirectInputCover C.output ∪
    Finset.univ.biUnion (fun i : Fin C.gates => dagGateDirectInputCover (C.gate i))

theorem DagWireDirectInputOf_iff_mem_cover
    {n k : Nat} (w : DagWire n k) (j : Fin n) :
    DagWireDirectInputOf w j ↔ j ∈ dagWireDirectInputCover w := by
  cases w with
  | input a =>
      constructor <;> intro h
      · have ha : a = j := by simpa [DagWireDirectInputOf] using h
        simpa [dagWireDirectInputCover] using ha.symm
      · have hj : j = a := by simpa [dagWireDirectInputCover] using h
        simpa [DagWireDirectInputOf] using hj.symm
  | gate g => simp [DagWireDirectInputOf, dagWireDirectInputCover]

theorem DagOutputDirectInputOf_iff_mem_cover
    {n gates : Nat} (w : DagWire n gates) (j : Fin n) :
    DagOutputDirectInputOf w j ↔ j ∈ dagOutputDirectInputCover w := by
  cases w with
  | input a =>
      constructor <;> intro h
      · have ha : a = j := by simpa [DagOutputDirectInputOf] using h
        simpa [dagOutputDirectInputCover] using ha.symm
      · have hj : j = a := by simpa [dagOutputDirectInputCover] using h
        simpa [DagOutputDirectInputOf] using hj.symm
  | gate g => simp [DagOutputDirectInputOf, dagOutputDirectInputCover]

theorem DagGateDirectInputOf_mem_cover
    {n k : Nat} (g : DagGate n k) (j : Fin n) :
    DagGateDirectInputOf g j → j ∈ dagGateDirectInputCover g := by
  intro h
  cases g with
  | const b => cases h
  | not w =>
      simpa [dagGateDirectInputCover] using (DagWireDirectInputOf_iff_mem_cover w j).mp h
  | and w₁ w₂ =>
      rcases h with h1 | h2
      · exact Finset.mem_union.mpr <| Or.inl ((DagWireDirectInputOf_iff_mem_cover w₁ j).mp h1)
      · exact Finset.mem_union.mpr <| Or.inr ((DagWireDirectInputOf_iff_mem_cover w₂ j).mp h2)
  | or w₁ w₂ =>
      rcases h with h1 | h2
      · exact Finset.mem_union.mpr <| Or.inl ((DagWireDirectInputOf_iff_mem_cover w₁ j).mp h1)
      · exact Finset.mem_union.mpr <| Or.inr ((DagWireDirectInputOf_iff_mem_cover w₂ j).mp h2)

theorem DagCircuitDirectInputOf_mem_cover
    {n : Nat} (C : DagCircuit n) (j : Fin n)
    (h : DagCircuitDirectInputOf C j) :
    j ∈ dagDirectInputCover C := by
  rcases h with hOut | ⟨i, hGate⟩
  · exact Finset.mem_union.mpr <| Or.inl ((DagOutputDirectInputOf_iff_mem_cover C.output j).mp hOut)
  · exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_biUnion.mpr ⟨i, by
        exact ⟨by simp, DagGateDirectInputOf_mem_cover (C.gate i) j hGate⟩⟩

theorem dagWireDirectInputCover_card_le_one
    {n k : Nat} (w : DagWire n k) :
    (dagWireDirectInputCover w).card ≤ 1 := by
  cases w <;> simp [dagWireDirectInputCover]

theorem dagGateDirectInputCover_card_le_two
    {n k : Nat} (g : DagGate n k) :
    (dagGateDirectInputCover g).card ≤ 2 := by
  cases g with
  | const b => simp [dagGateDirectInputCover]
  | not w => exact Nat.le_trans (dagWireDirectInputCover_card_le_one w) (by decide)
  | and w₁ w₂ =>
      calc
        (dagGateDirectInputCover (.and w₁ w₂)).card
            ≤ (dagWireDirectInputCover w₁).card + (dagWireDirectInputCover w₂).card :=
              Finset.card_union_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (dagWireDirectInputCover_card_le_one w₁)
              (dagWireDirectInputCover_card_le_one w₂)
        _ = 2 := by decide
  | or w₁ w₂ =>
      calc
        (dagGateDirectInputCover (.or w₁ w₂)).card
            ≤ (dagWireDirectInputCover w₁).card + (dagWireDirectInputCover w₂).card :=
              Finset.card_union_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (dagWireDirectInputCover_card_le_one w₁)
              (dagWireDirectInputCover_card_le_one w₂)
        _ = 2 := by decide

theorem dagOutputDirectInputCover_card_le_one
    {n gates : Nat} (w : DagWire n gates) :
    (dagOutputDirectInputCover w).card ≤ 1 := by
  cases w <;> simp [dagOutputDirectInputCover]

theorem dagDirectInputCover_card_le_two_mul_size
    {n : Nat}
    (C : DagCircuit n) :
    (dagDirectInputCover C).card ≤ 2 * DagCircuit.size C := by
  have hBiUnion :
      (Finset.univ.biUnion (fun i : Fin C.gates => dagGateDirectInputCover (C.gate i))).card
        ≤ ∑ i : Fin C.gates, (dagGateDirectInputCover (C.gate i)).card :=
    Finset.card_biUnion_le
  have hSum :
      (∑ i : Fin C.gates, (dagGateDirectInputCover (C.gate i)).card) ≤ 2 * C.gates := by
    calc
      (∑ i : Fin C.gates, (dagGateDirectInputCover (C.gate i)).card)
          ≤ ∑ _i : Fin C.gates, 2 :=
            Finset.sum_le_sum (fun i _ => dagGateDirectInputCover_card_le_two (C.gate i))
      _ = 2 * C.gates := by simp [Nat.mul_comm]
  have hOut := dagOutputDirectInputCover_card_le_one C.output
  calc
    (dagDirectInputCover C).card
        ≤ (dagOutputDirectInputCover C.output).card +
            (Finset.univ.biUnion (fun i : Fin C.gates => dagGateDirectInputCover (C.gate i))).card :=
          Finset.card_union_le _ _
    _ ≤ 1 + (2 * C.gates) := Nat.add_le_add hOut (Nat.le_trans hBiUnion hSum)
    _ ≤ 2 * DagCircuit.size C := by
      simpa [DagCircuit.size, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Nat.succ_le_succ (Nat.le_add_left (2 * C.gates) 1)

theorem DagCircuit_exists_small_direct_input_cover
    {n : Nat}
    (C : DagCircuit n) :
    ∃ Q : Finset (Fin n),
      Q.card ≤ 2 * DagCircuit.size C ∧
        ∀ x y : Bitstring n,
          (∀ i ∈ Q, x i = y i) →
            DagCircuit.eval C x = DagCircuit.eval C y := by
  refine ⟨dagDirectInputCover C, dagDirectInputCover_card_le_two_mul_size C, ?_⟩
  intro x y hQ
  apply DagCircuit_eval_eq_of_eq_on_direct_inputs (C := C)
  intro j hDirect
  exact hQ j (DagCircuitDirectInputOf_mem_cover C j hDirect)

end Frontier
end Pnp4
