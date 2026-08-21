import Complexity.Interfaces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Union
/-!
# DAG support cardinality

Category: Infrastructure.  This module bounds the existing dependency-closed
`DagCircuit.support`; it does not supply a lower-bound source or make progress
toward `P != NP`.
-/
namespace Pnp3.ComplexityInterfaces.DagCircuit
open scoped BigOperators
/-- Input coordinates mentioned directly by a wire. -/
def wireDirectInputCover {n k : Nat} (w : DagWire n k) : Finset (Fin n) :=
  match w with
  | .input j => {j}
  | .gate _ => ∅
/-- Input coordinates mentioned directly in a gate payload. -/
def gateDirectInputCover {n k : Nat} (g : DagGate n k) : Finset (Fin n) :=
  match g with
  | .const _ => ∅
  | .not w => wireDirectInputCover w
  | .and w₁ w₂ => wireDirectInputCover w₁ ∪ wireDirectInputCover w₂
  | .or w₁ w₂ => wireDirectInputCover w₁ ∪ wireDirectInputCover w₂
/-- All input coordinates mentioned directly anywhere in a DAG circuit. -/
def directInputCover {n : Nat} (C : DagCircuit n) : Finset (Fin n) :=
  wireDirectInputCover C.output ∪
    Finset.univ.biUnion (fun i : Fin C.gates => gateDirectInputCover (C.gate i))
private def wireDependencySupport {n : Nat} (C : DagCircuit n)
    (i : Nat) (hi : i < C.gates) (w : DagWire n i) : Finset (Fin n) :=
  match w with
  | .input j => {j}
  | .gate j => supportAt C j.1 (Nat.lt_trans j.2 hi)
private theorem gateDirectInputCover_subset {n : Nat} (C : DagCircuit n)
    (i : Fin C.gates) : gateDirectInputCover (C.gate i) ⊆ directInputCover C := by
  intro j hj
  exact Finset.mem_union.mpr <| Or.inr <|
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩
/-- Every dependency-closed gate support lies in the circuit's direct-input cover. -/
theorem supportAt_subset_directInputCover {n : Nat} (C : DagCircuit n) :
    ∀ i (hi : i < C.gates), supportAt C i hi ⊆ directInputCover C
  | i, hi => by
      classical
      have hGate := gateDirectInputCover_subset C ⟨i, hi⟩
      have hWire (w : DagWire n i)
          (hw : wireDirectInputCover w ⊆ gateDirectInputCover (C.gate ⟨i, hi⟩)) :
          wireDependencySupport C i hi w ⊆ directInputCover C := by
        cases w with
        | input j => exact Finset.Subset.trans hw hGate
        | gate j => exact supportAt_subset_directInputCover C j.1 (Nat.lt_trans j.2 hi)
      cases hOp : C.gate ⟨i, hi⟩ with
      | const b =>
          rw [supportAt, hOp]
          exact Finset.empty_subset _
      | not w =>
          rw [supportAt, hOp]
          change wireDependencySupport C i hi w ⊆ directInputCover C
          apply hWire w
          rw [hOp]
          exact Finset.Subset.rfl
      | and w₁ w₂ | or w₁ w₂ =>
          rw [supportAt, hOp]
          change wireDependencySupport C i hi w₁ ∪ wireDependencySupport C i hi w₂ ⊆
            directInputCover C
          apply Finset.union_subset
          · apply hWire w₁
            rw [hOp]
            exact Finset.subset_union_left
          · apply hWire w₂
            rw [hOp]
            exact Finset.subset_union_right
/-- The output's dependency-closed support lies in the direct-input cover. -/
theorem support_subset_directInputCover {n : Nat} (C : DagCircuit n) :
    support C ⊆ directInputCover C := by
  classical
  cases hOut : C.output with
  | input j => simp [support, directInputCover, wireDirectInputCover, hOut]
  | gate j =>
      simpa only [support, hOut] using supportAt_subset_directInputCover C j.1 j.2
private theorem wireDirectInputCover_card_le_one {n k : Nat} (w : DagWire n k) :
    (wireDirectInputCover w).card ≤ 1 := by
  cases w <;> simp [wireDirectInputCover]
private theorem gateDirectInputCover_card_le_two {n k : Nat} (g : DagGate n k) :
    (gateDirectInputCover g).card ≤ 2 := by
  cases g with
  | const b => simp [gateDirectInputCover]
  | not w => exact (wireDirectInputCover_card_le_one w).trans (by omega)
  | and w₁ w₂ | or w₁ w₂ =>
      exact (Finset.card_union_le _ _).trans <|
        (Nat.add_le_add (wireDirectInputCover_card_le_one w₁)
          (wireDirectInputCover_card_le_one w₂)).trans (by omega)
/-- The finite direct-input cover has at most two coordinates per size unit. -/
theorem directInputCover_card_le_two_mul_size {n : Nat} (C : DagCircuit n) :
    (directInputCover C).card ≤ 2 * size C := by
  have hSum : (∑ i : Fin C.gates, (gateDirectInputCover (C.gate i)).card) ≤
      2 * C.gates := by
    calc
      _ ≤ ∑ _i : Fin C.gates, 2 :=
        Finset.sum_le_sum (fun i _ => gateDirectInputCover_card_le_two (C.gate i))
      _ = 2 * C.gates := by simp [Fintype.card_fin, Nat.mul_comm]
  calc
    (directInputCover C).card ≤ (wireDirectInputCover C.output).card +
        (Finset.univ.biUnion (fun i : Fin C.gates => gateDirectInputCover (C.gate i))).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + ∑ i : Fin C.gates, (gateDirectInputCover (C.gate i)).card :=
      Nat.add_le_add (wireDirectInputCover_card_le_one C.output) Finset.card_biUnion_le
    _ ≤ 1 + 2 * C.gates := Nat.add_le_add_left hSum 1
    _ ≤ 2 * size C := by simp [size]; omega
/-- A DAG's dependency-closed support has cardinality at most twice its size. -/
theorem support_card_le_two_mul_size {n : Nat} (C : DagCircuit n) :
    (support C).card ≤ 2 * size C :=
  (Finset.card_le_card (support_subset_directInputCover C)).trans
    (directInputCover_card_le_two_mul_size C)
/-- Every DAG has a small coordinate set determining its evaluation. -/
theorem exists_small_evaluation_support {n : Nat} (C : DagCircuit n) :
    ∃ Q : Finset (Fin n), Q.card ≤ 2 * size C ∧
      ∀ {x y : Bitstring n}, (∀ i ∈ Q, x i = y i) → eval C x = eval C y := by
  exact ⟨support C, support_card_le_two_mul_size C, fun h => eval_eq_of_eq_on_support C h⟩
end Pnp3.ComplexityInterfaces.DagCircuit
