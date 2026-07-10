import Complexity.Interfaces
import Mathlib.Tactic

/-!
# Standard topologically ordered Boolean DAG circuits

This module provides a serialisation-friendly, list-backed presentation of
ordinary Boolean DAG circuits.  External inputs occupy wire indices
`0, ..., n - 1`; at gate position `i`, the already available gates occupy
wire indices `n, ..., n + i - 1`.  Thus the bound `ref < n + i` enforces
acyclicity directly from the list order.

The semantics are exported through the frozen pnp3 `DagCircuit` evaluator.
The conventional internal-gate count is kept separate from the frozen pnp3
size convention, under which `DagCircuit.size C = C.gates + 1`.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StandardDAG

open Pnp3.ComplexityInterfaces

/-- One gate in a flat topologically ordered Boolean DAG.  Natural-number
references use the common input-then-gate wire space described above. -/
inductive FlatGate where
  | const (value : Bool)
  | notGate (src : Nat)
  | andGate (left right : Nat)
  | orGate (left right : Nat)
  deriving DecidableEq, Repr

namespace FlatGate

/-- A gate at position `i` is valid when every non-constant input references
an external input or a strictly earlier gate. -/
def Valid (gate : FlatGate) (n i : Nat) : Prop :=
  match gate with
  | .const _ => True
  | .notGate src => src < n + i
  | .andGate left right => left < n + i ∧ right < n + i
  | .orGate left right => left < n + i ∧ right < n + i

/-- Gate validity is executable. -/
instance instDecidableValid (gate : FlatGate) (n i : Nat) :
    Decidable (gate.Valid n i) := by
  cases gate <;> simp [Valid] <;> infer_instance

/-- The exact oracle-free MMW basis contains only `NOT`, fan-in-two `AND`,
and fan-in-two `OR`.  Constants remain in the structural carrier solely so
that it stays exactly equivalent to the frozen repository `DagCircuit`; the
target MCSP predicate below filters them out explicitly. -/
def InPaperBasis (gate : FlatGate) : Prop :=
  match gate with
  | .const _ => False
  | .notGate _ | .andGate _ _ | .orGate _ _ => True

instance instDecidableInPaperBasis (gate : FlatGate) :
    Decidable gate.InPaperBasis := by
  cases gate with
  | const _ => exact isFalse (fun h => h.elim)
  | notGate _ => exact isTrue trivial
  | andGate _ _ => exact isTrue trivial
  | orGate _ _ => exact isTrue trivial

end FlatGate

/-- Raw list-backed circuit data.  Validity is kept separately so decoding can
first parse raw data and then reject forward or out-of-range references. -/
structure FlatCircuitData where
  gateCount : Nat
  gates : List FlatGate
  output : Nat
  deriving DecidableEq, Repr

namespace FlatCircuitData

/-- Every gate references only inputs or earlier gates, and the designated
output references either an input or one of the listed gates. -/
def Valid (circuit : FlatCircuitData) (n : Nat) : Prop :=
  circuit.gates.length = circuit.gateCount ∧
    (∀ i : Fin circuit.gates.length,
      (circuit.gates.get i).Valid n i.val) ∧
    circuit.output < n + circuit.gateCount

/-- Whole-circuit validity is executable; no classical decision procedure is
used by the future decoder. -/
instance instDecidableValid (circuit : FlatCircuitData) (n : Nat) :
    Decidable (circuit.Valid n) := by
  unfold Valid
  letI : Decidable
      (∀ i : Fin circuit.gates.length,
        (circuit.gates.get i).Valid n i.val) :=
    Fintype.decidableForallFintype
  infer_instance

/-- Every active internal gate belongs to the exact AND/OR/NOT paper basis. -/
def UsesOnlyAndOrNot (circuit : FlatCircuitData) : Prop :=
  forall i : Fin circuit.gates.length,
    (circuit.gates.get i).InPaperBasis

instance instDecidableUsesOnlyAndOrNot (circuit : FlatCircuitData) :
    Decidable circuit.UsesOnlyAndOrNot := by
  unfold UsesOnlyAndOrNot
  exact Fintype.decidableForallFintype

end FlatCircuitData

/-- A standard fan-in-two, topologically ordered Boolean DAG on `n` external
inputs. -/
abbrev FlatCircuit (n : Nat) :=
  { circuit : FlatCircuitData // circuit.Valid n }

namespace FlatCircuit

/-- Conventional circuit size used by MMW: the number of internal gates. -/
def gateCount {n : Nat} (circuit : FlatCircuit n) : Nat :=
  circuit.val.gateCount

/-- Exact target-basis predicate used by standard-DAG MCSP. -/
def UsesOnlyAndOrNot {n : Nat} (circuit : FlatCircuit n) : Prop :=
  circuit.val.UsesOnlyAndOrNot

instance instDecidableUsesOnlyAndOrNot {n : Nat} (circuit : FlatCircuit n) :
    Decidable circuit.UsesOnlyAndOrNot :=
  FlatCircuitData.instDecidableUsesOnlyAndOrNot circuit.val

@[simp] theorem gates_length {n : Nat} (circuit : FlatCircuit n) :
    circuit.val.gates.length = circuit.gateCount :=
  circuit.property.1

/-- Translate a common-space natural-number reference to the dependent pnp3
wire type. -/
def refToDagWire {n i : Nat} (ref : Nat) (href : ref < n + i) :
    DagWire n i := by
  by_cases hInput : ref < n
  · exact .input ⟨ref, hInput⟩
  · exact .gate ⟨ref - n, by omega⟩

/-- Translate one valid flat gate to the corresponding dependent pnp3 gate. -/
def gateToDag {n i : Nat} (gate : FlatGate) (hgate : gate.Valid n i) :
    DagGate n i := by
  cases gate with
  | const value =>
      exact .const value
  | notGate src =>
      exact .not (refToDagWire src hgate)
  | andGate left right =>
      exact .and (refToDagWire left hgate.1) (refToDagWire right hgate.2)
  | orGate left right =>
      exact .or (refToDagWire left hgate.1) (refToDagWire right hgate.2)

/-- Canonical embedding into the frozen pnp3 DAG representation. -/
def toDag {n : Nat} (circuit : FlatCircuit n) : DagCircuit n where
  gates := circuit.val.gateCount
  gate := fun i =>
    let j : Fin circuit.val.gates.length :=
      Fin.cast circuit.property.1.symm i
    gateToDag (circuit.val.gates.get j) (by
      simpa [j] using circuit.property.2.1 j)
  output := refToDagWire circuit.val.output circuit.property.2.2

/-- Semantics of a flat circuit, by the frozen pnp3 DAG evaluator. -/
def eval {n : Nat} (circuit : FlatCircuit n)
    (input : Bitstring n) : Bool :=
  DagCircuit.eval circuit.toDag input

@[simp] theorem toDag_gates {n : Nat} (circuit : FlatCircuit n) :
    circuit.toDag.gates = circuit.gateCount :=
  rfl

/-- Exact reconciliation with the frozen pnp3 size convention. -/
@[simp] theorem toDag_size {n : Nat} (circuit : FlatCircuit n) :
    DagCircuit.size circuit.toDag = circuit.gateCount + 1 :=
  rfl

@[simp] theorem eval_toDag {n : Nat} (circuit : FlatCircuit n)
    (input : Bitstring n) :
    DagCircuit.eval circuit.toDag input = circuit.eval input :=
  rfl

/-- A paper gate threshold `s` is exactly the frozen pnp3 threshold `s + 1`.
This theorem records the shift rather than changing either size convention. -/
theorem gateCount_le_iff_toDag_size_le_succ
    {n : Nat} (circuit : FlatCircuit n) (s : Nat) :
    circuit.gateCount ≤ s ↔ DagCircuit.size circuit.toDag ≤ s + 1 := by
  simp only [toDag_size, Nat.add_le_add_iff_right]

/-! ## Exact inverse bridge to the frozen pnp3 DAG representation -/

/-- Encode a dependent pnp3 wire in the common natural-number wire space. -/
def dagWireToRef {n i : Nat} : DagWire n i → Nat
  | .input input => input.val
  | .gate gate => n + gate.val

/-- Every encoded dependent wire is in the common-space range. -/
theorem dagWireToRef_lt {n i : Nat} (wire : DagWire n i) :
    dagWireToRef wire < n + i := by
  cases wire with
  | input input =>
      simp only [dagWireToRef]
      omega
  | gate gate =>
      simp only [dagWireToRef]
      omega

@[simp] theorem dagWireToRef_refToDagWire
    {n i : Nat} (ref : Nat) (href : ref < n + i) :
    dagWireToRef (refToDagWire ref href) = ref := by
  by_cases hInput : ref < n
  · simp [refToDagWire, hInput, dagWireToRef]
  · simp [refToDagWire, hInput, dagWireToRef]
    omega

@[simp] theorem refToDagWire_dagWireToRef
    {n i : Nat} (wire : DagWire n i) :
    refToDagWire (dagWireToRef wire) (dagWireToRef_lt wire) = wire := by
  cases wire with
  | input input =>
      change refToDagWire input.val _ = .input input
      unfold refToDagWire
      split
      next hInput =>
        apply congrArg DagWire.input
        apply Fin.ext
        rfl
      next hInput =>
        exact (hInput input.isLt).elim
  | gate gate =>
      change refToDagWire (n + gate.val) _ = .gate gate
      unfold refToDagWire
      split
      · omega
      · apply congrArg DagWire.gate
        apply Fin.ext
        exact Nat.add_sub_cancel_left n gate.val

/-- Flatten one dependent pnp3 gate. -/
def gateOfDag {n i : Nat} : DagGate n i → FlatGate
  | .const value => .const value
  | .not wire => .notGate (dagWireToRef wire)
  | .and left right => .andGate (dagWireToRef left) (dagWireToRef right)
  | .or left right => .orGate (dagWireToRef left) (dagWireToRef right)

/-- Flattening a dependent gate automatically satisfies the positional
validity predicate. -/
theorem gateOfDag_valid {n i : Nat} (gate : DagGate n i) :
    (gateOfDag gate).Valid n i := by
  cases gate with
  | const value =>
      simp [gateOfDag, FlatGate.Valid]
  | not wire =>
      simpa [gateOfDag, FlatGate.Valid] using dagWireToRef_lt wire
  | and left right =>
      exact ⟨dagWireToRef_lt left, dagWireToRef_lt right⟩
  | or left right =>
      exact ⟨dagWireToRef_lt left, dagWireToRef_lt right⟩

@[simp] theorem gateToDag_gateOfDag
    {n i : Nat} (gate : DagGate n i) :
    gateToDag (gateOfDag gate) (gateOfDag_valid gate) = gate := by
  cases gate <;> simp [gateOfDag, gateToDag]

@[simp] theorem gateOfDag_gateToDag
    {n i : Nat} (gate : FlatGate) (hgate : gate.Valid n i) :
    gateOfDag (gateToDag gate hgate) = gate := by
  cases gate <;> simp [gateToDag, gateOfDag]

/-- Flatten a frozen pnp3 DAG into the list-backed representation. -/
def ofDag {n : Nat} (circuit : DagCircuit n) : FlatCircuit n := by
  let data : FlatCircuitData :=
    { gateCount := circuit.gates
      gates := List.ofFn (fun i : Fin circuit.gates =>
        gateOfDag (circuit.gate i))
      output := dagWireToRef circuit.output }
  refine ⟨data, ?_⟩
  refine ⟨by simp [data], ?_, ?_⟩
  · intro i
    simpa [data] using
      (gateOfDag_valid
        (circuit.gate (Fin.cast (by simp [data]) i)))
  · simpa [data] using dagWireToRef_lt circuit.output

@[simp] theorem toDag_ofDag {n : Nat} (circuit : DagCircuit n) :
    (ofDag circuit).toDag = circuit := by
  cases circuit with
  | mk gates gate output =>
    simp [ofDag, toDag]

@[simp] theorem ofDag_toDag {n : Nat} (circuit : FlatCircuit n) :
    ofDag circuit.toDag = circuit := by
  rcases circuit with ⟨⟨gateCount, gates, output⟩, hvalid⟩
  apply Subtype.ext
  simp [ofDag, toDag]
  apply List.ext_get
  · simp [hvalid.1]
  · intro i hleft hright
    simp

/-- The list-backed model and the frozen pnp3 model are exactly equivalent,
not merely simulations of one another. -/
def equivDagCircuit (n : Nat) : FlatCircuit n ≃ DagCircuit n where
  toFun := toDag
  invFun := ofDag
  left_inv := ofDag_toDag
  right_inv := toDag_ofDag

end FlatCircuit
end StandardDAG
end StreamingMagnification
end Frontier
end Pnp4
