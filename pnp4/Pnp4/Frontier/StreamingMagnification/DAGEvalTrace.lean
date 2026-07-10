import Pnp4.Frontier.StreamingMagnification.StandardDAGMCSP
import Mathlib.Tactic

/-!
# Local evaluation traces for shared Boolean DAGs

This module gives a local checker for the value of every internal gate of a
`DagCircuit`.  A trace is a full Boolean vector indexed by the circuit gates.
At gate `i`, the checker reads only the gate operation, the external input,
and trace entries at the strictly earlier gate indices permitted by the
dependent `DagGate n i` syntax.

The canonical trace is obtained from the existing recursive semantics.  We
prove that it satisfies every local equation, that every locally consistent
trace is equal to it, and that the output read from any such trace is exactly
`DagCircuit.eval`.  Thin wrappers expose the same facts for the standard flat
DAG carrier used by the streaming-MCSP development.

No complexity-class or running-time claim is made here.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace DAGEvalTrace

open Pnp3.ComplexityInterfaces
open StandardDAG

/-! ## Local checker for the frozen dependent DAG representation -/

/-- One Boolean value for every internal gate of `circuit`. -/
abbrev GateValues {n : Nat} (circuit : DagCircuit n) :=
  Fin circuit.gates -> Bool

/-- Embed an index below gate `i` into the full gate-index space. -/
def earlierIndex {n : Nat} {circuit : DagCircuit n}
    (i : Fin circuit.gates) (j : Fin i.val) : Fin circuit.gates :=
  ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- Read an input-or-earlier-gate wire using a proposed full trace. -/
def wireValueAt {n : Nat} (circuit : DagCircuit n) (input : Bitstring n)
    (values : GateValues circuit) (i : Fin circuit.gates) :
    DagWire n i.val -> Bool
  | .input inputIndex => input inputIndex
  | .gate gateIndex => values (earlierIndex i gateIndex)

/-- Locally compute gate `i` from the values assigned to its incoming wires. -/
def localGateValue {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) (values : GateValues circuit)
    (i : Fin circuit.gates) : Bool :=
  match circuit.gate i with
  | .const value => value
  | .not source => !(wireValueAt circuit input values i source)
  | .and left right =>
      wireValueAt circuit input values i left &&
        wireValueAt circuit input values i right
  | .or left right =>
      wireValueAt circuit input values i left ||
        wireValueAt circuit input values i right

/-- The trace entry at `i` satisfies exactly its one local gate equation. -/
def GateConsistentAt {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) (values : GateValues circuit)
    (i : Fin circuit.gates) : Prop :=
  values i = localGateValue circuit input values i

/-- Every gate entry satisfies its local equation. -/
def IsTrace {n : Nat} (circuit : DagCircuit n) (input : Bitstring n)
    (values : GateValues circuit) : Prop :=
  forall i, GateConsistentAt circuit input values i

instance instDecidableGateConsistentAt {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) (values : GateValues circuit)
    (i : Fin circuit.gates) :
    Decidable (GateConsistentAt circuit input values i) := by
  unfold GateConsistentAt
  infer_instance

instance instDecidableIsTrace {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) (values : GateValues circuit) :
    Decidable (IsTrace circuit input values) := by
  unfold IsTrace
  exact Fintype.decidableForallFintype

/-- Executable Boolean façade for the local trace predicate. -/
def check {n : Nat} (circuit : DagCircuit n) (input : Bitstring n)
    (values : GateValues circuit) : Bool :=
  decide (IsTrace circuit input values)

@[simp] theorem check_eq_true_iff {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) (values : GateValues circuit) :
    check circuit input values = true <-> IsTrace circuit input values := by
  simp [check]

/-- Read the designated circuit output from the external input and trace. -/
def outputValue {n : Nat} (circuit : DagCircuit n) (input : Bitstring n)
    (values : GateValues circuit) : Bool :=
  match circuit.output with
  | .input inputIndex => input inputIndex
  | .gate gateIndex => values gateIndex

/-! ## Canonical trace and local consistency -/

/-- The value of every gate according to the existing recursive evaluator. -/
def canonicalValues {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) : GateValues circuit :=
  fun i =>
    DagCircuit.eval.evalGateAt
      (C := circuit) (x := input) i.val i.isLt

theorem wireValueAt_canonical {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) (i : Fin circuit.gates)
    (wire : DagWire n i.val) :
    wireValueAt circuit input (canonicalValues circuit input) i wire =
      match wire with
      | .input inputIndex => input inputIndex
      | .gate gateIndex =>
          DagCircuit.eval.evalGateAt
            (C := circuit) (x := input) gateIndex.val
            (Nat.lt_trans gateIndex.isLt i.isLt) := by
  cases wire <;> rfl

/-- The recursively evaluated values satisfy every local gate equation. -/
theorem canonicalValues_gateConsistentAt {n : Nat}
    (circuit : DagCircuit n) (input : Bitstring n)
    (i : Fin circuit.gates) :
    GateConsistentAt circuit input (canonicalValues circuit input) i := by
  unfold GateConsistentAt canonicalValues localGateValue
  cases hgate : circuit.gate i with
  | const value =>
      rw [DagCircuit.eval.evalGateAt, hgate]
  | not source =>
      rw [DagCircuit.eval.evalGateAt, hgate]
      cases source <;> rfl
  | and left right =>
      rw [DagCircuit.eval.evalGateAt, hgate]
      cases left <;> cases right <;> rfl
  | or left right =>
      rw [DagCircuit.eval.evalGateAt, hgate]
      cases left <;> cases right <;> rfl

/-- The canonical gate-value vector is a locally consistent trace. -/
theorem canonicalValues_isTrace {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) :
    IsTrace circuit input (canonicalValues circuit input) := by
  intro i
  exact canonicalValues_gateConsistentAt circuit input i

/-- A locally consistent trace always exists. -/
theorem exists_isTrace {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) :
    Exists fun values : GateValues circuit => IsTrace circuit input values :=
  ⟨canonicalValues circuit input, canonicalValues_isTrace circuit input⟩

/-! ## Uniqueness from strictly earlier dependencies -/

theorem wireValueAt_congr_of_earlier {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) {left right : GateValues circuit}
    (i : Fin circuit.gates)
    (hearlier : forall j : Fin i.val,
      left (earlierIndex i j) = right (earlierIndex i j))
    (wire : DagWire n i.val) :
    wireValueAt circuit input left i wire =
      wireValueAt circuit input right i wire := by
  cases wire with
  | input inputIndex => rfl
  | gate gateIndex => exact hearlier gateIndex

theorem localGateValue_congr_of_earlier {n : Nat}
    (circuit : DagCircuit n) (input : Bitstring n)
    {left right : GateValues circuit} (i : Fin circuit.gates)
    (hearlier : forall j : Fin i.val,
      left (earlierIndex i j) = right (earlierIndex i j)) :
    localGateValue circuit input left i =
      localGateValue circuit input right i := by
  cases hgate : circuit.gate i with
  | const value => simp only [localGateValue, hgate]
  | not source =>
      simp only [localGateValue, hgate]
      rw [wireValueAt_congr_of_earlier circuit input i hearlier source]
  | and leftWire rightWire =>
      simp only [localGateValue, hgate]
      rw [wireValueAt_congr_of_earlier circuit input i hearlier leftWire,
        wireValueAt_congr_of_earlier circuit input i hearlier rightWire]
  | or leftWire rightWire =>
      simp only [localGateValue, hgate]
      rw [wireValueAt_congr_of_earlier circuit input i hearlier leftWire,
        wireValueAt_congr_of_earlier circuit input i hearlier rightWire]

/-- Two vectors satisfying all local equations are identical. -/
theorem isTrace_unique {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) {left right : GateValues circuit}
    (hleft : IsTrace circuit input left)
    (hright : IsTrace circuit input right) :
    left = right := by
  funext i
  have hpoint :
      forall k (hk : k < circuit.gates),
        left ⟨k, hk⟩ = right ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let i : Fin circuit.gates := ⟨k, hk⟩
        rw [hleft i, hright i]
        apply localGateValue_congr_of_earlier circuit input i
        intro j
        simpa [i, earlierIndex] using
          ih j.val j.isLt (Nat.lt_trans j.isLt hk)
  exact hpoint i.val i.isLt

/-- Every locally consistent vector is the canonical evaluator trace. -/
theorem isTrace_eq_canonicalValues {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) {values : GateValues circuit}
    (htrace : IsTrace circuit input values) :
    values = canonicalValues circuit input :=
  isTrace_unique circuit input htrace
    (canonicalValues_isTrace circuit input)

/-! ## Exact output semantics -/

/-- Reading the canonical trace is definitionally the recursive evaluator. -/
theorem outputValue_canonicalValues {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) :
    outputValue circuit input (canonicalValues circuit input) =
      DagCircuit.eval circuit input := by
  cases circuit.output <;> rfl

/-- Soundness: every locally checked trace has the exact semantic output. -/
theorem outputValue_eq_eval_of_isTrace {n : Nat} (circuit : DagCircuit n)
    (input : Bitstring n) {values : GateValues circuit}
    (htrace : IsTrace circuit input values) :
    outputValue circuit input values = DagCircuit.eval circuit input := by
  rw [isTrace_eq_canonicalValues circuit input htrace]
  exact outputValue_canonicalValues circuit input

/-- Exact relational characterization of one proposed output bit. -/
theorem exists_isTrace_and_outputValue_eq_iff {n : Nat}
    (circuit : DagCircuit n) (input : Bitstring n) (output : Bool) :
    (Exists fun values : GateValues circuit =>
      IsTrace circuit input values /\
        outputValue circuit input values = output) <->
      DagCircuit.eval circuit input = output := by
  constructor
  · rintro ⟨values, htrace, houtput⟩
    rw [outputValue_eq_eval_of_isTrace circuit input htrace] at houtput
    exact houtput
  · intro houtput
    refine ⟨canonicalValues circuit input,
      canonicalValues_isTrace circuit input, ?_⟩
    rw [outputValue_canonicalValues]
    exact houtput

/-! ## Standard flat-DAG wrappers -/

/-- Gate values for the canonical dependent image of a standard flat DAG. -/
abbrev FlatGateValues {n : Nat} (circuit : FlatCircuit n) :=
  GateValues circuit.toDag

/-- Local trace predicate for the standard flat-DAG carrier. -/
abbrev FlatIsTrace {n : Nat} (circuit : FlatCircuit n)
    (input : Bitstring n) (values : FlatGateValues circuit) : Prop :=
  IsTrace circuit.toDag input values

/-- Output reconstructed from a trace of the standard flat DAG. -/
abbrev flatOutputValue {n : Nat} (circuit : FlatCircuit n)
    (input : Bitstring n) (values : FlatGateValues circuit) : Bool :=
  outputValue circuit.toDag input values

theorem flat_exists_isTrace {n : Nat} (circuit : FlatCircuit n)
    (input : Bitstring n) :
    Exists fun values : FlatGateValues circuit =>
      FlatIsTrace circuit input values :=
  exists_isTrace circuit.toDag input

theorem flat_isTrace_unique {n : Nat} (circuit : FlatCircuit n)
    (input : Bitstring n) {left right : FlatGateValues circuit}
    (hleft : FlatIsTrace circuit input left)
    (hright : FlatIsTrace circuit input right) :
    left = right :=
  isTrace_unique circuit.toDag input hleft hright

theorem flatOutputValue_eq_eval_of_isTrace {n : Nat}
    (circuit : FlatCircuit n) (input : Bitstring n)
    {values : FlatGateValues circuit}
    (htrace : FlatIsTrace circuit input values) :
    flatOutputValue circuit input values = circuit.eval input := by
  exact outputValue_eq_eval_of_isTrace circuit.toDag input htrace

theorem flat_exists_isTrace_and_outputValue_eq_iff {n : Nat}
    (circuit : FlatCircuit n) (input : Bitstring n) (output : Bool) :
    (Exists fun values : FlatGateValues circuit =>
      FlatIsTrace circuit input values /\
        flatOutputValue circuit input values = output) <->
      circuit.eval input = output := by
  exact exists_isTrace_and_outputValue_eq_iff circuit.toDag input output

end DAGEvalTrace
end StreamingMagnification
end Frontier
end Pnp4
