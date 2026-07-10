import Pnp4.Frontier.StreamingMagnification.DAGEvalTrace
import Pnp4.Frontier.StreamingMagnification.DAGCodec

/-!
# Fixed-length padded evaluation traces for bounded Boolean DAGs

`DAGEvalTrace.FlatGateValues circuit` has one bit for every actual gate, so
its type depends on `circuit.gateCount`.  This module replaces that dependent
external witness by exactly `threshold` bits for a
`DAGCodec.BoundedCircuit n threshold`.

The active prefix is interpreted as the ordinary local DAG trace.  Every bit
after the actual gate count is required to be `false`, giving a canonical
extension rather than quotienting by an arbitrary unused suffix.  Restriction
and extension are inverse on canonical padded vectors, and the resulting
fixed-length trace relation has exactly the same output semantics as the
existing evaluator.

No complexity-class or running-time claim is made here.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace PaddedDAGEvalTrace

open Pnp3.ComplexityInterfaces
open StandardDAG
open DAGEvalTrace

/-- A circuit trace body with exactly `threshold` externally visible bits. -/
abbrev PaddedGateValues (threshold : Nat) := DAGCodec.BitString threshold

/-- Restrict a fixed-length trace body to the actual gate prefix. -/
def restrict {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (values : PaddedGateValues threshold) : FlatGateValues circuit.val :=
  fun i => values ⟨i.val, lt_of_lt_of_le i.isLt circuit.property⟩

/-- Extend an actual gate trace to exactly `threshold` bits, filling the
unused suffix with `false`. -/
def extend {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (values : FlatGateValues circuit.val) : PaddedGateValues threshold :=
  fun i => if hi : i.val < circuit.val.gateCount then values ⟨i.val, hi⟩
    else false

/-- Canonical padding requires every position after the actual gate prefix to
be zero. -/
def PaddingZero {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (values : PaddedGateValues threshold) : Prop :=
  ∀ i : Fin threshold, circuit.val.gateCount ≤ i.val → values i = false

instance instDecidablePaddingZero {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (values : PaddedGateValues threshold) :
    Decidable (PaddingZero circuit values) := by
  unfold PaddingZero
  exact Fintype.decidableForallFintype

/-- Restricting a canonical extension recovers the original dependent trace. -/
@[simp] theorem restrict_extend {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (values : FlatGateValues circuit.val) :
    restrict circuit (extend circuit values) = values := by
  funext i
  simp [restrict, extend]

/-- The canonical extension has a zero suffix. -/
theorem paddingZero_extend {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (values : FlatGateValues circuit.val) :
    PaddingZero circuit (extend circuit values) := by
  intro i hi
  simp [extend, Nat.not_lt.mpr hi]

/-- Extension after restriction recovers every canonically padded body. -/
theorem extend_restrict {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (values : PaddedGateValues threshold)
    (hpadding : PaddingZero circuit values) :
    extend circuit (restrict circuit values) = values := by
  funext i
  by_cases hi : i.val < circuit.val.gateCount
  · simp [extend, restrict, hi]
  · rw [extend, dif_neg hi]
    exact (hpadding i (Nat.le_of_not_gt hi)).symm

/-- Canonical extension is injective. -/
theorem extend_injective {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold) :
    Function.Injective (extend circuit) := by
  intro left right heq
  have := congrArg (restrict circuit) heq
  simpa using this

/-! ## Fixed-length local trace relation -/

/-- A fixed-length trace consists of a valid active gate prefix and canonical
zero padding. -/
def IsPaddedTrace {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (values : PaddedGateValues threshold) : Prop :=
  FlatIsTrace circuit.val input (restrict circuit values) ∧
    PaddingZero circuit values

instance instDecidableIsPaddedTrace {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (values : PaddedGateValues threshold) :
    Decidable (IsPaddedTrace circuit input values) := by
  unfold IsPaddedTrace
  infer_instance

/-- Executable Boolean facade for the fixed-length trace relation. -/
def check {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (values : PaddedGateValues threshold) : Bool :=
  decide (IsPaddedTrace circuit input values)

@[simp] theorem check_eq_true_iff {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (values : PaddedGateValues threshold) :
    check circuit input values = true ↔
      IsPaddedTrace circuit input values := by
  simp [check]

/-- A canonical extension is a padded trace exactly when its source vector is
an ordinary dependent trace. -/
@[simp] theorem isPaddedTrace_extend_iff {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (values : FlatGateValues circuit.val) :
    IsPaddedTrace circuit input (extend circuit values) ↔
      FlatIsTrace circuit.val input values := by
  simp [IsPaddedTrace, paddingZero_extend]

/-- Forgetting the fixed zero suffix of a padded trace yields the original
local trace relation. -/
theorem restrict_isTrace_of_isPaddedTrace {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) {values : PaddedGateValues threshold}
    (htrace : IsPaddedTrace circuit input values) :
    FlatIsTrace circuit.val input (restrict circuit values) :=
  htrace.1

/-- Read the designated circuit output through the active trace prefix. -/
def outputValue {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (values : PaddedGateValues threshold) : Bool :=
  flatOutputValue circuit.val input (restrict circuit values)

@[simp] theorem outputValue_extend {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (values : FlatGateValues circuit.val) :
    outputValue circuit input (extend circuit values) =
      flatOutputValue circuit.val input values := by
  simp [outputValue]

/-! ## Existence, uniqueness, and exact output semantics -/

/-- The existing canonical evaluator trace, padded to the threshold. -/
def canonicalValues {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) : PaddedGateValues threshold :=
  extend circuit (DAGEvalTrace.canonicalValues circuit.val.toDag input)

theorem canonicalValues_isPaddedTrace {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) :
    IsPaddedTrace circuit input (canonicalValues circuit input) := by
  rw [canonicalValues, isPaddedTrace_extend_iff]
  exact DAGEvalTrace.canonicalValues_isTrace circuit.val.toDag input

/-- A canonical fixed-length trace exists at every input. -/
theorem exists_isPaddedTrace {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) :
    ∃ values : PaddedGateValues threshold,
      IsPaddedTrace circuit input values :=
  ⟨canonicalValues circuit input,
    canonicalValues_isPaddedTrace circuit input⟩

/-- Canonical zero padding lifts uniqueness of local DAG traces to the entire
fixed-length body. -/
theorem isPaddedTrace_unique {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) {left right : PaddedGateValues threshold}
    (hleft : IsPaddedTrace circuit input left)
    (hright : IsPaddedTrace circuit input right) :
    left = right := by
  have hprefix : restrict circuit left = restrict circuit right :=
    flat_isTrace_unique circuit.val input hleft.1 hright.1
  calc
    left = extend circuit (restrict circuit left) :=
      (extend_restrict circuit left hleft.2).symm
    _ = extend circuit (restrict circuit right) := congrArg _ hprefix
    _ = right := extend_restrict circuit right hright.2

/-- Soundness: every checked fixed-length trace reconstructs exactly the
standard circuit evaluator output. -/
theorem outputValue_eq_eval_of_isPaddedTrace {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) {values : PaddedGateValues threshold}
    (htrace : IsPaddedTrace circuit input values) :
    outputValue circuit input values = circuit.val.eval input := by
  exact flatOutputValue_eq_eval_of_isTrace circuit.val input htrace.1

/-- Fixed-length and dependent trace witnesses have exactly the same
output-labelled existence relation. -/
theorem exists_isPaddedTrace_and_outputValue_eq_iff_flat
    {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (output : Bool) :
    (∃ values : PaddedGateValues threshold,
      IsPaddedTrace circuit input values ∧
        outputValue circuit input values = output) ↔
      ∃ values : FlatGateValues circuit.val,
        FlatIsTrace circuit.val input values ∧
          flatOutputValue circuit.val input values = output := by
  constructor
  · rintro ⟨values, htrace, houtput⟩
    exact ⟨restrict circuit values, htrace.1, houtput⟩
  · rintro ⟨values, htrace, houtput⟩
    refine ⟨extend circuit values, ?_, ?_⟩
    · exact (isPaddedTrace_extend_iff circuit input values).2 htrace
    · simpa using houtput

/-- Exact semantic characterization of one output-labelled fixed-length
trace witness. -/
theorem exists_isPaddedTrace_and_outputValue_eq_iff
    {n threshold : Nat}
    (circuit : DAGCodec.BoundedCircuit n threshold)
    (input : Bitstring n) (output : Bool) :
    (∃ values : PaddedGateValues threshold,
      IsPaddedTrace circuit input values ∧
        outputValue circuit input values = output) ↔
      circuit.val.eval input = output := by
  rw [exists_isPaddedTrace_and_outputValue_eq_iff_flat]
  exact flat_exists_isTrace_and_outputValue_eq_iff
    circuit.val input output

end PaddedDAGEvalTrace
end StreamingMagnification
end Frontier
end Pnp4
