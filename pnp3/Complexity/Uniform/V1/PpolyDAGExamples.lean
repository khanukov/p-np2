import Complexity.Uniform.V1.PpolyDAG
import Complexity.Uniform.V1.Examples

/-! # Uniform V1 run-circuit capstones -/

namespace Pnp3.Complexity.Uniform.V1

open Pnp3.ComplexityInterfaces.DagCircuit
open Circuit

/-- The exponent-one compiled scanner computes length parity at every length. -/
theorem lengthParity_runCircuit_eval (n : Nat) (x : Bitstring n) :
    eval (runCircuit lengthParityMachine 1 n) x = lengthParityLanguage n x := by
  apply runCircuit_eval_of_decidesAt
  simpa [polyClock_exponent_one] using
    (lengthParity_decidesAt (budget := n + 1) x)

/-- Length parity is a concrete non-uniform DAG member via the headline
versioned bridge. -/
theorem lengthParity_in_PpolyDAG :
    Pnp3.ComplexityInterfaces.PpolyDAG lengthParityLanguage :=
  uniformP_subset_PpolyDAG lengthParityLanguage uniformP_lengthParity

/-- False-output regression: the circuit returns false from a literal reject
verdict, not from timeout or mere nonacceptance. -/
theorem allReject_runCircuit_eval_false (n : Nat) (x : Bitstring n) :
    eval (runCircuit allRejectMachine 0 n) x = false := by
  apply runCircuit_eval_of_decidesAt
  simpa [polyClock_exponent_zero, DecidesAt] using
    (allReject_rejectsAt (budget := 1) (steps := 1) x)

end Pnp3.Complexity.Uniform.V1
