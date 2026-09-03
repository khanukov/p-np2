import Complexity.Uniform.V1.PpolyDAGExamples

/-! Explicit P1b-4 run-compiler and class-bridge proposition surface. -/

namespace Pnp3.Tests.UniformV1PpolyDAG

open Pnp3.ComplexityInterfaces.DagCircuit
open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.Circuit

#check clockedRunBundle
#check runCircuit
#check runCircuitExponent

theorem check_runCircuit_gates (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).gates =
      2 + polyClock c n * (stepBundle M n (polyClock c n)).gates :=
  runCircuit_gates M c n

theorem check_runCircuit_size (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).size =
      3 + polyClock c n * (stepBundle M n (polyClock c n)).gates :=
  runCircuit_size M c n

theorem check_runCircuit_size_le_raw (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).size ≤
      3 + polyClock c n *
        (19 * (n + polyClock c n + 1) + 16 * M.stateCount + 13) :=
  runCircuit_size_le_raw M c n

theorem check_runCircuit_accept_iff (M : UniformTM) (c n : Nat)
    (x : Pnp3.Complexity.Uniform.V1.Bitstring n) :
    eval (runCircuit M c n) x = true ↔
      AcceptsAt M (polyClock c n) (polyClock c n) x :=
  runCircuit_accept_iff M c n x

theorem check_runCircuit_eval_of_decidesAt (M : UniformTM) (c n : Nat)
    (x : Pnp3.Complexity.Uniform.V1.Bitstring n) (answer : Bool)
    (h : DecidesAt M (polyClock c n) (polyClock c n) x answer) :
    eval (runCircuit M c n) x = answer :=
  runCircuit_eval_of_decidesAt M c n x answer h

theorem check_runCircuit_size_le_poly (M : UniformTM) (c n : Nat) :
    (runCircuit M c n).size ≤
      n ^ runCircuitExponent M c + runCircuitExponent M c :=
  runCircuit_size_le_poly M c n

theorem check_uniformP_subset_PpolyDAG :
    ∀ L : Pnp3.Complexity.Uniform.V1.Language,
      UniformP L → Pnp3.ComplexityInterfaces.PpolyDAG L :=
  uniformP_subset_PpolyDAG

theorem check_lengthParity_runCircuit_eval (n : Nat)
    (x : Pnp3.Complexity.Uniform.V1.Bitstring n) :
    eval (runCircuit lengthParityMachine 1 n) x = lengthParityLanguage n x :=
  lengthParity_runCircuit_eval n x

theorem check_lengthParity_in_PpolyDAG :
    Pnp3.ComplexityInterfaces.PpolyDAG lengthParityLanguage :=
  lengthParity_in_PpolyDAG

theorem check_allReject_runCircuit_eval_false (n : Nat)
    (x : Pnp3.Complexity.Uniform.V1.Bitstring n) :
    eval (runCircuit allRejectMachine 0 n) x = false :=
  allReject_runCircuit_eval_false n x

end Pnp3.Tests.UniformV1PpolyDAG
