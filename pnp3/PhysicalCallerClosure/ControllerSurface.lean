import PhysicalCallerClosure.Controller
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
private def pin_callerMachine : Nat → UniformTM := (callerMachine : Nat → UniformTM)
private def pin_oldState : ∀ k : Nat,Fin (BodyIngress.machine k).stateCount →
    Fin ((BodyIngress.machine k).stateCount+7500+3337) :=
  (oldState : ∀ k : Nat,Fin (BodyIngress.machine k).stateCount → Fin ((BodyIngress.machine k).stateCount+7500+3337))
private def pin_evalState : ∀ k : Nat,Fin 7500 → Fin ((BodyIngress.machine k).stateCount+7500+3337) :=
  (evalState : ∀ k : Nat,Fin 7500 → Fin ((BodyIngress.machine k).stateCount+7500+3337))
private def pin_rowsDone : ∀ k : Nat,Fin ((BodyIngress.machine k).stateCount+7500+3337) :=
  (rowsDone : ∀ k : Nat,Fin ((BodyIngress.machine k).stateCount+7500+3337))
#print axioms callerMachine
#print axioms pin_callerMachine
#print axioms oldState
#print axioms pin_oldState
#print axioms evalState
#print axioms pin_evalState
#print axioms rowsDone
#print axioms pin_rowsDone
end PhysicalCallerClosure
