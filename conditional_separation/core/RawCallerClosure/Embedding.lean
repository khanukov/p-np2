import RawCallerClosure.Machine
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1
/-- Exact old guard controls, without any head/tape or runtime-data rewriting. -/
def old (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) : Fin (machine k).stateCount :=
  ⟨s.val,by
    have h:=s.isLt
    change s.val < 10+(67+(10+(BodyIngress.machine k).stateCount)) at h
    change s.val < 10+(67+(10+((BodyIngress.machine k).stateCount+7500+3337)))
    omega⟩
def oldConfig (k : Nat) {N B : Nat}
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) : Config (machine k).stateCount N B :=
  ⟨old k c.state,c.head,c.tape⟩
private def pin_machine : Nat → UniformTM := (show Nat → UniformTM from machine)
private def pin_callerState : (k : Nat) → Fin (PhysicalCallerClosure.callerMachine k).stateCount → Fin (machine k).stateCount :=
  (show (k : Nat) → Fin (PhysicalCallerClosure.callerMachine k).stateCount → Fin (machine k).stateCount from callerState)
private def pin_callerConfig : (k : Nat) → {N B : Nat} →
    Config (PhysicalCallerClosure.callerMachine k).stateCount N B → Config (machine k).stateCount N B :=
  (show (k : Nat) → {N B : Nat} → Config (PhysicalCallerClosure.callerMachine k).stateCount N B → Config (machine k).stateCount N B from callerConfig)
private def pin_allocation : Nat → Nat → Nat := (show Nat → Nat → Nat from allocation)
private def pin_deadline : Nat → Nat → Nat := (show Nat → Nat → Nat from deadline)
private def pin_old : (k : Nat) → Fin (CertificateGuardClosure.machine k).stateCount → Fin (machine k).stateCount :=
  (show (k : Nat) → Fin (CertificateGuardClosure.machine k).stateCount → Fin (machine k).stateCount from old)
private def pin_oldConfig : (k : Nat) → {N B : Nat} →
    Config (CertificateGuardClosure.machine k).stateCount N B → Config (machine k).stateCount N B :=
  (show (k : Nat) → {N B : Nat} → Config (CertificateGuardClosure.machine k).stateCount N B → Config (machine k).stateCount N B from oldConfig)
#print axioms machine
#print axioms pin_machine
#print axioms callerState
#print axioms pin_callerState
#print axioms callerConfig
#print axioms pin_callerConfig
#print axioms allocation
#print axioms pin_allocation
#print axioms deadline
#print axioms pin_deadline
#print axioms old
#print axioms pin_old
#print axioms oldConfig
#print axioms pin_oldConfig
end RawCallerClosure
