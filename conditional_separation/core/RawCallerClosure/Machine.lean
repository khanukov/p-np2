import RawCallerClosure.Joint
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1
/-- Exact parser/guard/parser prefix of the sealed guard, with only the final
BodyIngress component replaced by the sealed physical caller. -/
def machine (k : Nat) : UniformTM :=
  FixedPairParser.machine.seq (CertificateGuardClosure.guard.seq
    (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k)))
/-- The closed caller component, preserving the entire head and finite tape. -/
def callerState (k : Nat) (s : Fin (PhysicalCallerClosure.callerMachine k).stateCount) :
    Fin (machine k).stateCount :=
  FixedPairParser.machine.seqRight _ (CertificateGuardClosure.guard.seqRight _
    (FixedPairParser.machine.seqRight _ s))
def callerConfig (k : Nat) {N B : Nat}
    (c : Config (PhysicalCallerClosure.callerMachine k).stateCount N B) : Config (machine k).stateCount N B :=
  ⟨callerState k c.state,c.head,c.tape⟩
def allocation (k N : Nat) : Nat := CertificateGuardClosure.allocation k N
/-- Raw prefix plus every physical row, not a full verifier clock. -/
def deadline (k N : Nat) : Nat := 4398046511104*(k+1)*(N+1)^8
end RawCallerClosure
