import IngressAllocation.Bounded
import IngressAllocation.RepairRun
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1
/-- Ten fixed parser controls restore the whole raw word before the old ingress.
No input length, parsed target, truth value or proof is a transition operand. -/
def machine (k : Nat) : UniformTM := FixedPairParser.machine.seq (BodyIngress.machine k)
/-- Injective old-family control inclusion, including literal global verdicts. -/
def old (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) : Fin (machine k).stateCount :=
  FixedPairParser.machine.seqRight (BodyIngress.machine k) s
/-- Full same-allocation component configuration inclusion. -/
def config (k : Nat) {N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B) :
    Config (machine k).stateCount N B := FixedPairParser.machine.seqEmbedRight (BodyIngress.machine k) c
/-- Fixed-k length-only allocation; the old allocation theorem is unchanged. -/
def allocation (k N : Nat) : Nat := IngressAllocation.allocation k N
/-- Proposed complete local raw-ingress bound, not a full verifier clock. -/
def deadline (k N : Nat) : Nat := 68719476736*(k+1)*(N+1)^6
end TotalIngressClosure
