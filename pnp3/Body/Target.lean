import Body.Machine
import Pnp4.Frontier.ContractExpansion.TreeCircuitContentWitnessRelation
namespace Body.Target
open Pnp3.Complexity.Uniform.V1
/-- Frozen complete endpoint. This slice does not supply its machine family. -/
def PartA (M : Nat → UniformTM) (c : Nat → Nat) : Prop :=
  ∀ k, VerifiesRelation (M k) (c k)
    (Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation k)
/-- Tape ABI: actual unary span, blank boundaries and arbitrary exterior tape. -/
def Span {N B : Nat} (T : Fin (tapeLength N B) → Option Bool)
    (left : Nat) (digits : List Bool) : Prop :=
  ∀ i : Fin (tapeLength N B),
    (i.val = left → T i = none) ∧
    (i.val = left + digits.length + 1 → T i = none) ∧
    (∀ j, j < digits.length → i.val = left + digits.length - j →
      T i = some (digits[j]!))
/-- Generic round target includes the entire tape and head, not an observer. -/
def Round : Prop :=
  ∀ (N B left : Nat) (bits : List Bool)
    (c : Config machine.stateCount N B),
    left + bits.length + 1 < tapeLength N B →
    c.state = q 2 → c.head.val = left + bits.length + 1 →
    Span c.tape left bits →
    let e := machine.run (roundClock bits) c
    e.state = (if (inc bits).2 then machine.accept else q 2) ∧
    e.head.val = (if (inc bits).2 then left + 1 else left + bits.length + 1) ∧
    Span e.tape left (inc bits).1 ∧
    ∀ i, i.val ≤ left ∨ left + bits.length < i.val → e.tape i = c.tape i
end Body.Target
