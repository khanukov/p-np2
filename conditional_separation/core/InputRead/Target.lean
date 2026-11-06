import InputRead.Machine
import AcceptedBody.Target
namespace InputRead.Target
open Pnp3.Complexity.Uniform.V1

/-- Partial milestone frozen before proof: full configuration for a physically
discovered table cursor, including exact EOF (no scratch-as-source). The lifted
bit and the unique hole together retain the entire incoming source. -/
def CursorRead : Prop :=
  ∀ (N B p S z n : Nat) (c : Config machine.stateCount N B),
    ∀ (_hp : 2 ≤ p) (_hps : p ≤ S) (_hfit : S+z+n+3 < tapeLength N B),
    c.state=q 2 → c.head.val=S+z+n+3 →
    c.tape ⟨p-2,by omega⟩=none →
    c.tape ⟨p-1,by omega⟩=some true →
    (∀ i, p ≤ i.val → i.val < S → ∃ b, c.tape i=some b) →
    c.tape ⟨S,by omega⟩=none →
    (∀ i, S < i.val → i.val < S+z+2 → c.tape i=some false) →
    c.tape ⟨S+z+2,by omega⟩=none →
    (∀ i, S+z+2 < i.val → i.val < S+z+n+3 → ∃ b, c.tape i=some b) →
    c.tape ⟨S+z+n+3,by omega⟩=none →
    ∃ mode : Fin 3,
      (mode.val=2 ↔ p=S) ∧
      (p<S → c.tape ⟨p,by omega⟩=some (result mode)) ∧
      let e := machine.run (readClock n z (S-p)) c
      e.state=ready mode ∧ e.head=c.head ∧
      (∀ i, e.tape i=if i.val=p then none else c.tape i) ∧
      (∀ i, (if i.val=p ∧ p<S then some (result mode) else e.tape i)=c.tape i)

/-- The exact serialized-input obligation is deliberately retained as RED.
No cursor-only theorem is a proof of this endpoint. -/
def PartA (partAMachine : Nat → UniformTM) (partAExponent : Nat → Nat) : Prop :=
  ∀ k, VerifiesRelation (partAMachine k) (partAExponent k)
    (Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation k)
end InputRead.Target
