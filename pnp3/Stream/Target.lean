import Stream.Machine
namespace Stream.Target
open Pnp3.Complexity.Uniform.V1
/-- Specification arithmetic only; neither rows nor machine reads these functions. -/
def cursor (A S r : Nat) : Nat := min (A+r) S

def mode (U : Nat → Option Bool) (p S : Nat) : Fin 3 :=
  if p=S then ⟨2,by decide⟩ else if U p=some true then ⟨1,by decide⟩ else ⟨0,by decide⟩

def image (U : Nat → Option Bool) (S z n A r marks : Nat) (lift : Bool) : Nat → Option Bool :=
  fun i =>
    let L := S+z+2
    let H := L+n+1
    if L < i ∧ i < H then some ((Body.iterBits (List.replicate n false) r)[H-1-i]!)
    else if H < i ∧ i ≤ H+marks then some true
    else if lift ∧ i=cursor A S r ∧ i < S then none else U i

/-- Frozen intended same-table kernel. Every allowed row is paid once; final
source restoration and the actual next-field head are part of the full Config. -/
def Kernel : Prop :=
  ∀ (N B S z n A F : Nat) (U : Nat → Option Bool),
    2 ≤ A → A ≤ S → S+z+n+3 < F → F < tapeLength N B →
    (∀ i, A ≤ i → i < S → ∃ b, U i=some b) → U S=none →
    (∀ i, S < i → i < S+z+2 → U i=some false) → U (S+z+2)=none →
    U (S+z+n+3)=none →
    (∀ i, S+z+n+3 < i → i < F → U i=none) → U F=some false →
    let H := S+z+n+3
    let cap := F-H-1
    let count := min (2^n) cap
    ∀ hH : H < tapeLength N B,
    let c : Config machine.stateCount N B :=
      ⟨unpaid (mode U A S),⟨H,hH⟩,fun i => image U S z n A 0 0 true i.val⟩
    ∃ T, T ≤ 64*(F+1)^2 ∧
      (∀ r, r<count → ∃ t, t ≤ T ∧
        machine.run t c = ⟨paid (mode U (cursor A S r) S),⟨H,hH⟩,
          fun i => image U S z n A r (r+1) true i.val⟩) ∧
      (if 2^n ≤ cap then
        ∃ hp : cursor A S (2^n) < tapeLength N B,
          machine.run T c =
            ⟨q (if cursor A S (2^n)=S then 57 else 58),⟨cursor A S (2^n),hp⟩,
              fun i => image U S z n A (2^n) (2^n) false i.val⟩
       else
        ∃ hF : F < tapeLength N B,
          machine.run T c = ⟨machine.reject,⟨F,hF⟩,
            fun i => image U S z n A cap cap true i.val⟩)

/-- Endpoint stays RED; work exits are not verifier acceptance. -/
def PartA (partAMachine : Nat → UniformTM) (partAExponent : Nat → Nat) : Prop :=
  ∀ k, VerifiesRelation (partAMachine k) (partAExponent k)
    (Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation k)
end Stream.Target
