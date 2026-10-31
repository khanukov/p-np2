import PhysicalCallerClosure.Stability
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
/-- Full original installer premises followed by the actual same-table BODY, all beta. -/
def InstalledBody (k : Nat) : Prop :=
  ∀ (R S z n p g W Q : Nat) (source : Fin S  →  Bool) (beta : Fin n  →  Bool) (T : Nat  →  Option Bool),
    1 ≤ R  →  S ≤ R  →  n ≤ R  →  p < S  →
    let r:=S-p; let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
    let B:=FixedRawLengthFence.allocation R; let D:=SerializedBody.delimiter F r n
    g ≤ r  →  W ≤ r  →  bitLength n ≤ r  →  0 < Q  →  H+Q < F  →
    (∀ i, p ≤ i  →  ∀ hi : i < S, T i=some (source ⟨i,hi⟩))  →  T S=none  →
    (∀ i,S < i  →  i < L  →  T i=some false)  →  T L=none  →  T H=none  →
    (∀ j:Fin n,T (H-1-j.val)=some (beta j))  →
    (∀ i,H < i  →  i ≤ H+Q  →  T i=some true)  →
    (∀ i,H+Q < i  →  i < F  →  T i=none)  →  T F=some false  →
    (∀ j,j ≤ 6  →  T (D j)=none)  →
    (∀ i,D 0 < i  →  i < D 1  →  T i=some (decide (i-D 0 ≤ g)))  →
    (∀ i,D 1 < i  →  i < D 2  →  T i=some false)  →
    (∀ i,D 2 < i  →  i < D 3  →  T i=some (decide (i-D 2 ≤ bitLength W)))  →
    (∀ i,D 3 < i  →  i < D 5  →  i ≠ D 4  →  T i=some false)  →
    (∀ i,D 5 < i  →  i < D 6  →  T i=some (decide (i-D 5 ≤ W)))  →
    (∀ i,D 6 < i  →  i ≤ D 12  →  T i=none)  →
    ∀ (_fit:D 12 < tapeLength R B) (hd:D 0 < tapeLength R B) (hh:H < tapeLength R B),
    let c:Config (BodyIngress.machine k).stateCount R B:=⟨BodyIngress.old k (CarryWindow.ready k),⟨D 0,hd⟩,fun i=>T i.val⟩
    let M:=p+bitLength W+W
    let bits:=SerializedBody.window source M W
    let semantics:=do
      let (circuit,tail) ← decodeCircuitFull n (bitLength n) bits
      if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit beta),tail) else none
    ∃ e t,e ≤ 1073741824*(R+1)^3 ∧ t ≤ 1073741824*(R+1)^6 ∧
      e+t ≤ 2147483648*(R+1)^6 ∧
      (∀ u,u ≤ e+t → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).accept) ∧
      (∀ u,u < e+t → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).reject ∧
        ((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.done false) ∧
        ((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.done true)) ∧
      match semantics with
      | none=>(BodyIngress.machine k).run (e+t) c=
          ⟨(BodyIngress.machine k).reject,⟨H,hh⟩,
            fun i=>SerializedBody.image T F r n g W (S-min M S) 0 0 0 0 i.val⟩
      | some ((size,b),tail)=>∃ consumed,consumed ≤ W ∧ tail=bits.drop consumed ∧
          (BodyIngress.machine k).run (e+t) c=
            ⟨BodyIngress.body k (SerializedBody.done b),⟨H,hh⟩,
              fun i=>SerializedBody.image T F r n g W (S-min M S) size consumed (W-consumed) 0 i.val⟩
end PhysicalCallerClosure
