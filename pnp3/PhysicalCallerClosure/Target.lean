import PhysicalCallerClosure.Joint
namespace PhysicalCallerClosure
open SerializedBody Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
def AmbientBody : Prop :=
  ∀ (B R S z n r g W M Q : Nat) (source : Fin S → Bool) (beta : Fin n → Bool)
    (T : Nat → Option Bool),
    r ≤ S → S ≤ R → g ≤ r → W ≤ r → bitLength n ≤ r → S-min M S ≤ r →
    let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
    0 < Q → H+Q < F →
    (∀ i, M ≤ i → ∀ hi : i < S, T i=some (source ⟨i,hi⟩)) →
    T S=none →
    (∀ i, S < i → i < L → T i=some false) → T L=none →
    (∀ j : Fin n, T (H-1-j.val)=some (beta j)) → T H=none →
    (∀ i, H < i → i ≤ H+Q → T i=some true) →
    (∀ i, H+Q < i → i < F → T i=none) → T F=some false →
    ∀ _fit : delimiter F r n 12 < tapeLength R B,
    ∀ hH : H < tapeLength R B,
    let bits:=window source M W
    let initial : Config machine.stateCount R B :=
      ⟨entry (sourceMode source M),⟨H,hH⟩,fun i => prepared T S M F r n g W i.val⟩
    let semantics:=do
      let (c,tail) ← decodeCircuitFull n (bitLength n) bits
      if c.size ≤ g then some ((c.size,Pnp3.Models.Circuit.eval c beta),tail) else none
    ∃ t, t ≤ 1073741824*(R+1)^6 ∧
      (∀ u, u ≤ t → ((machine.run u initial).state≠machine.accept)) ∧
      (∀ u, u < t → (machine.run u initial).state≠machine.reject ∧
        (machine.run u initial).state≠done false ∧ (machine.run u initial).state≠done true) ∧
      match semantics with
      | none => machine.run t initial=
          ⟨machine.reject,⟨H,hH⟩,fun i => image T F r n g W (S-min M S) 0 0 0 0 i.val⟩
      | some ((size,b),tail) => ∃ consumed,
          consumed ≤ W ∧ tail=bits.drop consumed ∧
          machine.run t initial=
            ⟨done b,⟨H,hH⟩,fun i => image T F r n g W (S-min M S) size consumed (W-consumed) 0 i.val⟩
#check (AmbientBody : Prop)
#print axioms AmbientBody
end PhysicalCallerClosure
