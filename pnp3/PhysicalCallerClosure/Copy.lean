import PhysicalCallerClosure.Prefix
import PhysicalCallerClosure.AmbientSurface
namespace PhysicalCallerClosure
open SerializedBody Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
private def shift (a b c : Nat) (q : Fin b) : Fin (a+b+c) := ⟨a+q.val,by have h:=q.isLt;omega⟩
private theorem shift_injective (a b c : Nat) : Function.Injective (shift a b c) := by
  intro q r bad
  apply Fin.ext
  have values:=congrArg (fun s : Fin (a+b+c)=>s.val) bad
  change a+q.val=a+r.val at values
  omega
private theorem eval_injective (k : Nat) : Function.Injective (evalState k) :=
  shift_injective (BodyIngress.machine k).stateCount 7500 3337
/-- Complete actual copied BODY up to its first live terminal callback, at arbitrary allocation.
A copied reject callback is not yet the caller's literal global reject. -/
theorem copied_body (k : Nat) :
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
    let initial : Config (callerMachine k).stateCount R B :=
      ⟨evalState k (entry (sourceMode source M)),⟨H,hH⟩,fun i => prepared T S M F r n g W i.val⟩
    let semantics:=do
      let (c,tail) ← decodeCircuitFull n (bitLength n) bits
      if c.size ≤ g then some ((c.size,Pnp3.Models.Circuit.eval c beta),tail) else none
    ∃ t, t ≤ 1073741824*(R+1)^6 ∧
      (∀ u, u ≤ t → (((callerMachine k).run u initial).state≠evalState k machine.accept)) ∧
      (∀ u, u < t → ((callerMachine k).run u initial).state≠evalState k machine.reject ∧
        ((callerMachine k).run u initial).state≠evalState k (done false) ∧ ((callerMachine k).run u initial).state≠evalState k (done true)) ∧
      match semantics with
      | none => (callerMachine k).run t initial=
          ⟨evalState k machine.reject,⟨H,hH⟩,fun i => image T F r n g W (S-min M S) 0 0 0 0 i.val⟩
      | some ((size,b),tail) => ∃ consumed,
          consumed ≤ W ∧ tail=bits.drop consumed ∧
          (callerMachine k).run t initial=
            ⟨evalState k (done b),⟨H,hH⟩,fun i => image T F r n g W (S-min M S) size consumed (W-consumed) 0 i.val⟩
 := by
  intro B R S z n r g W M Q source beta T hr hs hg hw he ha
  dsimp only
  intro positive arena src eof reg left betaCells right marks gap fence fit hH
  obtain ⟨t,price,noAccept,early,result⟩:=ambient_body B R S z n r g W M Q source beta T
    hr hs hg hw he ha positive arena src eof reg left betaCells right marks gap fence fit hH
  let start : Config machine.stateCount R B:=
    ⟨entry (sourceMode source M),⟨S+z+2+n+1,hH⟩,
      fun i=>prepared T S M (FixedRawLengthFence.fencePos R) r n g W i.val⟩
  have work : ∀ u,u<t → 4≤(machine.run u start).state.val := by
    intro u hu
    by_contra hn
    have h:(machine.run u start).state.val=0 ∨ (machine.run u start).state.val=1 ∨
        (machine.run u start).state.val=2 ∨ (machine.run u start).state.val=3 := by omega
    rcases h with h|h|h|h
    · exact noAccept u (by omega) (Fin.ext h)
    · exact (early u hu).1 (Fin.ext h)
    · exact (early u hu).2.1 (Fin.ext h)
    · exact (early u hu).2.2 (Fin.ext h)
  have transport:=eval_prefix (k:=k) start work
  refine ⟨t,price,?_,?_,?_⟩
  · intro u hu bad
    rw [transport u hu] at bad
    exact noAccept u hu (eval_injective k bad)
  · intro u hu
    rw [transport u (by omega)]
    exact ⟨fun bad=>(early u hu).1 (eval_injective k bad),
      fun bad=>(early u hu).2.1 (eval_injective k bad),
      fun bad=>(early u hu).2.2 (eval_injective k bad)⟩
  · rw [transport t le_rfl]
    dsimp only at result ⊢
    generalize hs:(do
      let (c,tail) ← decodeCircuitFull n (bitLength n) (window source M W)
      if c.size ≤ g then some ((c.size,Pnp3.Models.Circuit.eval c beta),tail) else none)=spec at result ⊢
    cases spec with
    | none=>rw [result]
    | some pair=>
      rcases pair with ⟨⟨size,b⟩,tail⟩
      obtain ⟨consumed,hw,ht,done⟩:=result
      exact ⟨consumed,hw,ht,by rw [done]⟩
#print axioms copied_body
end PhysicalCallerClosure
