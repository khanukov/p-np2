import TotalIngressClosure.WideProducer
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.Producer","IngressAllocation","small_producer_first","smallFirst"),
      ("SmallOrbit.Runtime","SmallOrbit","small_tape_eq","smallTape")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique generic small-arity raw producer {mod}/{key}: {found.map Prod.fst}"
private theorem small_header_bits {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (small:n < 3) (physical:z=0 ∨ 9+z < a+m) :
    z=(if n=0 then 0 else 1) ∧ (if n=0 then 9 else 11) ≤ a+m ∧
      FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n==0) ∧
      (n≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true) ∧
      (n≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (n==2)) := by
  obtain ⟨z',width,_len,lower,upper,_borrow,_digits,_high⟩:=decremented_register_digits x w header
  have same:z'=z:=Option.some.inj (width.symm.trans gamma)
  subst z'
  obtain ⟨support,term,zeros⟩:=(FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma
  have zsmall:z < 2:=by
    by_contra no
    have four:4 ≤ 2^z:=Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega : 2 ≤ z)
    omega
  by_cases zero:z=0
  · subst z
    have nzero:n=0:=by norm_num at upper;omega
    subst n
    exact ⟨rfl,by simpa only [if_pos rfl] using (show 9 ≤ a+m by omega),by simpa only [Nat.add_zero] using term,by omega,by omega⟩
  · have one:z=1:=by omega
    subst z
    have full:11 ≤ a+m:=by rcases physical with h|h <;> omega
    have npos:0 < n:=by norm_num at lower;omega
    obtain ⟨other,payload,otherGamma,read,value,_consumed⟩:=
      (contentHeader?_eq_some_iff_gammaZeros_payload _).1 header
    have same:other=1:=Option.some.inj (otherGamma.symm.trans gamma)
    subst other
    let b:Bool:=(Fin.append x w) ⟨10,by omega⟩
    have oneRead:VirtualZeroTailReader.readNatBE (Fin.append x w) (2*(a+m)+1) 10 1=
        some (if b then 1 else 0):=by
      simp [VirtualZeroTailReader.readNatBE,VirtualZeroTailReader.readBit?,padRead,
        show 10 < 2*(a+m)+1 by omega,show 10 < a+m by omega,b]
    change VirtualZeroTailReader.readNatBE (Fin.append x w) (2*(a+m)+1) 10 1=some payload at read
    have content:payload=(if b then 1 else 0):=Option.some.inj (read.symm.trans oneRead)
    have target:n=(if b then 2 else 1):=by
      rw [content] at value
      norm_num at value
      cases hb:b <;> simp only [hb,Bool.false_eq_true,↓reduceIte] at value ⊢ <;> omega
    refine ⟨by rw [if_neg (by omega)],by rw [if_neg (by omega)];exact full,?_,?_,?_⟩
    · have zeroBit:=zeros 0 (by decide : 0 < 1)
      have beqZero:(n==0)=false:=by
        cases n with
        | zero=>omega
        | succ j=>rfl
      simpa only [Nat.add_zero,beqZero] using zeroBit
    · intro _
      simpa using term
    · intro _
      change (if h:10 < a+m then some ((Fin.append x w) ⟨10,h⟩) else none)=some (n==2)
      rw [dif_pos (by omega)]
      change some b=some (n==2)
      rw [target]
      cases b <;> rfl
private theorem small_producer_supported {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (small:n < 3) (physical:z=0 ∨ 9+z < a+m) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    ∃ (t : Nat) (hL:a+m+z+2 < tapeLength R B),t ≤ 144*(R+1)^2 ∧
      SmallIngress.producer.run t (initialConfig SmallIngress.producer B (encodePair x w))=
        ⟨SmallIngress.producer.accept,⟨a+m+z+2,hL⟩,SmallIngress.prepared B x w z n⟩ ∧
      (∀ u,u < t → (SmallIngress.producer.run u (initialConfig SmallIngress.producer B (encodePair x w))).state ≠
        SmallIngress.producer.accept) ∧
      ∀ u,u ≤ t → (SmallIngress.producer.run u
        (initialConfig SmallIngress.producer B (encodePair x w))).head.val ≤ 12*(R+1)^2 := by
  intro R B
  obtain ⟨zEq,full,h8,h9,h10⟩:=small_header_bits x w header gamma small physical
  let nf:Fin 3:=⟨n,small⟩
  obtain ⟨t,hL,price,done,first,heads⟩:=smallFirst x w nf tag full h8 h9 h10
  have tape:=smallTape (B:=B) x w nf full h8
  rw [tape] at done
  rw [zEq]
  have price' : t ≤ 64*(R+1)^2:=price
  exact ⟨t,hL,by omega,done,first,heads⟩
end TotalIngressClosure
