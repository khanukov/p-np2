import TotalIngressClosure.SmallProducer
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.SmallProducer","TotalIngressClosure","small_producer_supported","smallSupported"),
      ("TotalIngressClosure.WideProducer","TotalIngressClosure","wide_producer_first","wideSupported"),
      ("IngressAllocation.AllProducer","IngressAllocation","producer_seq_prefix","seqPrefix")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique actual producer prefix {mod}/{key}: {found.map Prod.fst}"
private theorem producer_supported {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    ∃ (t : Nat) (hL:a+m+z+2 < tapeLength R B),t ≤ 144*(R+1)^2 ∧
      SmallIngress.producer.run t (initialConfig SmallIngress.producer B (encodePair x w))=
        ⟨SmallIngress.producer.accept,⟨a+m+z+2,hL⟩,SmallIngress.prepared B x w z n⟩ ∧
      (∀ u,u < t → (SmallIngress.producer.run u (initialConfig SmallIngress.producer B (encodePair x w))).state ≠
        SmallIngress.producer.accept) ∧
      ∀ u,u ≤ t → (SmallIngress.producer.run u
        (initialConfig SmallIngress.producer B (encodePair x w))).head.val ≤ 12*(R+1)^2 := by
  intro R B
  by_cases small:n < 3
  · exact smallSupported x w header tag gamma small physical
  · obtain ⟨z',other,_consumed,_lower,upper,_borrow,_digits,_high⟩:=decremented_register_digits x w header
    have same:z'=z:=Option.some.inj (other.symm.trans gamma)
    subst z'
    have wide:2 ≤ z:=by
      by_contra no
      have short:2^(z+1) ≤ (2:Nat)^2:=Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
      norm_num at short
      omega
    obtain ⟨t,hL,price,done,first,heads⟩:=wideSupported x w header tag gamma wide cap
    have sameTape:SmallIngress.prepared B x w z n=FixedRawLengthFence.countdownTape B x w z 0 n:=by
      funext i
      dsimp only [SmallIngress.prepared]
      rw [if_neg (by omega)]
    have price':t ≤ 128*(R+1)^2:=price
    exact ⟨t,hL,by omega,by rw [sameTape];exact done,first,heads⟩
/-- The real repaired producer's FIRST Cursor ingress, all arities and no rho premise.
All conditional geometry is discharged by the eventual total raw partition. -/
private theorem repaired_entry (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let c:=initialConfig (IngressRepair.machine k) B (encodePair x w)
    ∃ (t : Nat) (hL:a+m+z+2 < tapeLength R B),t ≤ 144*(R+1)^2 ∧
      (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
        ⟨(Cursor.machine k).start,⟨a+m+z+2,hL⟩,SmallIngress.prepared B x w z n⟩ ∧
      (∀ u,u ≤ t → ((IngressRepair.machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (∀ u,u < t → ((IngressRepair.machine k).run u c).state.val < 288) := by
  intro R B c
  obtain ⟨t,hL,price,done,first,heads⟩:=producer_supported x w header tag gamma physical cap
  have part:=seqPrefix (Cursor.machine k) x w t (a+m+z+2) _ hL done first heads
  have equal(u : Nat):(IngressRepair.machine k).run u c=(AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w)):=
    IngressRepair.supported_transport k x w z tag gamma physical u
  refine ⟨t,hL,price,?_,?_,?_⟩
  · rw [equal]
    exact part.1
  · intro u hu
    rw [equal]
    exact part.2.1 u hu
  · intro u hu
    rw [equal]
    exact part.2.2 u hu
end TotalIngressClosure
