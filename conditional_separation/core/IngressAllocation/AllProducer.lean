import IngressAllocation.LargeProducer
import IngressAllocation.PrefixLift
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.Producer","IngressAllocation","small_producer_first","smallFirst"),
      ("IngressAllocation.LargeProducer","IngressAllocation","large_producer_first","largeFirst"),
      ("SmallOrbit.Runtime","SmallOrbit","small_tape_eq","smallTape"),
      ("IngressRepair.Runtime","IngressRepair","accepted_header","acceptedHeader"),
      ("VirtualLeaf.Raw","VirtualLeaf","width","acceptedWidth")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique SAME-pr producer interface {mod}/{key}: {found.map Prod.fst}"
private theorem all_producer_first (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    ∃ (z t : Nat) (hL : a+m+z+2 < tapeLength R B),
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧ t ≤ 144*(R+1)^2 ∧
      SmallIngress.producer.run t (initialConfig SmallIngress.producer B (encodePair x w))=
        ⟨SmallIngress.producer.accept,⟨a+m+z+2,hL⟩,SmallIngress.prepared B x w z pr.2.n⟩ ∧
      (∀ u,u < t → (SmallIngress.producer.run u (initialConfig SmallIngress.producer B (encodePair x w))).state ≠
        SmallIngress.producer.accept) ∧
      ∀ u,u ≤ t → (SmallIngress.producer.run u
        (initialConfig SmallIngress.producer B (encodePair x w))).head.val ≤ 12*(R+1)^2 := by
  intro R B
  obtain ⟨tag,_z,_gamma,_payload⟩:=acceptedHeader k x w accepted
  by_cases small : pr.2.n < 3
  · obtain ⟨gamma,full,h8,h9,h10⟩:=SmallOrbit.small_header_physical k x w accepted parsed small
    let nf : Fin 3:=⟨pr.2.n,small⟩
    obtain ⟨t,hL,price,done,first,heads⟩:=smallFirst x w nf tag full h8 h9 h10
    refine ⟨if pr.2.n=0 then 0 else 1,t,?_,gamma,?_,?_,first,heads⟩
    · exact hL
    · change t ≤ 144*(pairLength a m+1)^2
      omega
    · have tape:=smallTape (B:=B) x w nf full h8
      rw [tape] at done
      exact done
  · obtain ⟨z,_hz,gamma,stage⟩:=largeFirst k x w parsed tag (by omega)
    have width:=acceptedWidth x w accepted parsed
    have capacity:=AcceptedBody.strict_capacity x w gamma width
    obtain ⟨t,hL,price,done,first,heads⟩:=stage capacity
    have sameTape : SmallIngress.prepared B x w z pr.2.n=FixedRawLengthFence.countdownTape B x w z 0 pr.2.n := by
      funext i
      dsimp only [SmallIngress.prepared]
      rw [if_neg (by omega)]
    exact ⟨z,t,hL,gamma,by
      change t ≤ 144*(pairLength a m+1)^2
      dsimp only [FixedRawLengthFence.countdownDeadline] at price
      omega,
      by rw [sameTape];exact done,first,heads⟩
private theorem producer_seq_prefix (suffix : UniformTM) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (t L : Nat) (T : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))) → Option Bool)
    (hL : L < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)))
    (done : SmallIngress.producer.run t (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      ⟨SmallIngress.producer.accept,⟨L,hL⟩,T⟩)
    (first : ∀ u,u < t → (SmallIngress.producer.run u
      (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠ SmallIngress.producer.accept)
    (heads : ∀ u,u ≤ t → (SmallIngress.producer.run u
      (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ 12*(pairLength a m+1)^2) :
    let B:=FixedRawLengthFence.allocation (pairLength a m)
    let M:=SmallIngress.producer.seq suffix
    let c:=initialConfig M B (encodePair x w)
    M.run t c=SmallIngress.producer.seqEmbedRight suffix ⟨suffix.start,⟨L,hL⟩,T⟩ ∧
    (∀ u,u ≤ t → (M.run u c).head.val ≤ 12*(pairLength a m+1)^2) ∧
    ∀ u,u < t → (M.run u c).state.val < 288 := by
  intro B M c
  let old:=initialConfig SmallIngress.producer B (encodePair x w)
  have tx (u : Nat) (hu : u ≤ t) : M.run u c=SmallIngress.producer.seqEmbedRouted suffix (SmallIngress.producer.run u old) :=
    SmallIngress.producer.seq_run_left suffix old first u hu
  have noReject (u : Nat) (hu : u ≤ t) : (SmallIngress.producer.run u old).state ≠ SmallIngress.producer.reject := by
    intro bad
    have eq:=SmallIngress.producer.run_reject_of_le old bad hu
    have reject:=(congrArg Config.state eq).trans bad
    rw [done] at reject
    exact SmallIngress.producer.accept_ne_reject reject
  refine ⟨?_,?_,?_⟩
  · rw [tx t le_rfl,done]
    rfl
  · intro u hu;rw [tx u hu];exact heads u hu
  · intro u hu
    rw [tx u (Nat.le_of_lt hu)]
    change (SmallIngress.producer.seqRoute suffix _).val < 288
    rw [UniformTM.seqRoute,if_neg (first u hu),if_neg (noReject u (Nat.le_of_lt hu))]
    exact (SmallIngress.producer.run u old).state.isLt
end IngressAllocation
