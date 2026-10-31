import IngressAllocation.AllProducer
import IngressAllocation.StreamOrbit
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.AllProducer","IngressAllocation","all_producer_first","producerFirst"),
      ("IngressAllocation.AllProducer","IngressAllocation","producer_seq_prefix","seqPrefix"),
      ("IngressAllocation.LargeProducer","IngressAllocation","large_producer_first","largeFirst"),
      ("IngressAllocation.StreamOrbit","IngressAllocation","orbit_heads","orbitHeads"),
      ("SmallOrbit.Runtime","SmallOrbit","prepared_frame","preparedFrame"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.room","fr_room"),
      ("SmallOrbit.Runtime","SmallOrbit","clear_extend","clearExtend"),
      ("SmallOrbit.Runtime","SmallOrbit","accepted_facts","acceptedFacts"),
      ("VirtualLeaf.Raw","VirtualLeaf","width","acceptedWidth")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique raw orbit footprint interface {mod}/{key}: {found.map Prod.fst}"
private theorem full_zero (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    9+2*z ≤ a+m ∧ (z=0 → pr.2.n=0) := by
  have empty : z=0 → pr.2.n=0 := by
    obtain ⟨consumed,header,target⟩:=contentInput?_target_eq_contentHeader
      (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) parsed
    rw [← target] at header
    obtain ⟨other,payload,otherGamma,read,value,_rest⟩:=
      (contentHeader?_eq_some_iff_gammaZeros_payload _).1 header
    have same : other=z:=Option.some.inj (otherGamma.symm.trans gamma)
    intro hz0
    have otherZero : other=0:=same.trans hz0
    rw [otherZero] at read value
    change some 0=some payload at read
    have pzero : payload=0:=Option.some.inj read.symm
    simp only [pow_zero,pzero] at value
    omega
  refine ⟨?_,empty⟩
  by_cases small : pr.2.n < 3
  · obtain ⟨other,full,_bits⟩:=SmallOrbit.small_header_physical k x w accepted parsed small
    have same : z=(if pr.2.n=0 then 0 else 1):=Option.some.inj (gamma.symm.trans other)
    rw [same]
    split_ifs at full ⊢ <;> omega
  · have semantic:=(acceptedFacts k x w accepted).2
    have normal : 3 ≤ pr.2.n := by omega
    exact GammaSupport.exact k x w parsed semantic normal z gamma
private theorem raw_stream_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr) :
    ∃ (z T : Nat) (_hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧ T ≤ 4096*((pairLength a m)+1)^2 ∧
      let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
      let p:=Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)
      ∃ hp : p < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
        SmallIngress.machine.run T (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
          SmallIngress.producer.seqEmbedRight Stream.machine
            ⟨Stream.q (if p=a+m then 57 else 58),⟨p,hp⟩,
              fun i=>Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩ ∧
        ∀ u,u ≤ T → (SmallIngress.machine.run u
          (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ 12*((pairLength a m)+1)^2 := by
  let R:=pairLength a m
  let B:=FixedRawLengthFence.allocation R
  obtain ⟨z,tp,hL,gamma,prePrice,producerRun,first,producerHeads⟩:=producerFirst k x w accepted parsed
  have width:=acceptedWidth x w accepted parsed
  have cap:=AcceptedBody.strict_capacity x w gamma width
  obtain ⟨full,zero⟩:=full_zero k x w accepted parsed z gamma
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  let S:=a+m;let n:=pr.2.n;let F:=FixedRawLengthFence.fencePos R
  let T0:=Body.extend (SmallIngress.prepared B x w z n)
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
  have frame:=preparedFrame x w gamma cap full zero
  obtain ⟨_room,_scratch,hF,_fence⟩:=Stream.raw_budget_cells x w gamma cap
  have hH : S+z+n+3 < tapeLength R B:=(fr_room frame).trans hF
  obtain ⟨tb,bodyPrice,bodyHeads,hp,finished⟩:=orbitHeads T0 frame hF rows hL hH
  have Ueq : Body.clear T0 (S+z+3) n=U :=
    clearExtend (SmallIngress.prepared B x w z n) (S+z+2) n (by
      change S+z+2+n+1 < tapeLength R B
      omega)
  rw [Ueq] at finished
  have entry : (⟨Stream.machine.start,⟨S+z+2,hL⟩,SmallIngress.prepared B x w z n⟩ : Config 64 R B)=
      ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i=>T0 i.val⟩ := by
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i;exact (Body.extend_read _ i).symm
  have replay (s : Nat) : SmallIngress.machine.run (tp+s)
      (initialConfig SmallIngress.machine B (encodePair x w))=SmallIngress.producer.seqEmbedRight Stream.machine
        (Stream.machine.run s ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i=>T0 i.val⟩) := by
    have hand:=SmallIngress.producer.seq_handoff Stream.machine
      (initialConfig SmallIngress.producer B (encodePair x w)) first (by rw [producerRun]) s
    rw [producerRun,entry] at hand
    exact hand
  have price : tp+tb ≤ 4096*(R+1)^2 := by
    have pair : S ≤ R := by dsimp only [S,R,pairLength];omega
    have gammaBound:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    have nz : n ≤ 3*R := by
      have nw : n ≤ S:=width
      omega
    have zz : z ≤ R := by dsimp only [S] at pair;omega
    have dist : S-(9+2*z) ≤ R := (Nat.sub_le _ _).trans pair
    have square : R+1 ≤ (R+1)^2 := by
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (R+1) (show 1≤R+1 by omega)
    change tp ≤ 144*(R+1)^2 at prePrice
    change tb ≤ n+2+InputRead.readClock n z (S-(9+2*z))+64*(F+1)^2 at bodyPrice
    dsimp only [InputRead.readClock,F,FixedRawLengthFence.fencePos] at bodyPrice
    nlinarith only [prePrice,bodyPrice,nz,zz,dist,square]
  obtain ⟨_start,oldHeads,_before⟩:=seqPrefix Stream.machine x w tp (S+z+2) _ hL producerRun first producerHeads
  refine ⟨z,tp+tb,hH,gamma,price,hp,?_,?_⟩
  · rw [replay tb,finished]
  · intro u hu
    by_cases early : u ≤ tp
    · exact oldHeads u early
    · rw [show u=tp+(u-tp) by omega,replay]
      have bound:=bodyHeads (u-tp) (by omega)
      have fenceEnvelope : F ≤ 12*(R+1)^2 := by
        dsimp only [F,FixedRawLengthFence.fencePos]
        nlinarith only [Nat.zero_le R,Nat.zero_le (R*R)]
      exact bound.trans fenceEnvelope
end IngressAllocation
