import VirtualLeaf.Raw
namespace VirtualLeaf
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
/-- The preserved actual q613 endpoint excludes verdicts on its whole prefix. -/
theorem normal_work (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (t : Nat) (h : Fin (tapeLength N B)) (T : Fin (tapeLength N B) → Option Bool)
    (done : (machine k).run t c=config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (613+93*k),h,T⟩)) :
    ∀ u, u≤t → ((machine k).run u c).state≠(machine k).accept ∧
      ((machine k).run u c).state≠(machine k).reject := by
  have value : ((machine k).run t c).state.val=901+93*k := by
    rw [done]
    change 288+(613+93*k)%Cursor.stateCount k=901+93*k
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]; omega
  have a : (machine k).accept.val=327 := (AllArityCursor.control_values k).2.2.1
  have r : (machine k).reject.val=328 := (AllArityCursor.control_values k).2.2.2
  apply (machine k).no_terminal_of_le c
  · intro bad; have eq:=congrArg Fin.val bad; rw [value,a] at eq; omega
  · intro bad; have eq:=congrArg Fin.val bad; rw [value,r] at eq; omega
/-- Original relation on a literal 7+8 word, proved with the original serializer. -/
theorem tiny_accepted :
    let x : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
    let w : Bitstring 8:=fun i => i.val==2 || i.val==5
    PartAEndpoint.thresholdContentWitnessRelation 0 7 8 x w=true := by
  dsimp only
  let x : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
  let w : Bitstring 8:=fun i => i.val==2 || i.val==5
  let codec:=treeCircuitWitnessCodec (thresholdPoly 0)
  let tt : TruthTable 1:=fun i => i.val==1
  let input:=CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec (zeroPrefixFields codec 1 tt)
  have len1 : bitLength 1=1 := by norm_num [bitLength,Nat.log2]
  have len5 : bitLength 5=3 := by norm_num [bitLength,Nat.log2]
  have ambient : treeMCSPPrefixM codec 1=21 := by
    change 8+(2*bitLength 2-1)+2+bitLength ((bitLength 1+4)*(1^0+0))+(bitLength 1+4)*(1^0+0)=21
    norm_num [bitLength,Nat.log2]
  have header : contentHeader? (Fin.append x w)=some (1,3) := by decide
  have wb : codec.witnessBits 1=5 := by
    change (bitLength 1+4)*(1^0+0)=5
    rw [len1]; rfl
  have gl : gammaLen 1=3 := by norm_num [gammaLen,bitLength,Nat.log2]
  have iw : idxWidth codec.witnessBits 1=3 := by dsimp only [idxWidth]; rw [wb,len5]
  have query : padWord (Fin.append x w) (treeMCSPPrefixM codec 1)=zeroPrefixQueryValue codec 1 tt := by
    funext ⟨j,hj⟩
    have bound : j<21 := by omega
    dsimp only [padWord,zeroPrefixQueryValue,encodeTreeMCSPPrefixFields,zeroPrefixFields]
    simp only [tagLen,gl,iw,Pnp3.Models.Partial.tableLen]
    interval_cases j
    all_goals norm_num [padRead,x,w,tt,Fin.append,Fin.addCases,treePrefixTag,gammaBit,natBitBE,bitLength,Nat.log2,Pnp3.Models.Partial.tableLen]
    all_goals rfl
  have parsed : contentInput? codec (Fin.append x w)=some ⟨1,input⟩ := by
    unfold contentInput?
    rw [header]
    dsimp only
    rw [query,parse_zeroPrefixQueryValue]; rfl
  have blank : contentWitness codec (Fin.append x w) 1=(fun _ => false) := by
    funext j
    dsimp only [contentWitness]
    rw [ambient]
    exact padRead_ge _ (by omega)
  have semantic : contentSemanticAccepts codec (Fin.append x w)=true := by
    apply (contentSemanticAccepts_eq_true_iff codec _).2
    refine ⟨⟨1,input⟩,parsed,?_,?_⟩
    · intro j; exact Fin.elim0 j
    · change codec.verifies 1 tt (contentWitness codec (Fin.append x w) 1)
      rw [blank]
      refine ⟨Pnp3.Models.Circuit.input ⟨0,by decide⟩,treeCircuitWitnessCodec_decode_blank_pos 0 (by decide),by decide,?_⟩
      intro beta
      change beta ⟨0,by decide⟩=(Pnp3.Models.bitVecToNat beta % 2==1)
      have bit : Pnp3.Models.bitVecToNat beta=if beta ⟨0,by decide⟩ then 1 else 0 := by
        change 0+(if beta ⟨0,by decide⟩ then 1 else 0)=_
        exact Nat.zero_add _
      rw [bit]; cases beta ⟨0,by decide⟩ <;> rfl
  unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation
  split
  · simpa only [AcceptedBody.concat_eq_append] using semantic
  · rename_i guard
    exact (guard (by norm_num [Pnp3.ComplexityInterfaces.certificateLength])).elim
/-- The reviewed missing-FIRST-payload bad word remains a literal reject, all k. -/
theorem stall_reject (k : Nat) :
    let x : Bitstring 11:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
    let w : Bitstring 0:=Fin.elim0
    ∃ t, t≤128*(pairLength 11 0+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) 9216 (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k 11 0 x w=false := by
  dsimp only
  apply missing_payload k _ _ 2 (by decide) (by decide) (by decide) (by decide)
/-- A genuine accepted raw virtual fixture, not an accepted host-trace assumption. -/
theorem tiny_raw :
    let x : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
    let w : Bitstring 8:=fun i => i.val==2 || i.val==5
    ∃ t, t≤4294967296*(pairLength 7 8+1)^5 ∧
      ((machine 0).run t (initialConfig (machine 0) 9216 (encodePair x w))).state=result 0 false ∧
      ((machine 0).run t (initialConfig (machine 0) 9216 (encodePair x w))).head.val=20 := by
  dsimp only
  let x : Bitstring 7:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6
  let w : Bitstring 8:=fun i => i.val==2 || i.val==5
  obtain ⟨pr,parsed,z,_hH,gamma,_eof,physical⟩:=accepted_leaf 0 x w tiny_accepted
  have g : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some 1 := by decide
  have z1 : z=1:=Option.some.inj (gamma.symm.trans g)
  obtain ⟨consumed,header,target⟩:=contentInput?_target_eq_contentHeader _ _ parsed
  have h : contentHeader? (Fin.append x w)=some (1,3) := by decide
  have n1 : pr.2.n=1:=target.trans (congrArg Prod.fst (Option.some.inj (header.symm.trans h)))
  have phys : min (9+2*z+2^pr.2.n) (7+8) < 7+8 := by rw [z1,n1]; decide
  obtain ⟨_fit,outcome⟩:=physical phys
  rcases outcome with ⟨over,_⟩ | ⟨_fits,tail⟩
  · have bad : ¬(7+8-min (9+2*1+2^1) (7+8) < bitLength 1) := by norm_num [bitLength,Nat.log2]
    exact False.elim (bad (by simpa only [z1,n1] using over))
  · rcases tail with ⟨wr,_⟩ | ⟨_v2,_v3,_v4,_v5,_d,_cap,_logical,leaf⟩
    · have bad : ¬(Cursor.Target.W 0 1 ≤ 7+8-min (9+2*1+2^1) (7+8)) := by norm_num [Cursor.Target.W,bitLength,Nat.log2]
      exact False.elim (bad (by simpa only [z1,n1] using wr))
    · obtain ⟨_positive,_logical,_zeros,_decoded,t,s,_hs,_ht,_old,_firstCfg,_first,_prefix,price,run,_safe⟩:=leaf
      refine ⟨_,price,congrArg Config.state run,?_⟩
      have eq:=congrArg (fun c => c.head.val) run
      simpa only [z1,n1] using eq
end VirtualLeaf
