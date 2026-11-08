import IngressAllocation.RawNormal
import IngressAllocation.RawVirtual
import IngressAllocation.EofTrace
import IngressAllocation.VirtualLift
import IngressAllocation.Consumers
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.RawNormal","IngressAllocation","normal_consumer_heads","normalHeads"),
      ("IngressAllocation.RawVirtual","IngressAllocation","physical_virtual_heads","physicalVirtual"),
      ("IngressAllocation.EofTrace","IngressAllocation","eof_raw_heads","eofHeads"),
      ("IngressAllocation.VirtualLift","IngressAllocation","virtual_consumer_heads","virtualHeads"),
      ("IngressAllocation.Consumers","IngressAllocation","raw_of_bounded_consumers","rawBounded"),
      ("FullWeight.Raw","FullWeight","cap_weight","capWeight")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique exhaustive accepted footprint closure {mod}/{key}: {found.map Prod.fst}"
private def BoundedConsumer (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Prop:=
  ∃ t,Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
    (encodePair x w) t (12*(pairLength a m+1)^2) ∧
    (((BodyIngress.machine k).run t
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)) ∨
     ∃ mode:Fin 3,((BodyIngress.machine k).run t
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        BodyIngress.body k (SerializedBody.entry mode))
private theorem weight_exceeds_length (k n : Nat) : bitLength n < Cursor.Target.W k n:=by
  have base : 1 ≤ n^k+k:=by
    by_cases zero : k=0
    · subst k;simp
    · omega
  have scale:=Nat.mul_le_mul_left (bitLength n+4) base
  dsimp only [Cursor.Target.W]
  nlinarith only [scale]
set_option maxRecDepth 4000 in
private theorem bounded_virtual (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (branch : min (9+2*z+2^pr.2.n) (a+m)=a+m ∨
      (min (9+2*z+2^pr.2.n) (a+m) < a+m ∧
        a+m-min (9+2*z+2^pr.2.n) (a+m) < Cursor.Target.W k pr.2.n))
    (oldBound : ∃ t,((AllArityCursor.machine k).run t
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩) ∧
      Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2))
    (s : Nat)
    (atEntry : ((IngressRepair.machine k).run s
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=VirtualLeaf.entry k)
    (atHead : ((IngressRepair.machine k).run s
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val=a+m+z+pr.2.n+3)
    (first : ∀ u,u < s → ((IngressRepair.machine k).run u
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠ VirtualLeaf.entry k)
    (result : ((BodyIngress.machine k).run (s+5)
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false))) : BoundedConsumer k x w:=by
  obtain ⟨T,reached,heads⟩:=oldBound
  have repaired : ((IngressRepair.machine k).run T
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=VirtualLeaf.entry k:=by
    rw [IngressRepair.accepted_transport k x w accepted T]
    exact reached
  have firstLe : s ≤ T:=by
    by_contra late
    exact first T (by omega) repaired
  have footprint : Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
      (encodePair x w) s (12*(pairLength a m+1)^2):=by
    intro u hu;exact heads u (hu.trans firstLe)
  have actual:=virtualHeads k x w accepted parsed z gamma branch s atEntry atHead first footprint
  exact ⟨s+5,actual,Or.inl result⟩
set_option maxRecDepth 4000 in
private theorem all_bounded (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) : BoundedConsumer k x w:=by
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=FullIngressClosure.raw k x w accepted
  let S:=a+m;let n:=pr.2.n;let p:=min (9+2*z+2^n) S;let r:=S-p
  by_cases atEOF : p=S
  · obtain ⟨_positive,_logical,_zeros,_decoded,_t,s,_st,_price,_oldEnd,oldFirst,firstOld,_atEntry,_localPrice,done,_safe,_first⟩:=eof atEOF
    obtain ⟨T,_hH,oldEnd,heads⟩:=eofHeads k x w accepted parsed z gamma atEOF
    have oldState : ((AllArityCursor.machine k).run T
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩):=by rw [oldEnd];rfl
    apply bounded_virtual k x w accepted parsed z gamma (Or.inl atEOF) ⟨T,oldState,heads⟩ s
    · rw [oldFirst]
    · rw [oldFirst]
    · exact firstOld
    · rw [done]
  · have phys : p < S:=lt_of_le_of_ne (Nat.min_le_right _ _) atEOF
    obtain ⟨_fit,branch⟩:=physical phys
    rcases branch with ⟨overflow,_logical,leaf⟩|⟨ellFits,branch⟩
    · have over : r < Cursor.Target.W k n:=overflow.trans (weight_exceeds_length k n)
      obtain ⟨_positive,_logical,_zeros,_decoded,_t,s,_st,_price,_oldEnd,oldFirst,firstOld,_atEntry,_localPrice,done,_safe,_first⟩:=leaf
      apply bounded_virtual k x w accepted parsed z gamma (Or.inr ⟨phys,over⟩)
        (physicalVirtual k x w accepted parsed z gamma phys over) s
      · rw [oldFirst]
      · rw [oldFirst]
      · exact firstOld
      · rw [done]
    · rcases branch with normal|⟨v2,v3,v4,v5,d0,cap,_logical,leaf⟩
      · obtain ⟨wFits,_rest⟩:=normal
        obtain ⟨t,heads,mode,atEntry⟩:=normalHeads k x w accepted parsed z gamma phys ellFits wFits
        exact ⟨t,heads,Or.inr ⟨mode,atEntry⟩⟩
      · have over : r < Cursor.Target.W k n:=capWeight k n r v2 v3 v4 v5 d0 cap
        obtain ⟨_positive,_logical,_zeros,_decoded,_t,s,_st,_price,_oldEnd,oldFirst,firstOld,_atEntry,_localPrice,done,_safe,_first⟩:=leaf
        apply bounded_virtual k x w accepted parsed z gamma (Or.inr ⟨phys,over⟩)
          (physicalVirtual k x w accepted parsed z gamma phys over) s
        · rw [oldFirst]
        · rw [oldFirst]
        · exact firstOld
        · rw [done]
set_option maxRecDepth 4000 in
theorem raw (k : Nat) : Target.Raw k:=by
  exact rawBounded k (fun x w accepted=>all_bounded k x w accepted)
end IngressAllocation
