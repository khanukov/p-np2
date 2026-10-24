import IngressAllocation.RawLength
import IngressAllocation.RawWeight
import IngressAllocation.CleanupTrace
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.RawLength","IngressAllocation","physical_length_heads","rawLength"),
      ("IngressAllocation.RawWeight","IngressAllocation","physical_weight_heads","rawWeight"),
      ("IngressAllocation.CleanupTrace","IngressAllocation","cleanup_d0_heads","cleanD0"),
      ("IngressAllocation.CleanupTrace","IngressAllocation","cleanup_d2_heads","cleanD2"),
      ("VirtualReady.Raw","VirtualReady","actual_base","actualBase"),
      ("VirtualReady.Raw","VirtualReady","computed_frame","computedFrame"),
      ("RawPrelude.Kernel","RawPrelude","overlay_frame","overlayFrame"),
      ("VirtualLeaf.Raw","VirtualLeaf","width","acceptedWidth")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique exhaustive physical virtual interval {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem physical_virtual_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical : min (9+2*z+2^pr.2.n) (a+m) < a+m)
    (over : a+m-min (9+2*z+2^pr.2.n) (a+m) < Cursor.Target.W k pr.2.n) :
    ∃ t,((AllArityCursor.machine k).run t
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩) ∧
      Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=pr.2.n;let L:=S+z+2;let F:=3*R+2
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  have width:=acceptedWidth x w accepted parsed
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨base,fresh⟩:=actualBase x w gamma cap rows
  obtain ⟨_legacy,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R B at fit
  change ∀ i : Fin (tapeLength R B),F < i.val → V i.val=none at fresh
  have fr:=computedFrame V S z n F r base (by
    intro i lo hi
    exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
  have rp : 0 < r:=by change p < S at physical;dsimp only [r];omega
  have replay (s : Nat) (config : Config (Cursor.machine k).stateCount R B) :
      (AllArityCursor.machine k).run s (SmallIngress.producer.seqEmbedRight (Cursor.machine k) config)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run s config):=by
    change (SmallIngress.producer.seq (Cursor.machine k)).run s _=_
    rw [UniformTM.seq_run_right]
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=width.trans pair
  have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
  have envelope : F+5*r+n+7 ≤ 12*(R+1)^2:=by
    dsimp only [F];nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
  by_cases ellFits : bitLength n ≤ r
  · obtain ⟨t,priorHeads,_before,outcome⟩:=rawWeight k x w accepted parsed z gamma physical ellFits
    rcases outcome with ⟨fits,_⟩|⟨v2,v3,v4,v5,d0,_cap,h,atCap⟩
    · exact False.elim (Nat.not_lt_of_ge fits over)
    · let T:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
      have frame:=overlayFrame Y L n (2^n) F r v2 v3 v4 v5 d0 fr rp
      have clean:=cleanD0 k R B L n (2^n) F r T frame fit
      dsimp only at clean
      let d:=F-(L+n+1)+18*r+6*n+44
      refine ⟨t+d,?_,?_⟩
      · rw [UniformTM.run_add,atCap,replay]
        change SmallIngress.producer.seqRight (Cursor.machine k) _=_
        rw [clean.1]
      · intro u hu
        by_cases early : u ≤ t
        · exact priorHeads u early
        · rw [show u=t+(u-t) by omega,UniformTM.run_add,atCap,replay]
          exact (clean.2.2 (u-t) (by change u-t ≤ d;omega)).trans envelope
  · obtain ⟨t,h,atLength,priorHeads,_before⟩:=rawLength k x w accepted parsed z gamma physical
    change (if bitLength n ≤ r then L else F+r+n+3) < tapeLength R B at h
    change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
        ⟨if bitLength n ≤ r then L else F+r+n+3,h⟩,fun i=>Y i.val⟩ at atLength
    let d:=(n+r+4)+(F-(L+n+1)+18*r+6*n+44)
    have oddEq : (if decide ((r+1)%2=1) then 250 else 304)=(if (r+1)%2=1 then 250 else 304):=by
      by_cases h : (r+1)%2=1 <;> simp only [h,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false]
    have clean:=cleanD2 k R B L n (2^n) F r Y fr fit (decide ((r+1)%2=1))
    dsimp only at clean
    rw [oddEq] at clean
    have start : (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),
          ⟨F+r+n+3,by simpa only [if_neg ellFits] using h⟩,fun i=>Y i.val⟩:=by
      simpa only [if_neg ellFits] using atLength
    refine ⟨t+d,?_,?_⟩
    · rw [UniformTM.run_add,start,replay]
      change SmallIngress.producer.seqRight (Cursor.machine k) _=_
      rw [clean.1]
    · intro u hu
      by_cases early : u ≤ t
      · exact priorHeads u early
      · rw [show u=t+(u-t) by omega,UniformTM.run_add,start,replay]
        exact (clean.2.2 (u-t) (by change u-t ≤ d;omega)).trans envelope
end IngressAllocation
