import TotalIngressClosure.LengthTotal
import TotalIngressClosure.WeightTotal
import IngressAllocation.CleanupTrace
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
open IngressAllocation (Footprint)
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.LengthTotal","TotalIngressClosure","physical_length_heads","rawLength"),
      ("TotalIngressClosure.WeightTotal","TotalIngressClosure","physical_weight_heads","rawWeight"),
      ("IngressAllocation.CleanupTrace","IngressAllocation","cleanup_d0_heads","cleanD0"),
      ("IngressAllocation.CleanupTrace","IngressAllocation","cleanup_d2_heads","cleanD2"),
      ("VirtualReady.Raw","VirtualReady","actual_base","actualBase"),
      ("VirtualReady.Raw","VirtualReady","computed_frame","computedFrame"),
      ("RawPrelude.Kernel","RawPrelude","overlay_frame","overlayFrame"),
      ("TotalIngressClosure.Header","TotalIngressClosure","table_budget_width","tableWidth"),
      ("VirtualReady.Raw","VirtualReady","Base.arena","baseArena"),
      ("VirtualReady.Raw","VirtualReady","cleared_image","clearImage"),
      ("FullIngressClosure.Frame","FullIngressClosure","arena_room","arenaRoom"),
      ("VirtualReady.Raw","VirtualReady","paint","paint"),
      ("VirtualReady.Raw","VirtualReady","stage","stage"),
      ("VirtualReady.Raw","VirtualReady","cleanup_run","runD2"),
      ("RawPrelude.Kernel","RawPrelude","cleanup_D0","runD0"),
      ("RawPrelude.Kernel","RawPrelude","cleared_overlay","clearOverlay")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      let expectedDef:=key="paint" || key="stage"
      let actualDef:=match ci with | .defnInfo _=>true | _=>false
      let actualTheorem:=match ci with | .thmInfo _=>true | _=>false
      unless (expectedDef && actualDef) || (!expectedDef && actualTheorem) do
        throwError "Wrong expected virtual cleanup declaration kind {n}"
      logInfo m!"private-term|{n}|isDefinition={actualDef}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique exhaustive physical virtual interval {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem physical_virtual_heads (k : Nat) {a m n0 consumed z : Nat} (x:Bitstring a) (w:Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n0,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical:z=0 ∨ 9+z < a+m) (cap:n0 < FixedRawLengthFence.capacity a m z)
    (rows:2^n0 ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n0+3)-1)
    (physical:min (9+2*z+2^n0) (a+m) < a+m)
    (over:a+m-min (9+2*z+2^n0) (a+m) < Cursor.Target.W k n0) :
    let S:=a+m;let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n0) L n0)
    let V:=Stream.Target.image U S z n0 (9+2*z) (2^n0) (2^n0) false
    let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
    ∃ (t:Nat) (hH:S+z+n0+3 < tapeLength R B),
      t ≤ 536870912*(k+1)*(R+1)^3 ∧ S < Cursor.Target.M k n0 z ∧
      (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n0+3,hH⟩,
          fun i=>Cursor.Target.image V k S n0 z F i.val⟩ ∧
      Footprint (AllArityCursor.machine k) (C:=B) (encodePair x w) t (12*(R+1)^2) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=n0;let L:=S+z+2;let F:=3*R+2
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
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
  have arena:S+z+n+3+2^n < F:=baseArena base
  have nr : n ≤ R:=tableWidth R S z n (by dsimp only [R,pairLength];omega) arena
  have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
  have envelope : F+5*r+n+7 ≤ 12*(R+1)^2:=by
    dsimp only [F];nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
  have hH:S+z+n+3 < tapeLength R B:=by omega
  have hh:L+n+1 < tapeLength R B:=by dsimp only [L];omega
  have beyond:S < Cursor.Target.M k n z:=by
    have pe:p=9+2*z+2^n:=Nat.min_eq_left (by change min (9+2*z+2^n) S < S at physical;omega)
    have dist:p+r=S:=by dsimp only [r];omega
    dsimp only [Cursor.Target.M]
    have bound:r < Cursor.Target.W k n:=over
    omega
  have originalFalse(i : Nat)(lo:L < i)(hi:i < L+n+1):V i=some false:=by
    dsimp only [V,Stream.Target.image]
    rw [if_pos ⟨lo,hi⟩,CappedWorkspace.overflow_bits]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
    split_ifs <;> rfl
  have cleared:paint (stage Y F r n 6) (L+1) (L+n+1)=Cursor.Target.image V k S n z F:=by
    have room:L+n+1 < F:=arenaRoom S z n (2^n) F arena
    have core:paint (stage Y F r n 6) (L+1) (L+n+1)=Cursor.Target.scratch V F r n:=
      clearImage V L n F r room originalFalse
    rw [core]
    funext i
    simp only [Cursor.Target.image]
    rw [if_pos physical,if_neg (by omega)]
  by_cases ellFits : bitLength n ≤ r
  · obtain ⟨t,prefixPrice,priorHeads,_before,outcome⟩:=rawWeight k x w header tag gamma firstPhysical cap rows physical ellFits
    rcases outcome with ⟨fits,_⟩|⟨v2,v3,v4,v5,d0,_cap,h,atCap⟩
    · exact False.elim (Nat.not_lt_of_ge fits over)
    · let T:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
      have frame:=overlayFrame Y L n (2^n) F r v2 v3 v4 v5 d0 fr rp
      have clean:=cleanD0 k R B L n (2^n) F r T frame fit
      dsimp only at clean
      let d:=F-(L+n+1)+18*r+6*n+44
      have image:paint (stage T F r n 6) (L+1) (L+n+1)=Cursor.Target.image V k S n z F:=by
        exact (clearOverlay Y L n F r v2 v3 v4 v5 d0 rp).trans cleared
      have executed:=runD0 k R B L n (2^n) F r T frame fit hh
      have total:t+d ≤ 536870912*(k+1)*(R+1)^3:=by
        have tp:t ≤ 268435456*(k+1)*(R+1)^3:=prefixPrice
        have dp:d ≤ 64*(R+1):=by dsimp only [d,F];omega
        nlinarith only [tp,dp,Nat.zero_le R,Nat.zero_le k,Nat.zero_le (R^2),Nat.zero_le (R^3),
          Nat.zero_le (k*R),Nat.zero_le (k*R^2),Nat.zero_le (k*R^3)]
      refine ⟨t+d,hH,total,beyond,?_,?_⟩
      · rw [UniformTM.run_add,atCap,replay]
        rw [executed]
        apply congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k))
        apply Config.ext_parts
        · rfl
        · apply Fin.ext
          dsimp only [L,S,n]
          omega
        · funext i
          exact congrFun image i.val
      · intro u hu
        by_cases early : u ≤ t
        · exact priorHeads u early
        · rw [show u=t+(u-t) by omega,UniformTM.run_add,atCap,replay]
          exact (clean.2.2 (u-t) (by change u-t ≤ d;omega)).trans envelope
  · obtain ⟨t,h,prefixPrice,atLength,priorHeads,_before⟩:=rawLength k x w header tag gamma firstPhysical cap rows physical
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
    have executed:=runD2 k R B L n (2^n) F r Y fr fit (by omega) hh
    have total:t+d ≤ 536870912*(k+1)*(R+1)^3:=by
      have tp:t ≤ 4194304*(R+1)^3:=prefixPrice
      have dp:d ≤ 64*(R+1):=by dsimp only [d,F];omega
      nlinarith only [tp,dp,Nat.zero_le R,Nat.zero_le k,Nat.zero_le (R^2),Nat.zero_le (R^3),
        Nat.zero_le (k*R),Nat.zero_le (k*R^2),Nat.zero_le (k*R^3)]
    refine ⟨t+d,hH,total,beyond,?_,?_⟩
    · rw [UniformTM.run_add,start,replay]
      have clock:d=F-(L+n+1)+19*r+7*n+48:=by dsimp only [d];omega
      rw [clock,executed]
      apply congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k))
      apply Config.ext_parts
      · rfl
      · apply Fin.ext
        dsimp only [L,S,n]
        omega
      · funext i
        exact congrFun cleared i.val
    · intro u hu
      by_cases early : u ≤ t
      · exact priorHeads u early
      · rw [show u=t+(u-t) by omega,UniformTM.run_add,start,replay]
        exact (clean.2.2 (u-t) (by change u-t ≤ d;omega)).trans envelope
end TotalIngressClosure
