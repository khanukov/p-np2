import BodyIngress.Native
namespace BodyIngress
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private theorem inject_old {k : Nat} {s t : Fin (CarryWindow.machine k).stateCount}
    (h : old k s=old k t) : s=t := by
  have e:=congrArg (fun q : Fin ((CarryWindow.machine k).stateCount+7500+2035) => q.val) h
  dsimp only [old] at e
  exact Fin.ext e
private theorem lift_leaf {k N B s : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (H : Fin (tapeLength N B)) (T : Fin (tapeLength N B)    →    Option Bool)
    (pre:(CarryWindow.machine k).run s c=⟨CarryWindow.embed k (CanonicalLeaf.entry k),H,T⟩)
    (done:(CarryWindow.machine k).run (s+5) c=⟨CarryWindow.embed k (CanonicalLeaf.result k false),H,Function.update T H (some false)⟩)
    (safe:∀ u,u   ≤   s+5    →    ((CarryWindow.machine k).run u c).state   ≠   (CarryWindow.machine k).accept    ∧
      ((CarryWindow.machine k).run u c).state   ≠   (CarryWindow.machine k).reject)
    (early:∀ u,u   <   s+5    →    ∀ b,((CarryWindow.machine k).run u c).state   ≠   CarryWindow.embed k (CanonicalLeaf.result k b)) :
    (machine k).run s (config k c)=⟨old k (CarryWindow.embed k (CanonicalLeaf.entry k)),H,T⟩    ∧
    (machine k).run (s+5) (config k c)=⟨old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,Function.update T H (some false)⟩    ∧
    (∀ u,u   ≤   s+5    →    ((machine k).run u (config k c)).state   ≠   (machine k).accept    ∧    ((machine k).run u (config k c)).state   ≠   (machine k).reject)    ∧
    (∀ u,u   <   s+5    →    ∀ b,((machine k).run u (config k c)).state   ≠   old k (CarryWindow.embed k (CanonicalLeaf.result k b))) := by
  have notReady:((CarryWindow.machine k).run (s+5) c).state   ≠   CarryWindow.ready k:=by
    rw [done]
    intro bad;have eqv:=congrArg Fin.val bad
    change (CanonicalLeaf.result k false).val=(CanonicalLeaf.machine k).stateCount+24 at eqv
    have hi:=(CanonicalLeaf.result k false).isLt;omega
  have tx:=transport_stopped c notReady
  constructor
  · rw [tx s (by omega),pre]
    rfl
  · constructor
    · rw [tx (s+5) le_rfl,done]
      rfl
    · constructor
      · intro u hu
        rw [tx u hu]
        constructor
        · intro bad
          exact (safe u hu).1 (inject_old (k:=k) bad)
        · intro bad
          exact (safe u hu).2 (inject_old (k:=k) bad)
      · intro u hu b
        rw [tx u (by omega)]
        intro bad
        exact early u hu b (inject_old (k:=k) bad)
/-- Complete old accepted cut on the new table. This ends at Ready/leaf, before installer completion. -/
theorem accepted_frontier (k : Nat) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true    →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr    ∧
    ∃ (z : Nat) (hH : a+m+z+pr.2.n+3    <    tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z    ∧
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let c:=initialConfig (machine k) B (encodePair x w)
    let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
    let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
    let virtual (T : Nat    →    Option Bool) : Prop :=
      ∃ positive : 0   <   n, S   ≤   Cursor.Target.M k n z    ∧
      (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false)    ∧
      (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩)    ∧
      ∃ t s, s   ≤   t    ∧    t   ≤   2147483648*(k+1)*(R+1)^5    ∧
      (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩    ∧
      (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩    ∧
      (∀ u, u   <   s    →    ((IngressRepair.machine k).run u old).state   ≠   VirtualLeaf.entry k)    ∧
      (BodyIngress.machine k).run s c=⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.entry k)),H,fun i => T i.val⟩    ∧
      s+5   ≤   4294967296*(k+1)*(R+1)^5    ∧
      (BodyIngress.machine k).run (s+5) c=
        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,Function.update (fun i => T i.val) H (some false)⟩    ∧
      (∀ u, u   ≤   s+5    →    ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).accept    ∧
        ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).reject)    ∧
      (∀ u, u   <   s+5    →    ∀ b, ((BodyIngress.machine k).run u c).state   ≠   BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))
    (p=S    →    virtual V)    ∧
    (p   <   S    →    ∃ fit : F+5*r+n+7    <    tapeLength R B,
      (r   <   bitLength n    ∧    S   <   Cursor.Target.M k n z    ∧    virtual (Cursor.Target.image V k S n z F)) ∨
      (bitLength n   ≤   r    ∧
        ((Cursor.Target.W k n   ≤   r    ∧    ∃ t d,
          t   ≤   268435456*(k+1)*(R+1)^4    ∧    d   ≤   1048576*(R+1)^3    ∧
          t+d   ≤   8589934592*(k+1)*(R+1)^5    ∧
          (BodyIngress.machine k).run t c=BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3   ≤   F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩)))    ∧
          (∀ u, u   <   t    →    ((BodyIngress.machine k).run u c).state   ≠   BodyIngress.old k (CarryWindow.embed k (VirtualLeaf.embed k
            (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))))))    ∧
          (BodyIngress.machine k).run (t+d) c=⟨BodyIngress.old k (CarryWindow.ready k),⟨F+1,lt_of_le_of_lt (by omega : F+1   ≤   F+5*r+n+7) fit⟩,
            fun i => CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0)
              F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) i.val⟩    ∧
          (∀ u, u   ≤   t+d    →    ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).accept    ∧
            ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).reject)    ∧
          (∀ u, u   <   t+d    →    ((BodyIngress.machine k).run u c).state   ≠   BodyIngress.old k (CarryWindow.ready k))) ∨
        (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d    ∧
          S   <   Cursor.Target.M k n z    ∧    virtual (Cursor.Target.image V k S n z F)))))
 := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=CarryReadyCompletion.raw k x w accepted
  refine ⟨pr,parsed,z,hH,gamma,?_,?_⟩
  · intro atEOF
    obtain ⟨pos,logical,zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,done,safe,early⟩:=eof atEOF
    obtain ⟨pre',done',safe',early'⟩:=lift_leaf _ _ _ pre done safe early
    exact ⟨pos,logical,zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre',price,done',safe',early'⟩
  · intro phys
    obtain ⟨fit,branch⟩:=physical phys
    refine ⟨fit,?_⟩
    rcases branch with ⟨over,logical,leaf⟩ | ⟨bitsFit,tail⟩
    · obtain ⟨pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,done,safe,early⟩:=leaf
      obtain ⟨pre',done',safe',early'⟩:=lift_leaf _ _ _ pre done safe early
      exact Or.inl ⟨over,logical,pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre',price,done',safe',early'⟩
    · refine Or.inr ⟨bitsFit,?_⟩
      rcases tail with ⟨wr,t,d,ht,hd,total,atW,firstW,atReady,safe,early⟩ | ⟨v2,v3,v4,v5,dd,cap,logical,leaf⟩
      · have tx:=transport _ early
        refine Or.inl ⟨wr,t,d,ht,hd,total,(tx t (by omega)).trans (congrArg (config k) atW),?_,
          (tx (t+d) le_rfl).trans (congrArg (config k) atReady),?_,?_⟩
        · intro u hu bad
          exact firstW u hu (inject_old (k:=k) ((congrArg Config.state (tx u (by omega))).symm.trans bad))
        · intro u hu;constructor
          · intro bad;exact (safe u hu).1 (inject_old (k:=k) ((congrArg Config.state (tx u hu)).symm.trans bad))
          · intro bad;exact (safe u hu).2 (inject_old (k:=k) ((congrArg Config.state (tx u hu)).symm.trans bad))
        · intro u hu bad
          exact early u hu (inject_old (k:=k) ((congrArg Config.state (tx u (by omega))).symm.trans bad))
      · obtain ⟨pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,done,safe,early⟩:=leaf
        obtain ⟨pre',done',safe',early'⟩:=lift_leaf _ _ _ pre done safe early
        exact Or.inr ⟨v2,v3,v4,v5,dd,cap,logical,pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre',price,done',safe',early'⟩

theorem check_accepted_frontier (k : Nat) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true    →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr    ∧
    ∃ (z : Nat) (hH : a+m+z+pr.2.n+3    <    tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z    ∧
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let c:=initialConfig (machine k) B (encodePair x w)
    let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
    let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
    let virtual (T : Nat    →    Option Bool) : Prop :=
      ∃ positive : 0   <   n, S   ≤   Cursor.Target.M k n z    ∧
      (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false)    ∧
      (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩)    ∧
      ∃ t s, s   ≤   t    ∧    t   ≤   2147483648*(k+1)*(R+1)^5    ∧
      (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩    ∧
      (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩    ∧
      (∀ u, u   <   s    →    ((IngressRepair.machine k).run u old).state   ≠   VirtualLeaf.entry k)    ∧
      (BodyIngress.machine k).run s c=⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.entry k)),H,fun i => T i.val⟩    ∧
      s+5   ≤   4294967296*(k+1)*(R+1)^5    ∧
      (BodyIngress.machine k).run (s+5) c=
        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,Function.update (fun i => T i.val) H (some false)⟩    ∧
      (∀ u, u   ≤   s+5    →    ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).accept    ∧
        ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).reject)    ∧
      (∀ u, u   <   s+5    →    ∀ b, ((BodyIngress.machine k).run u c).state   ≠   BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))
    (p=S    →    virtual V)    ∧
    (p   <   S    →    ∃ fit : F+5*r+n+7    <    tapeLength R B,
      (r   <   bitLength n    ∧    S   <   Cursor.Target.M k n z    ∧    virtual (Cursor.Target.image V k S n z F)) ∨
      (bitLength n   ≤   r    ∧
        ((Cursor.Target.W k n   ≤   r    ∧    ∃ t d,
          t   ≤   268435456*(k+1)*(R+1)^4    ∧    d   ≤   1048576*(R+1)^3    ∧
          t+d   ≤   8589934592*(k+1)*(R+1)^5    ∧
          (BodyIngress.machine k).run t c=BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3   ≤   F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩)))    ∧
          (∀ u, u   <   t    →    ((BodyIngress.machine k).run u c).state   ≠   BodyIngress.old k (CarryWindow.embed k (VirtualLeaf.embed k
            (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))))))    ∧
          (BodyIngress.machine k).run (t+d) c=⟨BodyIngress.old k (CarryWindow.ready k),⟨F+1,lt_of_le_of_lt (by omega : F+1   ≤   F+5*r+n+7) fit⟩,
            fun i => CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0)
              F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) i.val⟩    ∧
          (∀ u, u   ≤   t+d    →    ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).accept    ∧
            ((BodyIngress.machine k).run u c).state   ≠   (BodyIngress.machine k).reject)    ∧
          (∀ u, u   <   t+d    →    ((BodyIngress.machine k).run u c).state   ≠   BodyIngress.old k (CarryWindow.ready k))) ∨
        (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d    ∧
          S   <   Cursor.Target.M k n z    ∧    virtual (Cursor.Target.image V k S n z F)))))
 := by
  exact accepted_frontier k

/-- Entire reviewed missing-FIRST-payload domain remains a literal raw rejection. -/
theorem missing_payload (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (positive : 0 < z) (short : a+m=9+z) :
    ∃ t,t ≤ 128*(pairLength a m+1)^2  ∧
      ((machine k).run t (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(machine k).reject  ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  obtain ⟨t,ht,done,negative⟩:=CarryWindow.missing_payload k x w z tag gamma positive short
  have notReady:((CarryWindow.machine k).run t (initialConfig (CarryWindow.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠ CarryWindow.ready k:=by
    rw [done]
    intro bad;have e:=congrArg Fin.val bad
    change (CanonicalLeaf.machine k).reject.val=(CanonicalLeaf.machine k).stateCount+24 at e
    have h:=(CanonicalLeaf.machine k).reject.isLt;omega
  have tx:=transport_stopped _ notReady t le_rfl
  refine ⟨t,ht,?_,negative⟩
  have state:=congrArg Config.state tx
  change _=old k ((CarryWindow.machine k).run t _).state at state
  rw [done] at state
  exact state
/-- Same fixed repaired bad word, uniformly in k; no arbitrary-malformed verdict claim. -/
theorem stall_reject (k : Nat) :
    let x : Bitstring 11:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
    let w : Bitstring 0:=Fin.elim0
    ∃ t,t ≤ 128*(pairLength 11 0+1)^2  ∧
      ((machine k).run t (initialConfig (machine k) 9216 (encodePair x w))).state=(machine k).reject  ∧
      PartAEndpoint.thresholdContentWitnessRelation k 11 0 x w=false := by
  dsimp only
  exact missing_payload k _ _ 2 (by decide) (by decide) (by decide) (by decide)

theorem check_missing_payload (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (positive : 0 < z) (short : a+m=9+z) :
    ∃ t,t ≤ 128*(pairLength a m+1)^2  ∧
      ((machine k).run t (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(machine k).reject  ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  exact missing_payload k x w z tag gamma positive short
theorem check_stall_reject (k : Nat) :
    let x : Bitstring 11:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
    let w : Bitstring 0:=Fin.elim0
    ∃ t,t ≤ 128*(pairLength 11 0+1)^2  ∧
      ((machine k).run t (initialConfig (machine k) 9216 (encodePair x w))).state=(machine k).reject  ∧
      PartAEndpoint.thresholdContentWitnessRelation k 11 0 x w=false := by
  exact stall_reject k
end BodyIngress
