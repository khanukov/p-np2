import CarryReadyCompletion.Virtual
namespace CarryReadyCompletion
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let allNames:=(← getEnv).constants.toList.map Prod.fst
  for (mod,ns,key,localName) in [
    ("CarryReadyCompletion.Native","CarryReadyCompletion","complete_body","oldBody"),
    ("CarryReadyCompletion.Virtual","CarryReadyCompletion","virtual_cuts","oldCuts"),
    ("CarryWindow.Transport","CarryWindow","transport","oldTransport"),
    ("CarryWindow.Raw","CarryWindow","lift430","oldLift"),
    ("VirtualLeaf.Raw","VirtualLeaf","width","oldWidth"),
    ("AllArityBitLength.Raw","AllArityBitLength","actual_cells","oldCells"),
    ("AllArityBitLength.Raw","AllArityBitLength","Cells.arena","oldArena"),
    ("CarryWindow.Raw","CarryWindow","normalFrame","oldFrame"),
    ("CarryWindow.Geometry","CarryWindow","Banks.blank","oldBlank"),
    ("CarryWindow.Geometry","CarryWindow","Banks.bank1","oldBank1"),
    ("CarryReadyCompletion.Native","CarryReadyCompletion","complete_frame","oldComplete"),
    ("CarryReadyCompletion.Native","CarryReadyCompletion","work_safe","oldSafe"),
    ("FullWeight.Raw","FullWeight","cap_weight","oldCap")] do
    let found:=allNames.filter fun n => n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    unless found.length=1 do throwError "Nonunique typed closure term {localName}: {found}"
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) found.head! :: st.openDecls}
private theorem raw_price (R n r d : Nat) (hn : n      ≤      R) (hr : r      ≤      R)
    (hd : d      ≤      8192*(r+1)*(3*R+2+5*r+n+9)^2) : d      ≤      1048576*(R+1)^3 := by
  have b : 3*R+2+5*r+n+9      ≤      11*(R+1) := by omega
  have mult:=Nat.mul_le_mul (Nat.mul_le_mul_left 8192 (show r+1      ≤      R+1 by omega)) (Nat.pow_le_pow_left b 2)
  nlinarith only [hd,mult,Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]
private theorem total_price (k R t d : Nat) (ht : t      ≤      268435456*(k+1)*(R+1)^4)
    (hd : d      ≤      1048576*(R+1)^3) : t+d      ≤      8589934592*(k+1)*(R+1)^5 := by
  have a : (R+1)^3      ≤      (R+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have b : (R+1)^4      ≤      (R+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have liftedT:=Nat.mul_le_mul_left (268435456*(k+1)) b
  have ad:=Nat.mul_le_mul (show 1048576      ≤      1048576*(k+1) by omega) a
  nlinarith only [ht,hd,liftedT,ad,Nat.zero_le ((k+1)*(R+1)^5)]
theorem body (k : Nat) : CarryWindow.Target.Body k := by
  exact oldBody k
private theorem normal_extension (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    (pr : Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q))
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let T:=CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0
    let c:=initialConfig (CarryWindow.machine k) B (encodePair x w)
    let base:=initialConfig (CanonicalLeaf.machine k) B (encodePair x w)
    p < S  →  Cursor.Target.W k n ≤ r  →
    ∀ (fit : F+5*r+n+7 < tapeLength R B) (t : Nat), t ≤ 268435456*(k+1)*(R+1)^4  →
    (CanonicalLeaf.machine k).run t base=VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) fit⟩,fun i => T i.val⟩)  →
    (∀ u, u < t  →  ((CanonicalLeaf.machine k).run u base).state ≠ VirtualLeaf.embed k
      (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))))  →
    ∃ d, d ≤ 1048576*(R+1)^3  ∧  t+d ≤ 8589934592*(k+1)*(R+1)^5  ∧
      (CarryWindow.machine k).run t c=CarryWindow.config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) fit⟩,fun i => T i.val⟩))  ∧
      (∀ u, u < t  →  ((CarryWindow.machine k).run u c).state ≠ CarryWindow.embed k (VirtualLeaf.embed k
        (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k)))))  ∧
      (CarryWindow.machine k).run (t+d) c=⟨CarryWindow.ready k,⟨F+1,lt_of_le_of_lt (by omega : F+1 ≤ F+5*r+n+7) fit⟩,
        fun i => CarryWindow.Target.image T F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) i.val⟩  ∧
      (∀ u, u ≤ t+d  →  ((CarryWindow.machine k).run u c).state ≠ (CarryWindow.machine k).accept  ∧
        ((CarryWindow.machine k).run u c).state ≠ (CarryWindow.machine k).reject)  ∧
      (∀ u, u < t+d  →  ((CarryWindow.machine k).run u c).state ≠ CarryWindow.ready k) := by
  intro S R B n L F p r U V X Y Z T c base phys wr fit t ht firstRun first
  have tx:=oldLift base (t:=t) (congrArg Config.state firstRun) first
  have prefixRun (u : Nat) (hu : u  ≤  t) : (CarryWindow.machine k).run u c=
      CarryWindow.config k ((CanonicalLeaf.machine k).run u base) := tx.1 u hu
  have reached : (CarryWindow.machine k).run t c=CarryWindow.config k (VirtualLeaf.config k
      (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3    ≤    F+5*r+n+7) fit⟩,fun i => T i.val⟩)) :=
    (tx.1 t le_rfl).trans (congrArg (CarryWindow.config k) firstRun)
  have width:=oldWidth x w accepted parsed
  have capacity:=AcceptedBody.strict_capacity x w gamma width
  have paid:=Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨cells,_,fresh⟩:=oldCells x w gamma capacity paid
  have arena:=oldArena cells
  change S+z+n+3+2^n  <  F at arena
  have Hsame : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  have room : L+n+1  <  F := by
    rw [Hsame]
    exact (Nat.le_add_right _ _).trans_lt arena
  have gr : n^k+k      ≤      r := by
    have cover:=(VirtualLeaf.decode_leaf k n (fun _ => false)).1
    have mul:=Nat.mul_le_mul_right (n^k+k) (show 1      ≤      bitLength n+4 by omega)
    dsimp only [Cursor.Target.W] at wr; omega
  have rp : 0   <   r:=Nat.sub_pos_of_lt phys
  obtain ⟨fr,shape⟩:=oldFrame V L n F r (n^k+k) (Cursor.Target.W k n) room rp
    (by intro i lo hi; exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
  have blank:=oldBlank fr
  have b1:=oldBank1 fr
  obtain ⟨d,hd,run,_foot,_safe,early⟩:=oldComplete k R B L n F r (n^k+k) (Cursor.Target.W k n) T room gr wr blank b1 shape fit
  have done : (CarryWindow.machine k).run (t+d) c=
      ⟨CarryWindow.ready k,⟨F+1,lt_of_le_of_lt (by omega : F+1    ≤    F+5*r+n+7) fit⟩,
        fun i => CarryWindow.Target.image T F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) i.val⟩ := by
    rw [UniformTM.run_add,reached]; exact run
  have nr : n      ≤      R := by change n      ≤      S at width; dsimp only [R,pairLength]; omega
  have rr : r      ≤      R := by have le:=Nat.sub_le S p; dsimp only [R,pairLength]; omega
  have hd' : d      ≤      1048576*(R+1)^3:=raw_price R n r d nr rr hd
  refine ⟨d,hd',total_price k R t d ht hd',reached,tx.2,done,?_,?_⟩
  · exact oldSafe c (congrArg Config.state done)
  · intro u hu
    by_cases before : u      <      t
    · rw [prefixRun u (by omega)]
      intro bad; have e:=congrArg Fin.val bad
      change ((CanonicalLeaf.machine k).run u base).state.val=(CanonicalLeaf.machine k).stateCount+24 at e
      have lt:=((CanonicalLeaf.machine k).run u base).state.isLt; omega
    · rw [show u=t+(u-t) by omega,UniformTM.run_add,reached]; exact early (u-t) (by omega)

theorem raw (k : Nat) : CarryWindow.Target.Raw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=CanonicalLeaf.accepted_leaf k x w accepted
  let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S; let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (CarryWindow.machine k) B (encodePair x w)
  let base:=initialConfig (CanonicalLeaf.machine k) B (encodePair x w)
  let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
  let deliver (T : Nat       →       Option Bool) : Prop :=
      ∃ positive : 0      <      n, S      ≤      Cursor.Target.M k n z       ∧
      (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false)       ∧
      (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩)       ∧
      ∃ t s, s      ≤      t       ∧       t      ≤      2147483648*(k+1)*(R+1)^5       ∧
      (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩       ∧
      (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩       ∧
      (∀ u, u      <      s       →       ((IngressRepair.machine k).run u old).state      ≠      VirtualLeaf.entry k)       ∧
      (CarryWindow.machine k).run s c=⟨CarryWindow.embed k (CanonicalLeaf.entry k),H,fun i => T i.val⟩       ∧
      s+5      ≤      4294967296*(k+1)*(R+1)^5       ∧
      (CarryWindow.machine k).run (s+5) c=
        ⟨CarryWindow.embed k (CanonicalLeaf.result k false),H,Function.update (fun i => T i.val) H (some false)⟩       ∧
      (∀ u, u      ≤      s+5       →       ((CarryWindow.machine k).run u c).state      ≠      (CarryWindow.machine k).accept       ∧
        ((CarryWindow.machine k).run u c).state      ≠      (CarryWindow.machine k).reject)       ∧
      (∀ u, u      <      s+5       →       ∀ b, ((CarryWindow.machine k).run u c).state      ≠      CarryWindow.embed k (CanonicalLeaf.result k b))
  have virtualTransport (branch : p=S       ∨       (p      <      S       ∧       r      <      Cursor.Target.W k n)) :
      ∀ u, (CarryWindow.machine k).run u c=CarryWindow.config k ((CanonicalLeaf.machine k).run u base) := by
    have safe:=oldCuts k x w accepted pr parsed z gamma branch
    intro u
    exact oldTransport base (t:=u) (fun v _ => safe v) u le_rfl
  refine ⟨pr,parsed,z,hH,gamma,?_,?_⟩
  · intro atEOF
    obtain ⟨pos,logical,zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,done,safe,early⟩:=eof atEOF
    have tx:=virtualTransport (Or.inl atEOF)
    refine ⟨pos,logical,zeros,decoded,t,s,hs,ht,oldT,oldS,first,(tx s).trans (congrArg (CarryWindow.config k) pre),price,
      (tx (s+5)).trans (congrArg (CarryWindow.config k) done),?_,?_⟩
    · intro u hu
      constructor
      all_goals intro bad; have e:=congrArg Config.state (tx u)
      all_goals first
        | exact (safe u hu).1 ((CarryWindow.controls k).2.2.2.2 (e.symm.trans bad))
        | exact (safe u hu).2 ((CarryWindow.controls k).2.2.2.2 (e.symm.trans bad))
    · intro u hu b bad
      have e:=congrArg Config.state (tx u)
      exact early u hu b ((CarryWindow.controls k).2.2.2.2 (e.symm.trans bad))
  · intro phys
    change p   <   S at phys
    obtain ⟨fit,outcome⟩:=physical phys
    change F+5*r+n+7   <   tapeLength R B at fit
    refine ⟨fit,?_⟩
    have close (branch : r      <      Cursor.Target.W k n) :
        ∀ (T : Nat       →       Option Bool) (pos : 0      <      n) (logical : S      ≤      Cursor.Target.M k n z)
        (zeros : ∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false)
        (decoded : (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=some (Pnp3.Models.Circuit.input ⟨0,pos⟩))
        (t s : Nat), s      ≤      t       →       t      ≤      2147483648*(k+1)*(R+1)^5       →
        (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩       →
        (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩       →
        (∀ u, u      <      s       →       ((IngressRepair.machine k).run u old).state      ≠      VirtualLeaf.entry k)       →
        (CanonicalLeaf.machine k).run s base=⟨CanonicalLeaf.entry k,H,fun i => T i.val⟩       →
        s+5      ≤      4294967296*(k+1)*(R+1)^5       →
        (CanonicalLeaf.machine k).run (s+5) base=⟨CanonicalLeaf.result k false,H,Function.update (fun i => T i.val) H (some false)⟩       →
        (∀ u, u      ≤      s+5       →       ((CanonicalLeaf.machine k).run u base).state      ≠      (CanonicalLeaf.machine k).accept       ∧       ((CanonicalLeaf.machine k).run u base).state      ≠      (CanonicalLeaf.machine k).reject)       →
        (∀ u, u      <      s+5       →       ∀ b, ((CanonicalLeaf.machine k).run u base).state      ≠      CanonicalLeaf.result k b)       →
        deliver T := by
      intro T pos logical zeros decoded t s hs ht oldT oldS first pre price done safe early
      have tx:=virtualTransport (Or.inr ⟨phys,branch⟩)
      refine ⟨pos,logical,zeros,decoded,t,s,hs,ht,oldT,oldS,first,(tx s).trans (congrArg (CarryWindow.config k) pre),price,
        (tx (s+5)).trans (congrArg (CarryWindow.config k) done),?_,?_⟩
      · intro u hu; constructor
        all_goals intro bad; have e:=congrArg Config.state (tx u)
        all_goals first
          | exact (safe u hu).1 ((CarryWindow.controls k).2.2.2.2 (e.symm.trans bad))
          | exact (safe u hu).2 ((CarryWindow.controls k).2.2.2.2 (e.symm.trans bad))
      · intro u hu b bad; have e:=congrArg Config.state (tx u)
        exact early u hu b ((CarryWindow.controls k).2.2.2.2 (e.symm.trans bad))
    rcases outcome with ⟨over,logical,leaf⟩ | ⟨fits,tail⟩
    · obtain ⟨pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,done,safe,early⟩:=leaf
      change r    <    bitLength n at over
      have cover:=(VirtualLeaf.decode_leaf k n (fun _ => false)).1
      exact Or.inl ⟨over,logical,close (by omega) _ pos logical' zeros decoded t s hs ht oldT oldS first pre price done safe early⟩
    · refine Or.inr ⟨fits,?_⟩
      rcases tail with ⟨wr,t,_d,ht,_hd,_total,firstRun,first,_normal⟩ | ⟨v2,v3,v4,v5,dd,cap,logical,leaf⟩
      · obtain ⟨d,hd,total,runW,firstW,done,safe,early⟩:=
          normal_extension k x w accepted pr parsed z gamma phys wr fit t ht firstRun first
        exact Or.inl ⟨wr,t,d,ht,hd,total,runW,firstW,done,safe,early⟩
      · obtain ⟨pos,logical',zeros,decoded,t,s,hs,ht,oldT,oldS,first,pre,price,done,safe,early⟩:=leaf
        have small:=oldCap k n r v2 v3 v4 v5 dd cap
        exact Or.inr ⟨v2,v3,v4,v5,dd,cap,logical,close small _ pos logical' zeros decoded t s hs ht oldT oldS first pre price done safe early⟩

theorem check_body (k : Nat) :
  ∀ {N B : Nat} (L n F r g W : Nat) (beta : Fin n       →       Bool) (T : Nat       →       Option Bool),
    let D : Nat       →       Nat := fun j => match j with
      | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
      | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
    L+n+1       <       F       →       g       ≤       r       →       W       ≤       r       →
    T L=none       →       T (L+n+1)=none       →
    (∀ j : Fin n, T (L+n+1-1-j.val)=some (beta j))       →
    (∀ j, j       ≤       6       →       T (D j)=none)       →
    (∀ i, D 0       <       i       →       i       <       D 1       →       T i=some true)       →
    (∀ i, D 1       <       i       →       i       <       D 2       →       ∃ b, T i=some b)       →
    (∀ i, D 2       <       i       →       i       <       D 3       →       T i=some false)       →
    (∀ i, D 3       <       i       →       i       <       D 4       →       T i=some (decide (i       ≤       D 3+g)))       →
    (∀ i, D 4       <       i       →       i       <       D 5       →       T i=some (decide (i       ≤       D 4+W)))       →
    (∀ i, D 5       <       i       →       i       <       D 6       →       T i=some false)       →
    ∀ fit : D 6       <       tapeLength N B,
    let c : Config (CarryWindow.machine k).stateCount N B :=
      ⟨CarryWindow.embed k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k)
        (Cursor.q k (430+93*k)))),⟨D 2,by dsimp only [D] at fit ⊢; omega⟩,fun i => T i.val⟩
    ∃ t, t       ≤       8192*(r+1)*(D 6+2)^2       ∧
      (CarryWindow.machine k).run t c=⟨CarryWindow.ready k,⟨D 0,by dsimp only [D] at fit ⊢; omega⟩,
        fun i => CarryWindow.Target.image T F r n g (bitLength W) 0 0 W i.val⟩       ∧
      (∀ u, u       ≤       t       →       D 0       ≤       ((CarryWindow.machine k).run u c).head.val       ∧
        ((CarryWindow.machine k).run u c).head.val       ≤       D 6)       ∧
      (∀ u, u       ≤       t       →       ((CarryWindow.machine k).run u c).state       ≠       (CarryWindow.machine k).accept       ∧
        ((CarryWindow.machine k).run u c).state       ≠       (CarryWindow.machine k).reject)       ∧
      (∀ u, u       <       t       →       ((CarryWindow.machine k).run u c).state       ≠       CarryWindow.ready k) := by
  exact body k

theorem check_raw (k : Nat) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true       →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr       ∧
    ∃ (z : Nat) (hH : a+m+z+pr.2.n+3       <       tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z       ∧
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let c:=initialConfig (CarryWindow.machine k) B (encodePair x w)
    let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
    let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
    let virtual (T : Nat       →       Option Bool) : Prop :=
      ∃ positive : 0      <      n, S      ≤      Cursor.Target.M k n z       ∧
      (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false)       ∧
      (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩)       ∧
      ∃ t s, s      ≤      t       ∧       t      ≤      2147483648*(k+1)*(R+1)^5       ∧
      (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩       ∧
      (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩       ∧
      (∀ u, u      <      s       →       ((IngressRepair.machine k).run u old).state      ≠      VirtualLeaf.entry k)       ∧
      (CarryWindow.machine k).run s c=⟨CarryWindow.embed k (CanonicalLeaf.entry k),H,fun i => T i.val⟩       ∧
      s+5      ≤      4294967296*(k+1)*(R+1)^5       ∧
      (CarryWindow.machine k).run (s+5) c=
        ⟨CarryWindow.embed k (CanonicalLeaf.result k false),H,Function.update (fun i => T i.val) H (some false)⟩       ∧
      (∀ u, u      ≤      s+5       →       ((CarryWindow.machine k).run u c).state      ≠      (CarryWindow.machine k).accept       ∧
        ((CarryWindow.machine k).run u c).state      ≠      (CarryWindow.machine k).reject)       ∧
      (∀ u, u      <      s+5       →       ∀ b, ((CarryWindow.machine k).run u c).state      ≠      CarryWindow.embed k (CanonicalLeaf.result k b))
    (p=S       →       virtual V)       ∧
    (p      <      S       →       ∃ fit : F+5*r+n+7       <       tapeLength R B,
      (r      <      bitLength n       ∧       S      <      Cursor.Target.M k n z       ∧       virtual (Cursor.Target.image V k S n z F))       ∨
      (bitLength n      ≤      r       ∧
        ((Cursor.Target.W k n      ≤      r       ∧       ∃ t d,
          t      ≤      268435456*(k+1)*(R+1)^4       ∧       d      ≤      1048576*(R+1)^3       ∧
          t+d      ≤      8589934592*(k+1)*(R+1)^5       ∧
          (CarryWindow.machine k).run t c=CarryWindow.config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3      ≤      F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩))       ∧
          (∀ u, u      <      t       →       ((CarryWindow.machine k).run u c).state      ≠      CarryWindow.embed k (VirtualLeaf.embed k
            (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k)))))       ∧
          (CarryWindow.machine k).run (t+d) c=⟨CarryWindow.ready k,⟨F+1,lt_of_le_of_lt (by omega : F+1      ≤      F+5*r+n+7) fit⟩,
            fun i => CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0)
              F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) i.val⟩       ∧
          (∀ u, u      ≤      t+d       →       ((CarryWindow.machine k).run u c).state      ≠      (CarryWindow.machine k).accept       ∧
            ((CarryWindow.machine k).run u c).state      ≠      (CarryWindow.machine k).reject)       ∧
          (∀ u, u      <      t+d       →       ((CarryWindow.machine k).run u c).state      ≠      CarryWindow.ready k))       ∨
        (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d       ∧
          S      <      Cursor.Target.M k n z       ∧       virtual (Cursor.Target.image V k S n z F))))) := by
  exact raw k

#print axioms CarryReadyCompletion.body
#print axioms CarryReadyCompletion.raw
#print axioms CarryReadyCompletion.check_body
#print axioms CarryReadyCompletion.check_raw
theorem projection_ready :
    let x : Bitstring 13:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==9 || i.val==12
    let w : Bitstring 14:=fun _ => false
    ∃ t, ((CarryWindow.machine 0).run t (initialConfig (CarryWindow.machine 0) 28224 (encodePair x w))).state=CarryWindow.ready 0 := by
  dsimp only
  let x : Bitstring 13:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==9 || i.val==12
  let w : Bitstring 14:=fun _ => false
  obtain ⟨pr,parsed,z,_hH,gamma,_eof,physical⟩:=raw 0 x w CarryWindow.projection_normal_accepted
  have g : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some 1 := by decide
  have z1 : z=1:=Option.some.inj (gamma.symm.trans g)
  obtain ⟨_consumed,header,target⟩:=contentInput?_target_eq_contentHeader _ _ parsed
  have h : contentHeader? (Fin.append x w)=some (1,3) := by decide
  have n1 : pr.2.n=1:=target.trans (congrArg Prod.fst (Option.some.inj (header.symm.trans h)))
  obtain ⟨_fit,branch⟩:=physical (by rw [z1,n1]; decide)
  rcases branch with ⟨over,_,_⟩ | ⟨_fits,tail⟩
  · rw [z1,n1] at over; have bad : ¬(27-min (9+2*1+2^1) 27     <     bitLength 1) := by norm_num [bitLength,Nat.log2]
    exact False.elim (bad over)
  · rcases tail with ⟨_wr,t,d,_ht,_hd,_total,_entry,_first,last,_safe,_early⟩ | ⟨v2,v3,v4,v5,dd,cap,_,_⟩
    · exact ⟨t+d,congrArg Config.state last⟩
    · have over:=oldCap 0 pr.2.n (27-min (9+2*z+2^pr.2.n) 27) v2 v3 v4 v5 dd cap
      rw [z1,n1] at over
      have bad : ¬(27-min (9+2*1+2^1) 27     <     Cursor.Target.W 0 1) := by norm_num [Cursor.Target.W,bitLength,Nat.log2]
      exact False.elim (bad over)
theorem check_projection_ready :
    let x : Bitstring 13:=fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==9 || i.val==12
    let w : Bitstring 14:=fun _ => false
    ∃ t, ((CarryWindow.machine 0).run t (initialConfig (CarryWindow.machine 0) 28224 (encodePair x w))).state=CarryWindow.ready 0 := by
  exact projection_ready
#print axioms CarryReadyCompletion.projection_ready
#print axioms CarryReadyCompletion.check_projection_ready
open Lean Elab Command in run_cmd do
  let env ← getEnv
  for n in env.header.moduleNames do logInfo m!"imported|{n}"
  for (n,ci) in env.constants.toList do
    let owner:=match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => env.mainModule.toString
    if "CarryReadyCompletion.".isPrefixOf owner then
      logInfo m!"owner-all|{owner}|{n}|{n.isInternal}"
      if !n.isInternal && !(n.toString.splitOn ".").any (fun c => "_".isPrefixOf c || "match_".isPrefixOf c) then
        logInfo m!"owned-public-name|{owner}|{n}"
        logInfo m!"public-type|{n}|{ci.type}"
        let kind:=match ci with
          | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
          | .axiomInfo _ => "axiomatic" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
        logInfo m!"public-kind|{n}|{kind}"
  for n in [``CappedWeight.Target.image.eq_1,``AllArityBitLength.Target.seedImage.eq_1,
      ``RuntimeBitLength.Target.fullImage.eq_1,``Cursor.Target.scratch.eq_1,``Cursor.Target.image.eq_1,``Cursor.Target.W.eq_1,
      ``Pnp4.Frontier.ContractExpansion.gammaLen.eq_1,``Pnp4.Frontier.ContractExpansion.gammaBit.eq_1] do
    if let some i := env.getModuleIdxFor? n then logInfo m!"imported-equation|{env.header.moduleNames[i]!}|{n}"
  let opts ← getOptions
  logInfo m!"option|maxHeartbeats|{Lean.maxHeartbeats.get opts}"
  logInfo m!"option|maxRecDepth|{Lean.maxRecDepth.get opts}"
  logInfo m!"option|registeredDefaultHeartbeats|{Lean.maxHeartbeats.get {}}"
  logInfo m!"option|registeredDefaultRecursion|{Lean.maxRecDepth.get {}}"

end CarryReadyCompletion
