import RawCallerClosure.Lift
import RawCallerClosure.Prefix
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName,kind) in [
    (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"Layout","Layout","inductive"),
    (`RawCallerClosure.Frame,`RawCallerClosure,"normal_layout","normalLayout","theorem"),
    (`RawCallerClosure.Lift,`RawCallerClosure,"prepared_high","preparedHigh","theorem"),
    (`RawCallerClosure.Lift,`RawCallerClosure,"extend_image","extendImage","theorem"),
    (`RawCallerClosure.Rows,`RawCallerClosure,"old_body","oldBody","theorem"),
    (`RawCallerClosure.Images,`RawCallerClosure,"ready","ready","definition"),
    (`RawCallerClosure.Images,`RawCallerClosure,"table","table","definition")] do
    let found:=e.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++owner.toString++".") && n.toString.endsWith ("."++ns.toString++"."++leaf)
    let [(n,ci)]:=found | throwError "Nonunique actual ingress result support"
    let actual:=match ci with|.thmInfo _=>"theorem"|.defnInfo _=>"definition"|.inductInfo _=>"inductive"|_=>"other"
    unless actual==kind do throwError "Wrong actual ingress support kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong actual ingress support owner"
    logInfo m!"ordinary-ingress-result|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private def Normal (k N : Nat) (y : Bitstring N) (pre : Nat) : Prop :=
  ∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN:pairLength a m=N),
    decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
    ∃ n z,FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
    let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N
    let B0:=FixedRawLengthFence.allocation N;let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
    let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
    let I:=ready (table B0 x w z n) L n F r (n^k+k) W
    p<S ∧ bitLength n≤r ∧ W≤r ∧ n<FixedRawLengthFence.capacity a m z ∧ S+z+n+3+Q<F ∧
    Layout (allocation k N) N S z n r (n^k+k) W address (9+2*z) Q (Fin.append x w) I ∧
    ∃ hH:S+z+2+n+1<tapeLength N (allocation k N),
      (machine k).run pre (initialConfig (machine k) (allocation k N) y)=callerConfig k
        ⟨PhysicalCallerClosure.oldState k (BodyIngress.body k
          (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address))),⟨S+z+2+n+1,hH⟩,
          fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩
private theorem layoutRoom {B R S z n r g W M A Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool}
    (lay:Layout B R S z n r g W M A Q source T) : S+z+n+3 < tapeLength R B := by
  rcases lay with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,room⟩
  exact room
private theorem nested_config (k : Nat) {N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B) :
    oldConfig k (CertificateGuardClosure.config k (TotalIngressClosure.config k c))=
      callerConfig k ⟨PhysicalCallerClosure.oldState k c.state,c.head,c.tape⟩ := by
  apply Config.ext_parts
  · exact oldBody k c.state
  · dsimp only [oldConfig,callerConfig,CertificateGuardClosure.config,TotalIngressClosure.config,UniformTM.seqEmbedRight]
  · dsimp only [oldConfig,callerConfig,CertificateGuardClosure.config,TotalIngressClosure.config,UniformTM.seqEmbedRight]
private theorem relation_encoded (k N a m : Nat) (y : Bitstring N) (x : Bitstring a) (w : Bitstring m)
    (parsed:decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair))
    (bad:PartAEndpoint.thresholdContentWitnessRelation k a m x w=false) :
    encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false := by
  unfold encodedRelationLanguage
  rw [parsed]
  exact bad
private theorem canonical_pair {N a m a' m' : Nat} {y : Bitstring N} {x : Bitstring a} {w : Bitstring m}
    {x' : Bitstring a'} {w' : Bitstring m'}
    (p:decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair))
    (q:decodePair y=some ((⟨a',x'⟩,⟨m',w'⟩):DecodedPair)) (length:m=a+1) : m'=a'+1 := by
  have eq:=Option.some.inj (p.symm.trans q)
  have shapes:=congrArg (fun v:DecodedPair=>(v.1.1,v.2.1)) eq
  have aa:=congrArg Prod.fst shapes
  have mm:=congrArg Prod.snd shapes
  change a=a' at aa
  change m=m' at mm
  omega
private theorem head_config {states N B : Nat} (q : Fin states) (h j : Nat)
    (hh:h<tapeLength N B) (hj:j<tapeLength N B) (T : Nat → Option Bool) (eq:h=j) :
    (⟨q,⟨h,hh⟩,fun i=>T i.val⟩:Config states N B)=⟨q,⟨j,hj⟩,fun i=>T i.val⟩ := by
  apply Config.ext_parts
  · rfl
  · exact Fin.ext eq
  · rfl
private theorem normal_arrival (k N pre d' a' m' n z : Nat) (y : Bitstring N) (x' : Bitstring a') (w' : Bitstring m')
    (hN':pairLength a' m'=N) (parsed':decodePair y=some ((⟨a',x'⟩,⟨m',w'⟩):DecodedPair))
    (word':y=(hN' ▸ encodePair x' w')) (length':m'=a'+1)
    (tag:FixedContentTagGate.tagMatches (Fin.append x' w')=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x' w')=some z)
    (header:contentHeader? (Fin.append x' w')=some (n,2*z+1))
    (capacity:n<FixedRawLengthFence.capacity a' m' z)
    (arena:a'+m'+z+n+3+2^n<FixedRawLengthFence.fencePos N)
    (physical:min (9+2*z+2^n) (a'+m')<a'+m')
    (ellFits:bitLength n≤a'+m'-min (9+2*z+2^n) (a'+m'))
    (wFits:Cursor.Target.W k n≤a'+m'-min (9+2*z+2^n) (a'+m'))
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos N) (a'+m'-min (9+2*z+2^n) (a'+m')) n 12<
      tapeLength N (FixedRawLengthFence.allocation N))
    (hSmall:a'+m'+z+n+3<tapeLength N (FixedRawLengthFence.allocation N))
    (budget:FixedRawLengthFence.allocation N≤TotalIngressClosure.allocation k N)
    (same:(machine k).run pre (initialConfig (machine k) (allocation k N) y)=oldConfig k
      ((CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)))
    (oldAt:(CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)=
      CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig budget
        ((BodyIngress.machine k).run d' (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)))))
    (bodyDone:(BodyIngress.machine k).run d' (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)=
      ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x' w') (Cursor.Target.M k n z))),
        ⟨a'+m'+z+n+3,hSmall⟩,fun i=>SerializedBody.prepared
          (ready (table (FixedRawLengthFence.allocation N) x' w' z n) (a'+m'+z+2) n (FixedRawLengthFence.fencePos N)
            (a'+m'-min (9+2*z+2^n) (a'+m')) (n^k+k) (Cursor.Target.W k n))
          (a'+m') (Cursor.Target.M k n z) (FixedRawLengthFence.fencePos N)
          (a'+m'-min (9+2*z+2^n) (a'+m')) n (n^k+k) (Cursor.Target.W k n) i.val⟩) :
    Normal k N y pre := by
  let S:=a'+m';let R:=N;let F:=FixedRawLengthFence.fencePos R
  let r:=S-min (9+2*z+2^n) S
  let I:=ready (table (FixedRawLengthFence.allocation R) x' w' z n) (S+z+2) n F r (n^k+k) (Cursor.Target.W k n)
  have lay:Layout (allocation k N) N S z n r (n^k+k) (Cursor.Target.W k n) (Cursor.Target.M k n z)
      (9+2*z) (2^n) (Fin.append x' w') I:=by
    dsimp only [I,F,R,r,S]
    rw [←hN']
    exact normalLayout k x' w' gamma header capacity (by simpa only [hN'] using arena) physical ellFits wFits
  have room:S+z+2+n+1<tapeLength N (allocation k N):=by
    have bound:=layoutRoom lay
    change S+z+n+3 < tapeLength N (allocation k N) at bound
    omega
  have high:∀ i,tapeLength N (FixedRawLengthFence.allocation N) ≤ i →
      SerializedBody.prepared I S (Cursor.Target.M k n z) F r n (n^k+k) (Cursor.Target.W k n) i=none:=by
    dsimp only [I,F,R,r,S]
    rw [←hN']
    exact preparedHigh k x' w' gamma capacity (by simpa only [hN'] using arena) (by simpa only [hN'] using fit)
  have small:S+z+2+n+1<tapeLength N (FixedRawLengthFence.allocation N):=by omega
  have large:S+z+2+n+1<tapeLength N (TotalIngressClosure.allocation k N):=room
  have ext:=extendImage budget (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x' w') (Cursor.Target.M k n z))))
    (S+z+2+n+1) small large (SerializedBody.prepared I S (Cursor.Target.M k n z) F r n (n^k+k) (Cursor.Target.W k n)) high
  have headEq:a'+m'+z+n+3=S+z+2+n+1:=by omega
  have bodyDone':(BodyIngress.machine k).run d'
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)=
      ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x' w') (Cursor.Target.M k n z))),
        ⟨S+z+2+n+1,small⟩,fun i=>SerializedBody.prepared I S (Cursor.Target.M k n z) F r n (n^k+k) (Cursor.Target.W k n) i.val⟩:=
    bodyDone.trans (head_config _ _ _ _ _ _ headEq)
  refine ⟨a',m',x',w',hN',parsed',word',length',n,z,tag,gamma,header,physical,ellFits,wFits,capacity,arena,lay,room,?_⟩
  rw [same,oldAt,bodyDone',ext,nested_config]
private def Result (k N : Nat) (y : Bitstring N) (pre : Nat) : Prop :=
    let G:=CertificateGuardClosure.machine k;let oldC:=initialConfig G (allocation k N) y
    (((G.run pre oldC).state=G.reject ∧
      encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false) ∨
    (∃ b,(G.run pre oldC).state=CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))) ∨ Normal k N y pre)
private def BodyOutcome (k N : Nat) (y : Bitstring N) (a m : Nat) (x : Bitstring a) (w : Bitstring m) (d : Nat) : Prop :=
  let B0:=FixedRawLengthFence.allocation N;let O:=BodyIngress.machine k;let c0:=initialConfig O B0 y
(((O.run d c0).state=O.reject ∧
                PartAEndpoint.thresholdContentWitnessRelation k a m x w=false) ∨
             ∃ (n z : Nat) (hH:a+m+z+n+3 < tapeLength N B0),
              FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
              FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
              contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
              let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N
              let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
              let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
              let H:Fin (tapeLength N B0):=⟨S+z+n+3,hH⟩
              let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
              let V:=Stream.Target.image U S z n (9+2*z) Q Q false
              let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
              let Y:=RuntimeBitLength.Target.fullImage X L n F r
              let Z:=AllArityBitLength.Target.seedImage Y F r n
              let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
                F r n (n^k+k) (bitLength W) 0 0 W
              n < FixedRawLengthFence.capacity a m z ∧ H.val+Q < F ∧
              ((p < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
                  SerializedBody.delimiter F r n 12 < tapeLength N B0 ∧
                  (∀ i,address ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
                  O.run d c0=⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address)),H,
                    fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩) ∨
               (∃ positive : 0 < n, S ≤ address ∧
                  (∀ j:Fin W,padRead (Fin.append x w) (address+j.val)=false) ∧
                  (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=
                    some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
                  ((p=S ∧ O.run d c0=
                      ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                        Function.update (fun i=>V i.val) H (some false)⟩) ∨
                   (p < S ∧
                      ((r < bitLength n) ∨
                       (bitLength n ≤ r ∧ ∃ v2 v3 v4 v5 residual,
                          CappedWeight.Target.Cap k n r v2 v3 v4 v5 residual)) ∧
                      O.run d c0=
                        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                          Function.update (fun i=>Cursor.Target.image V k S n z F i.val) H (some false)⟩)))))
private def FrameOutcome (k N : Nat) (y : Bitstring N) (a m : Nat) (x : Bitstring a) (w : Bitstring m)
    (d n z : Nat) (hSmall:a+m+z+n+3<tapeLength N (FixedRawLengthFence.allocation N)) : Prop :=
  let B0:=FixedRawLengthFence.allocation N;let O:=BodyIngress.machine k;let c0:=initialConfig O B0 y
let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N
              let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
              let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
              let H:Fin (tapeLength N B0):=⟨S+z+n+3,hSmall⟩
              let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
              let V:=Stream.Target.image U S z n (9+2*z) Q Q false
              let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
              let Y:=RuntimeBitLength.Target.fullImage X L n F r
              let Z:=AllArityBitLength.Target.seedImage Y F r n
              let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
                F r n (n^k+k) (bitLength W) 0 0 W
              n < FixedRawLengthFence.capacity a m z ∧ H.val+Q < F ∧
              ((p < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
                  SerializedBody.delimiter F r n 12 < tapeLength N B0 ∧
                  (∀ i,address ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
                  O.run d c0=⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address)),H,
                    fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩) ∨
               (∃ positive : 0 < n, S ≤ address ∧
                  (∀ j:Fin W,padRead (Fin.append x w) (address+j.val)=false) ∧
                  (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=
                    some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
                  ((p=S ∧ O.run d c0=
                      ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                        Function.update (fun i=>V i.val) H (some false)⟩) ∨
                   (p < S ∧
                      ((r < bitLength n) ∨
                       (bitLength n ≤ r ∧ ∃ v2 v3 v4 v5 residual,
                          CappedWeight.Target.Cap k n r v2 v3 v4 v5 residual)) ∧
                      O.run d c0=
                        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                          Function.update (fun i=>Cursor.Target.image V k S n z F i.val) H (some false)⟩))))
private theorem framed_result (k N : Nat) (y : Bitstring N) (pre d' a' m' n z : Nat) (x' : Bitstring a') (w' : Bitstring m')
    (hN':pairLength a' m'=N) (parsed':decodePair y=some ((⟨a',x'⟩,⟨m',w'⟩):DecodedPair))
    (word':y=(hN' ▸ encodePair x' w')) (length':m'=a'+1)
    (budget:FixedRawLengthFence.allocation N≤TotalIngressClosure.allocation k N)
    (oldAt:(CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)=
      CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig budget
        ((BodyIngress.machine k).run d' (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)))))
    (same:(machine k).run pre (initialConfig (machine k) (allocation k N) y)=oldConfig k
      ((CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)))
    (hSmall:a'+m'+z+n+3<tapeLength N (FixedRawLengthFence.allocation N))
    (tag:FixedContentTagGate.tagMatches (Fin.append x' w')=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x' w')=some z)
    (header:contentHeader? (Fin.append x' w')=some (n,2*z+1))
    (frame:FrameOutcome k N y a' m' x' w' d' n z hSmall) : Result k N y pre := by
  let G:=CertificateGuardClosure.machine k
  let oldC:=initialConfig G (allocation k N) y
  rcases frame with ⟨capacity,arena,normalOrVirtual⟩
  rcases normalOrVirtual with ⟨physical,ellFits,wFits,fit,_source,bodyDone⟩|⟨_positive,_virtual,_zeros,_codec,bodyDone⟩
  · right;right
    exact normal_arrival k N pre d' a' m' n z y x' w' hN' parsed' word' length'
      tag gamma header capacity arena physical ellFits wFits fit hSmall budget same oldAt bodyDone
  · right;left
    refine ⟨false,?_⟩
    have states:=congrArg Config.state oldAt
    change (G.run pre oldC).state=CertificateGuardClosure.old k (TotalIngressClosure.old k _) at states
    rcases bodyDone with ⟨_eof,eq⟩|⟨_physical,_cap,eq⟩
    · rw [eq] at states
      exact states
    · rw [eq] at states
      exact states
private theorem guard_reject (k : Nat) : CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.machine k).reject)=
    (CertificateGuardClosure.machine k).reject := by
  apply Fin.ext
  dsimp only [CertificateGuardClosure.old,TotalIngressClosure.old,CertificateGuardClosure.machine,
    TotalIngressClosure.machine,UniformTM.seqRight,UniformTM.seq]
private theorem nested_state (k : Nat) {N C B : Nat} (h:C≤B)
    (c:Config (BodyIngress.machine k).stateCount N C) :
    (CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig h c))).state=
      CertificateGuardClosure.old k (TotalIngressClosure.old k c.state) := by
  dsimp only [CertificateGuardClosure.config,TotalIngressClosure.config,UniformTM.seqEmbedRight,
    IngressAllocation.extendConfig,CertificateGuardClosure.old,TotalIngressClosure.old]
private theorem mapped_reject (k : Nat) {N C B : Nat} (h:C≤B)
    (c:Config (BodyIngress.machine k).stateCount N C)
    (d:Config (CertificateGuardClosure.machine k).stateCount N B)
    (eq:d=CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig h c)))
    (reject:c.state=(BodyIngress.machine k).reject) : d.state=(CertificateGuardClosure.machine k).reject := by
  exact (congrArg Config.state eq).trans ((nested_state k h c).trans
    ((congrArg (fun q=>CertificateGuardClosure.old k (TotalIngressClosure.old k q)) reject).trans (guard_reject k)))
private theorem body_rejected (k N : Nat) (y : Bitstring N) (pre d' a' m' : Nat) (x' : Bitstring a') (w' : Bitstring m')
    (hN':pairLength a' m'=N) (parsed':decodePair y=some ((⟨a',x'⟩,⟨m',w'⟩):DecodedPair))
    (_word':y=(hN' ▸ encodePair x' w')) (_length':m'=a'+1)
    (budget:FixedRawLengthFence.allocation N≤TotalIngressClosure.allocation k N)
    (oldAt:(CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)=
      CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig budget
        ((BodyIngress.machine k).run d' (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)))))
    (_same:(machine k).run pre (initialConfig (machine k) (allocation k N) y)=oldConfig k
      ((CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)))
    (reject:((BodyIngress.machine k).run d' (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)).state=(BodyIngress.machine k).reject)
    (bad:PartAEndpoint.thresholdContentWitnessRelation k a' m' x' w'=false) : Result k N y pre := by
  left
  refine ⟨?_,relation_encoded k N a' m' y x' w' parsed' bad⟩
  exact mapped_reject k budget _ _ oldAt reject
private theorem body_result (k N : Nat) (y : Bitstring N) (pre d' a' m' : Nat) (x' : Bitstring a') (w' : Bitstring m')
    (hN':pairLength a' m'=N) (parsed':decodePair y=some ((⟨a',x'⟩,⟨m',w'⟩):DecodedPair))
    (word':y=(hN' ▸ encodePair x' w')) (length':m'=a'+1)
    (budget:FixedRawLengthFence.allocation N≤TotalIngressClosure.allocation k N)
    (oldAt:(CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)=
      CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig budget
        ((BodyIngress.machine k).run d' (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)))))
    (same:(machine k).run pre (initialConfig (machine k) (allocation k N) y)=oldConfig k
      ((CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)))
    (body:BodyOutcome k N y a' m' x' w' d') : Result k N y pre := by
  let G:=CertificateGuardClosure.machine k
  let oldC:=initialConfig G (allocation k N) y
  rcases body with ⟨reject,bad⟩|⟨n,z,hSmall,tag,gamma,header,framed⟩
  · exact body_rejected k N y pre d' a' m' x' w' hN' parsed' word' length' budget oldAt same reject bad
  · exact framed_result k N y pre d' a' m' n z x' w' hN' parsed' word' length' budget oldAt same hSmall tag gamma header framed
private theorem frontier_result (k N : Nat) (y : Bitstring N) (pre d : Nat)
    (canonical:∀ (a m : Nat) (x : Bitstring a) (w : Bitstring m),
      decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) → m=a+1)
    (same:(machine k).run pre (initialConfig (machine k) (allocation k N) y)=oldConfig k
      ((CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)))
    (done:(CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y)=
      CertificateGuardClosure.config k ((TotalIngressClosure.machine k).run d
        (initialConfig (TotalIngressClosure.machine k) (allocation k N) y)))
    (frontier:CertificateGuardClosure.Target.Frontier k N y d) : Result k N y pre := by
  let G:=CertificateGuardClosure.machine k
  let oldC:=initialConfig G (allocation k N) y
  rcases frontier with ⟨_price,_heads,_safe,_first,branch⟩
  rcases branch with ⟨_bad,_clock,malformed,bad⟩|⟨a',m',x',w',hN',parsed',word',d',_clock,_suffix,budget,_extension,_footprint,_move,_trace,oldDone,body⟩
  · left
    refine ⟨?_,bad⟩
    exact congrArg Config.state (done.trans (congrArg (CertificateGuardClosure.config k) malformed))
  · have length':m'=a'+1:=canonical a' m' x' w' parsed'
    have oldAt:G.run pre oldC=CertificateGuardClosure.config k (TotalIngressClosure.config k
        (IngressAllocation.extendConfig budget ((BodyIngress.machine k).run d'
          (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation N) y)))):=
      done.trans (congrArg (CertificateGuardClosure.config k) oldDone)
    exact body_result k N y pre d' a' m' x' w' hN' parsed' word' length' budget oldAt same body
private theorem ingress_result (k N : Nat) (y : Bitstring N) (pre : Nat)
    (front:Target.Prelude k N y pre)
    (same:(machine k).run pre (initialConfig (machine k) (allocation k N) y)=oldConfig k
      ((CertificateGuardClosure.machine k).run pre (initialConfig (CertificateGuardClosure.machine k) (allocation k N) y))) :
    Result k N y pre := by
  rcases front with ⟨_price,_heads,_safe,_first,outcome⟩
  rcases outcome with ⟨_malformed,_time,done,bad⟩|⟨a,m,x,w,_hN,parsed,_word,_length,_price,done,bad⟩|
    ⟨a,m,x,w,_hN,parsed,_word,length,_g,d,_time,_price,_low,_entry,_suffix,frontier,done⟩
  · exact Or.inl ⟨congrArg Config.state done,bad⟩
  · exact Or.inl ⟨congrArg Config.state done,relation_encoded k N a m y x w parsed bad⟩
  · exact frontier_result k N y pre d (fun a' m' x' w' p=>canonical_pair parsed p length) same done frontier
end RawCallerClosure
