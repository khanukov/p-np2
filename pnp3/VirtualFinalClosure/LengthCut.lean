import VirtualFinalClosure.LengthPrefix
import VirtualFinalClosure.HeadFields
namespace VirtualFinalClosure.LengthCut
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawLengthLift","VirtualFinalClosure.RawLengthLift","raw_length_body","rawLength",(1:Nat)),
      ("VirtualFinalClosure.PairPrefix","VirtualFinalClosure.PairPrefix","raw_entry","pairPrefix",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_room","smallRoom",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","extend_body","extendBody",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","low_prefix_safe","oldPrefixSafe",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","low_safe","lowSafe",1),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",0),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","every_prefix","everyPrefix",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","lift","liftPrefix",0),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","guarded","guardedState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","total","totalState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","extension","extensionState",1),
      ("VirtualFinalClosure.RawLengthLift","VirtualFinalClosure.RawLengthLift","embed_state","embedState",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","guarded_old","guardedOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","total_old","totalOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","body_old","bodyOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","carry_old","carryOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","virtual_old","virtualOld",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","guarded","guardedHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","total","totalHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","extension","extensionHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","included","includedHead",1)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong concrete raw bitLength cut term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique concrete raw bitLength cut term {mod}/{key}"
private theorem lifted_head (k : Nat) {N B : Nat} (f : Fin 4)
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) :
    (liftPrefix k f c).head.val=c.head.val := by dsimp only [liftPrefix,config]
private theorem extended_state (k : Nat) {N C B : Nat} (h : C≤B)
    (c : Config (AllArityCursor.machine k).stateCount N C) :
    (CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig h
      (BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k c)))))).state=
      CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.old k
        (CarryWindow.embed k (VirtualLeaf.embed k c.state)))) := by
  apply Fin.ext
  rw [guardedState,totalState,extensionState,embedState,guardedOld,totalOld,bodyOld,carryOld,virtualOld]
/-- A physical all-arity raw branch through BOTH real pair-parser runs and the
exact certificate guard, with FIRST live bitLength-cap interception. Header and
resource premises are explicit local classification hypotheses, not new Raw
caller premises and not a conclusion that the full virtual verifier is closed. -/
private theorem raw_length_cut (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n≤FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (shortage : a+m-min (9+2*z+2^n) (a+m) < bitLength n) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let y:=encodePair x w;let c:=initialConfig (machine k) B y
    let old:=initialConfig (CertificateGuardClosure.machine k) B y
    ∃ (g t : Nat) (h : F+r+n+3 < tapeLength R C) (f : Fin 4),
      g≤128*(R+1)^2 ∧ t≤4194304*(R+1)^3 ∧
      (∀ u,u≤g+t → ((machine k).run u c).head.val≤12*(R+1)^2) ∧
      (∀ u,u < g+t → ¬Intercept k ((CertificateGuardClosure.machine k).run u old).state
        (((CertificateGuardClosure.machine k).run u old).tape ((CertificateGuardClosure.machine k).run u old).head)) ∧
      (∀ u,u≤g+t → ∃ flag : Fin 4,(machine k).run u c=
        config k ⟨8+flag.val,by have h:=flag.isLt;omega⟩ ((CertificateGuardClosure.machine k).run u old)) ∧
      (machine k).run (g+t) c=config k ⟨8+f.val,by have h:=f.isLt;omega⟩
        (CertificateGuardClosure.config k (TotalIngressClosure.config k
          (IngressAllocation.extendConfig (smallBudget k R)
            (BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k
              (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,h⟩,fun i=>Y i.val⟩))))))) := by
  intro S R C B L F r U V Y y c old
  obtain ⟨t,h,tPrice,atLength,bodyEvery,bodyHeads,avoid,before⟩:=
    rawLength k x w header tag gamma firstPhysical cap rows physical
  have fits : ¬bitLength n≤r := by omega
  have fitsExpanded : ¬bitLength n≤a+m-min (9+2*z+2^n) (a+m) := fits
  have hd : F+r+n+3 < tapeLength R C := by simpa only [if_neg fitsExpanded] using h
  have done : (BodyIngress.machine k).run t (initialConfig (BodyIngress.machine k) C y)=
      BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k
        (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,hd⟩,fun i=>Y i.val⟩))) := by
    simpa only [if_neg fitsExpanded] using atLength
  have bodyLarge:=extendBody k R t y bodyHeads
  have budget : C≤B := smallBudget k R
  have room : 2*R+3 < tapeLength R B := by
    have small : 2*R+3 < tapeLength R C := by
      dsimp only [tapeLength,FixedRawLengthFence.allocation,C]
      nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    simp only [tapeLength] at small ⊢
    omega
  have parserRoom : FixedPairParser.clock R≤B := by
    have small : FixedPairParser.clock R≤C := by
      change 2*R+1≤16*(R+1)^2
      nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    exact small.trans budget
  obtain ⟨g,gPrice,low,parserHeads,rawBody⟩:=pairPrefix k B x w canonical room parserRoom
  have safe : ∀ u,u < g+t → ¬Intercept k ((CertificateGuardClosure.machine k).run u old).state
      (((CertificateGuardClosure.machine k).run u old).tape ((CertificateGuardClosure.machine k).run u old).head) := by
    intro u hu
    by_cases early : u < g
    · exact lowSafe k _ _ ((low u early).trans (by decide))
    · rw [show u=g+(u-g) by omega,rawBody,bodyLarge (u-g) (by omega),bodyEvery (u-g) (by omega)]
      have av:=avoid (u-g) (by omega)
      rw [extended_state]
      have rawLow : ((AllArityCursor.machine k).run (u-g)
          (initialConfig (AllArityCursor.machine k) C y)).state.val≤617 := by
        have bound:=before (u-g) (by omega)
        rw [bodyEvery (u-g) (by omega),embedState] at bound
        exact bound
      exact oldPrefixSafe k _ rawLow av.1 av.2.1 _
  have every := everyPrefix k B y (g+t) safe
  obtain ⟨f,arrival⟩:=every (g+t) le_rfl
  have oldHeads (u : Nat) (hu : u≤g+t) :
      ((CertificateGuardClosure.machine k).run u old).head.val≤12*(R+1)^2 := by
    by_cases early : u≤g
    · exact parserHeads u early
    · rw [show u=g+(u-g) by omega,rawBody,bodyLarge (u-g) (by omega),guardedHead,totalHead,extensionHead]
      exact bodyHeads (u-g) (by omega)
  have heads (u : Nat) (hu : u≤g+t) : ((machine k).run u c).head.val≤12*(R+1)^2 := by
    obtain ⟨flag,eq⟩:=every u hu
    rw [eq,lifted_head]
    exact oldHeads u hu
  refine ⟨g,t,hd,f,gPrice,tPrice,heads,safe,every,?_⟩
  change (machine k).run (g+t) c=config k _ ((CertificateGuardClosure.machine k).run (g+t) old) at arrival
  rw [rawBody t,bodyLarge t le_rfl,done] at arrival
  exact arrival
#print axioms lifted_head
#print axioms extended_state
#print axioms raw_length_cut
end VirtualFinalClosure.LengthCut
