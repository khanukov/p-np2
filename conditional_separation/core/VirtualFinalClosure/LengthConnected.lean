import VirtualFinalClosure.LengthCut
import VirtualFinalClosure.LengthMarker
import VirtualFinalClosure.PathTrace
import VirtualFinalClosure.CapMeaning
namespace VirtualFinalClosure.LengthConnected
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LengthCut","VirtualFinalClosure.LengthCut","raw_length_cut","rawCut",(1:Nat)),
      ("VirtualFinalClosure.LengthMarker","VirtualFinalClosure.LengthMarker","length_marker","marker",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","length_shortage","lengthShortage",1),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","virtual_address","virtualAddress",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.LengthCut","VirtualFinalClosure.LengthCut","extended_state","extendedState",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","guarded_old","guardedOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","total_old","totalOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","body_old","bodyOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","carry_old","carryOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","virtual_old","virtualOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","sequential","sequentialState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","sequential","sequentialConfig",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong raw-origin source marker term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique raw-origin source marker term {mod}/{key}"
private theorem native_price (R n r delta d : Nat) (hn : n≤R) (hr : r≤R)
    (hd : delta≤3*R+2)
    (price : d≤n+r+7+r*(2*r+2*delta+14)+delta+r+7) : d≤64*(R+1)^2 := by
  have product : r*(2*r+2*delta+14)≤R*(8*R+18) :=
    Nat.mul_le_mul hr (by omega)
  nlinarith only [price,product,hn,hr,hd,Nat.zero_le R,Nat.zero_le (R^2)]
private theorem combined_price (R g t d : Nat)
    (hg : g≤128*(R+1)^2) (ht : t≤4194304*(R+1)^3) (hd : d≤64*(R+1)^2) :
    g+t+d≤8388608*(R+1)^3 := by
  nlinarith only [hg,ht,hd,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
private theorem cut_image (k R C B i head : Nat) (f : Fin 4) (Y : Nat → Option Bool)
    (budget : C≤B) (fit : head < tapeLength R C) (bound : i < Cursor.stateCount k) :
    config k ⟨8+f.val,by have h:=f.isLt;omega⟩
      (CertificateGuardClosure.config k (TotalIngressClosure.config k
        (IngressAllocation.extendConfig budget
          (BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k
            (SmallIngress.producer.seqEmbedRight (Cursor.machine k) ⟨Cursor.q k i,⟨head,fit⟩,fun j=>Y j.val⟩)))))))=
      (⟨control k (tableControl k i) ⟨8+f.val,by have h:=f.isLt;omega⟩,
        ⟨head,lt_of_lt_of_le fit (by simp only [tapeLength];omega)⟩,
        fun j=>masked Y (tapeLength R C) j.val⟩ : Config (machine k).stateCount R B) := by
  apply Config.ext_parts
  · apply congrArg (fun q=>control k q ⟨8+f.val,by have h:=f.isLt;omega⟩)
    rw [extendedState]
    apply Fin.ext
    rw [guardedOld,totalOld,bodyOld,carryOld,virtualOld,sequentialConfig,tableValue k i bound]
    change 77+(10+(288+i%Cursor.stateCount k))=375+i
    rw [Nat.mod_eq_of_lt bound]
    omega
  · exact Fin.ext rfl
  · funext j
    change (if hi:j.val < tapeLength R C then Y j.val else none)=masked Y (tapeLength R C) j.val
    dsimp only [masked]
    split_ifs <;> rfl
/-- A connected actual RAW branch consumes every physical suffix cell into the
native finite-mode guard. This is the bitLength-overflow classification branch
of the larger unconditional Target.Raw proof, not a replacement for that goal. -/
private theorem raw_marked_length (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n≤FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (shortage : a+m-min (9+2*z+2^n) (a+m) < bitLength n) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let P:=F+5*r+n+7
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C);let bits:=fun j=>(T (S-1-j)).getD false
    let c:=initialConfig (machine k) B (encodePair x w)
    S < Cursor.Target.M k n z ∧
    ∃ (g t d : Nat) (f : Fin 4) (hp : S-r < tapeLength R B),
      g≤128*(R+1)^2 ∧ t≤4194304*(R+1)^3 ∧
      d≤n+r+7+r*(2*r+2*(F-S)+14)+(F-S)+r+7 ∧
      g+t+d≤8388608*(R+1)^3 ∧
      (∀ u,u≤g+t+d → ((machine k).run u c).head.val≤12*(R+1)^2) ∧
      (machine k).run (g+t+d) c=
        ⟨nc k 40 (modes (8+f.val) bits r),⟨S-r,hp⟩,fun j=>image T F r S r j.val⟩ ∧
      (∀ u,u≤d → ((machine k).run (g+t+u) c).head.val≤P) ∧
      sourceMode (modes (8+f.val) bits r)=(if bits (r-1) then 1 else 0) ∧
      (seen (modes (8+f.val) bits r)=0 ↔ ∀ j,j < r → bits j=false) := by
  intro S R C B L F r P U V Y T bits c
  have inside : 9+2*z+2^n < S := by omega
  have rEq : r=S-(9+2*z+2^n) := by dsimp only [r];rw [Nat.min_eq_left inside.le]
  have wShort : S-(9+2*z+2^n) < Cursor.Target.W k n := by
    rw [←rEq]
    exact lengthShortage k n r shortage
  refine ⟨virtualAddress k n z S inside wShort,?_⟩
  obtain ⟨g,t,h,f,gPrice,tPrice,prefixHeads,_safe,_prefix,arrival⟩:=rawCut k x w canonical header tag gamma firstPhysical cap rows physical shortage
  have qbound : (if (r+1)%2=1 then 250 else 304) < Cursor.stateCount k := by
    split <;> unfold Cursor.stateCount <;> omega
  have start:=arrival.trans (cut_image k R C B _ _ f Y (smallBudget k R) h qbound)
  obtain ⟨d,price,path,mode,zero⟩:=marker k x w gamma cap rows physical f
  obtain ⟨_blank,oldFit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  have fit : P < tapeLength R B := by
    have small:P < tapeLength R C:=oldFit
    have grow:=smallBudget k R
    simp only [tapeLength] at small ⊢
    omega
  have run:=execute (N:=R) (B:=B) path fit
  have heads:=through (N:=R) (B:=B) path fit
  have pair : S≤R := by dsimp only [S,R,pairLength];omega
  have nr : n≤R := actualWidth R S z n pair physical
  have rr : r≤R := (Nat.sub_le _ _).trans pair
  have priceSmall : d≤64*(R+1)^2 := native_price R n r (F-S) d nr rr (by dsimp only [F];omega) price
  have envelope : P≤12*(R+1)^2 := by
    dsimp only [P,F]
    nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨g,t,d,f,by dsimp only [F,P] at fit;omega,gPrice,tPrice,price,
    combined_price R g t d gPrice tPrice priceSmall,?_,?_,?_,mode,zero⟩
  · intro u hu
    by_cases early : u≤g+t
    · exact prefixHeads u early
    · rw [show u=(g+t)+(u-(g+t)) by omega,UniformTM.run_add,start]
      exact (heads (u-(g+t)) (by omega)).trans envelope
  · rw [UniformTM.run_add,start]
    exact run
  · intro u hu
    rw [UniformTM.run_add,start]
    exact heads u hu
#print axioms native_price
#print axioms combined_price
#print axioms cut_image
#print axioms raw_marked_length
end VirtualFinalClosure.LengthConnected
