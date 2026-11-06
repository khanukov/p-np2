import VirtualFinalClosure.RawFlaggedWeight
import VirtualFinalClosure.CapImageFrame
import VirtualFinalClosure.WeightMarker
import VirtualFinalClosure.LengthConnected
namespace VirtualFinalClosure.RawFlaggedCap
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.RawFlaggedWeight","VirtualFinalClosure.RawFlaggedWeight","raw_weight","rawWeight",1),
      ("VirtualFinalClosure.CapImageFrame","VirtualFinalClosure.CapImageFrame","actual","capFrame",1),
      ("VirtualFinalClosure.WeightMarker","VirtualFinalClosure.WeightMarker","prepared","markCap",1),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","cap_shortage","capShortage",1),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","virtual_address","virtualAddress",1),
      ("VirtualFinalClosure.LengthConnected","VirtualFinalClosure.LengthConnected","native_price","markerPrice",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","physical","physicalValue",1),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","actual_length_frame","lengthFrame",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","bits","tableBits",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong original raw W-cap connection {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique original raw W-cap connection {mod}/{key}"
private theorem phase_head_bound (R S z n r h : Nat) (nr : n ≤ R) (rr : r ≤ R) (sr : S ≤ R)
    (inside : 9+2*z+2^n < S) (bound : h ≤ (S+z+2)+16*(3*R+2+5*r+n+8)) :
    h ≤ 256*(R+1)^2:=by
  have positive:=Nat.two_pow_pos n
  have zz : z ≤ R:=by omega
  nlinarith only [bound,nr,rr,sr,zz,Nat.zero_le R,Nat.zero_le (R^2)]
/-- The physically PAID n-bitLength-FITS raw branch with the actual computed flag. ALL four first W-caps
enter the ACTUAL source marker before any cleanup, on their exact dirty tapes.
Normal W arrival remains unconsumed. No cap or W-fit is a caller premise. -/
private theorem raw_cap (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (fits : bitLength n ≤ a+m-min (9+2*z+2^n) (a+m)) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C);let Z:=AllArityBitLength.Target.seedImage T F r n
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (t a0 b0 : Nat) (f : Fin 4),
      t ≤ 4194304*(R+1)^3 ∧
      a0 ≤ 16*(F+5*r+n+8) ∧ b0 ≤ 2097152*(k+1)*(n+r+1)^2*(F+5*r+n+9) ∧
      (f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0) ∧
      ((Cursor.Target.W k n ≤ r ∧ ∃ hD : F+r+n+3 < tapeLength R B,
        (machine k).run (t+a0+b0) c=
          ⟨control k (tableControl k (430+93*k)) ⟨8+f.val,by have h:=f.isLt;omega⟩,⟨F+r+n+3,hD⟩,
            fun i=>CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩) ∨
       ∃ v2 v3 v4 v5 d0,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d0 ∧ S < Cursor.Target.M k n z ∧
         let I:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
         let bits:=fun j=>(I (S-1-j)).getD false
         ∃ (d : Nat) (hp : S-r < tapeLength R B),d ≤ 64*(R+1)^2 ∧
           (machine k).run (t+a0+b0+d) c=
             ⟨nc k 40 (modes (8+f.val) bits r),⟨S-r,hp⟩,fun i=>image I F r S r i.val⟩ ∧
           (∀ q,q ≤ t+a0+b0+d → ((machine k).run q c).head.val ≤ 256*(R+1)^2) ∧
           sourceMode (modes (8+f.val) bits r)=(if bits (r-1) then 1 else 0) ∧
           (seen (modes (8+f.val) bits r)=0 ↔ ∀ j,j < r → bits j=false)) := by
  intro S R C B L F r U V Y T Z c
  let f:=folded (tableBits U (min (9+2*z) S) S) (2^n)
  obtain ⟨t,a0,b0,_hL,tp,ap,bp,_at308,oldHeads,phaseHeads,meaning,outcome⟩:=
    rawWeight k x w canonical header tag gamma firstPhysical cap rows physical fits
  refine ⟨t,a0,b0,f,tp,ap,bp,meaning,?_⟩
  rcases outcome with normal|⟨v2,v3,v4,v5,d0,capData,hD,atCap⟩
  · exact Or.inl normal
  · right
    let I:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
    let bits:=fun j=>(I (S-1-j)).getD false
    let P:=F+5*r+n+7
    obtain ⟨fr,gap,pos,short,oldFit,bank,last,sameSource⟩:=capFrame x w gamma cap rows physical fits v2 v3 v4 v5 d0
    have shortage:=capShortage k n r v2 v3 v4 v5 d0 capData
    have inside:=physicalValue S z n physical
    have rEq : r=S-(9+2*z+2^n):=by dsimp only [r];rw [Nat.min_eq_left inside.le]
    have virtual : S < Cursor.Target.M k n z:=virtualAddress k n z S inside (by rwa [←rEq])
    have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
    have nr : n ≤ R:=actualWidth R S z n pair physical
    have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
    have smallS : S ≤ P:=by dsimp only [P,F];omega
    obtain ⟨_fr,_gap,_pos,_short,_bank,_last,cells⟩:=lengthFrame x w gamma cap rows physical
    have selected (i : Nat) (hi : i < r) : I (S-1-i)=some (bits i):=by
      obtain ⟨v,cell⟩:=cells i hi
      have im : I (S-1-i)=some v:= (sameSource i hi).trans
        ((maskedLow Y (tapeLength R C) _ (lt_of_le_of_lt (by omega) oldFit)).trans cell)
      change I (S-1-i)=some ((I (S-1-i)).getD false)
      rw [im];rfl
    obtain ⟨d,dp,path,mode,zero⟩:=markCap k P S L n (2^n) F r f I bits fr gap pos short (by dsimp only [P];omega) bank last selected
    have price : d ≤ 64*(R+1)^2:=markerPrice R n r (F-S) d nr rr (by dsimp only [F];omega) (by omega)
    have finite : P < tapeLength R B:=by
      have mono:=smallBudget k R
      change F+5*r+n+7 < tapeLength R C at oldFit
      dsimp only [tapeLength] at oldFit ⊢
      omega
    refine ⟨v2,v3,v4,v5,d0,capData,virtual,d,by dsimp only [P] at finite;omega,price,?_,?_,mode,zero⟩
    · rw [UniformTM.run_add,atCap]
      exact execute path finite
    · intro q hq
      by_cases early : q ≤ t
      · exact (oldHeads q early).trans (Nat.mul_le_mul_right _ (by decide : 12 ≤ 256))
      · by_cases middle : q ≤ t+a0+b0
        · have same : q=t+(q-(t)):=by omega
          rw [same]
          have bound:=phaseHeads (q-(t)) (by omega)
          exact phase_head_bound R S z n r _ nr rr pair inside bound
        · rw [show q=(t+a0+b0)+(q-(t+a0+b0)) by omega,UniformTM.run_add,atCap]
          have bound:=through path finite (q-(t+a0+b0)) (by omega)
          have envelope : P ≤ 256*(R+1)^2:=by dsimp only [P,F];nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
          exact bound.trans envelope
#print axioms phase_head_bound
#print axioms raw_cap
end VirtualFinalClosure.RawFlaggedCap
