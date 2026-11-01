import VirtualFinalClosure.RawFlaggedCap
import VirtualFinalClosure.RawSourceFrame
import VirtualFinalClosure.TightCapPrices
import VirtualFinalClosure.InitialCapGrow
import VirtualFinalClosure.TightGrowth
import VirtualFinalClosure.GrownTail
import VirtualFinalClosure.WeightResources
import VirtualFinalClosure.CapImageFrame
import VirtualFinalClosure.WeightMarker
import VirtualFinalClosure.LengthConnected
namespace VirtualFinalClosure.RawCapGrow
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawFlaggedCap","VirtualFinalClosure.RawFlaggedCap","raw_cap","rawCap",(1:Nat)),
      ("VirtualFinalClosure.InitialCapGrow","VirtualFinalClosure.InitialCapGrow","prepared","growCap",1),
      ("VirtualFinalClosure.InitialWeightFrame","VirtualFinalClosure.InitialWeightFrame","actual","initialFrame",1),
      ("VirtualFinalClosure.RawSourceFrame","VirtualFinalClosure.RawSourceFrame","marked_source","rawSource",1),
      ("VirtualFinalClosure.RawLengthGrow","VirtualFinalClosure.RawLengthGrow","phase_price","growPrice",1),
      ("VirtualFinalClosure.TightGrowth","VirtualFinalClosure.TightGrowth","prepared","tightDriver",1),
      ("VirtualFinalClosure.TightCapPrices","VirtualFinalClosure.TightCapPrices","initial_price","prefixPrice",1),
      ("VirtualFinalClosure.TightCapPrices","VirtualFinalClosure.TightCapPrices","total","totalPrice",1),
      ("VirtualFinalClosure.TightCapPrices","VirtualFinalClosure.TightCapPrices","prefix_space","prefixSpace",1),
      ("VirtualFinalClosure.GrownFrame","VirtualFinalClosure.GrownFrame","actual","grownFrame",1),
      ("VirtualFinalClosure.GrownTail","VirtualFinalClosure.GrownTail","actual","grownTail",1),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","room","weightRoom",1),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","heads","weightHeads",1),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","cap_shortage","capShortage",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_gap","actualGap",1),
      ("VirtualFinalClosure.GrowEntry","VirtualFinalClosure.GrowEntry","reentry_phase","reentryPhase",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_bound","modeBound",1),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong original raw W-cap connection {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique original raw W-cap connection {mod}/{key}"
private theorem counts (S z n : Nat) (physical : min (9+2*z+2^n) S < S) :
    9+2*z+2^n < S ∧ S-(S-min (9+2*z+2^n) S)=9+2*z+2^n ∧
      S-min (9+2*z+2^n) S < S:=by
  have below : 9+2*z+2^n < S:=by omega
  rw [Nat.min_eq_left below.le]
  have positive:=Nat.two_pow_pos n
  exact ⟨below,Nat.sub_sub_self below.le,Nat.sub_lt (by omega) (by omega)⟩
/-- Same raw paid flag through ALL four original W-cap residuals, the real
seen1 reset/doubling and the ENTIRE tight W/bitLengthW driver. Normal W remains
unconsumed; seen0 remains a separate actual source condition, never a reject. -/
private theorem raw_grow (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
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
             ⟨nc k 40 (modes (8+f.val) bits r),⟨S-r,hp⟩,fun i=>marked I F r S r i.val⟩ ∧
           (∀ q,q ≤ t+a0+b0+d → ((machine k).run q c).head.val ≤ 256*(R+1)^2) ∧
           ((∀ j,j < r → bits j=false) ∨
            ∃ (s width : Nat) (h0 : F+1 < tapeLength R B),
              let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
              let md : Fin 144:=⟨changeMeta 4 (modes (8+f.val) bits r),metaBound 4 _⟩
              r ≤ width ∧ 0 < width ∧ Cursor.Target.W k n ≤ width ∧ width ≤ 2*Cursor.Target.W k n ∧
              s ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4) ∧
              (machine k).run s c=⟨control k (tableControl k (613+93*k)) md,⟨F+1,h0⟩,
                fun i=>residual G L n F width (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩ ∧
              (∀ u,u ≤ s → ((machine k).run u c).head.val ≤ spaceBound k R))) := by
  intro S R C B L F r U V Y T Z c
  obtain ⟨t,a0,b0,f,tp,ap,bp,meaning,outcome⟩:=rawCap k x w canonical header tag gamma firstPhysical cap rows physical fits
  refine ⟨t,a0,b0,f,tp,ap,bp,meaning,?_⟩
  rcases outcome with normal|⟨v2,v3,v4,v5,d0,data,virtual,d,hp,dp,marker,oldHeads,_mode,zeroTest⟩
  · exact Or.inl normal
  · right
    let I:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
    let bits:=fun j=>(I (S-1-j)).getD false
    refine ⟨v2,v3,v4,v5,d0,data,virtual,d,hp,dp,marker,oldHeads,?_⟩
    by_cases noTrue : seen (modes (8+f.val) bits r)=0
    · exact Or.inl (zeroTest.mp noTrue)
    · right
      let m0:=modes (8+f.val) bits r
      let md : Fin 144:=⟨changeMeta 4 m0,metaBound 4 _⟩
      let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
      let P:=F+5*r+n+7
      have observed : seen m0=1:=by dsimp only [seen] at noTrue ⊢;omega
      have hm : m0 < 144:=modeBound _ _ _ (by have h:=f.isLt;omega)
      obtain ⟨frT,rp,oldFit,blank,cells,_empty,_power⟩:=initialFrame x w gamma cap rows physical fits
      obtain ⟨source,_hole,_suffix⟩:=rawSource x w gamma cap physical
      have sr : S ≤ R:=by dsimp only [S,R,pairLength];omega
      have nr : n ≤ R:=actualWidth R S z n sr physical
      have rr : r ≤ R:=(Nat.sub_le _ _).trans sr
      obtain ⟨inside,pe,rs⟩:=counts S z n physical
      change S-r=9+2*z+2^n at pe
      change r < S at rs
      have finite : P < tapeLength R B:=by
        have grow:=smallBudget k R
        change P < tapeLength R C at oldFit
        dsimp only [tapeLength] at oldFit ⊢
        omega
      have gap : L+n+1+2^n+1 < F:=by
        have actual:=actualGap R S z n sr physical
        change S+z+n+3+2^n+1 < F at actual
        have same : L+n+1+2^n+1=S+z+n+3+2^n+1:=by dsimp only [L];omega
        rw [same];exact actual
      obtain ⟨e,ep,path⟩:=growCap k P m0 S L n (2^n) F r v2 v3 v4 v5 d0 T hm observed frT gap rp
        rs le_rfl blank cells
        (by intro i lo hi
            have lower : 9+2*z ≤ i:=(Nat.le_add_right (9+2*z) (2^n)).trans (pe ▸ lo.le)
            exact ⟨_,source i lower hi⟩)
      have epSmall : e ≤ 128*(R+1)^2:=growPrice R F S (S-r) r n e nr rr rfl ep
      have hS : S < tapeLength R B:=by
        have lo : R ≤ P:=by dsimp only [P,F];omega
        exact (sr.trans lo).trans_lt finite
      have at98 : (machine k).run (t+a0+b0+d+e) c=
          ⟨control k (tableControl k 98) md,⟨S,hS⟩,
            fun i=>G i.val⟩:=by
        rw [UniformTM.run_add,marker]
        exact execute path finite
      obtain ⟨fr,reg,assn,_bank,_fresh,_fit⟩:=grownFrame x w gamma cap rows physical
      obtain ⟨_allTail,identity⟩:=grownTail x w gamma cap rows physical
      have short:=capShortage k n r v2 v3 v4 v5 d0 data
      have room : F+10*Cursor.Target.W k n+n+7 < tapeLength R B:=
        lt_of_le_of_lt (by dsimp only [F];omega) (weightRoom k R n nr)
      obtain ⟨aa,bb,u,j0,C0,j1,C1,h0,form0,_ellFits,_limit0,form1,weightFits,limit1,aPrice,bPrice,uPrice,done,heads⟩:=
        tightDriver k R B S L n (2^n) F (2*r) G md (reentryPhase _) (by omega) (by omega) fr reg assn room
      rw [identity] at done heads
      have lower0 : 2*r ≤ C0:=by rw [form0];have pow:=Nat.two_pow_pos j0;nlinarith only [pow,Nat.zero_le r]
      have lower1 : C0 ≤ C1:=by rw [form1];have pow:=Nat.two_pow_pos j1;nlinarith only [pow,Nat.zero_le C0]
      have price0 : t+a0+b0+d+e ≤ 268435456*(k+1)*(R+1)^3:=prefixPrice k R n r t a0 b0 d e nr rr tp ap bp dp epSmall
      have price : t+a0+b0+d+e+aa+bb+u ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4):=
        totalPrice k R n (2*r) C0 C1 (t+a0+b0+d+e) aa bb u nr price0 limit1 aPrice bPrice uPrice
      have sourceL : L ≤ 2*R+2:=by dsimp only [L];omega
      have smallP : P ≤ 256*(R+1)^2:=by
        dsimp only [P,F]
        nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
      refine ⟨t+a0+b0+d+e+aa+bb+u,C1,h0,by omega,by omega,weightFits,limit1,price,?_,?_⟩
      · rw [show t+a0+b0+d+e+aa+bb+u=(t+a0+b0+d+e)+(aa+bb+u) by omega,UniformTM.run_add,at98]
        exact done
      · intro v hv
        by_cases early : v ≤ t+a0+b0+d
        · exact (oldHeads v early).trans (prefixSpace k R)
        · by_cases middle : v ≤ t+a0+b0+d+e
          · rw [show v=(t+a0+b0+d)+(v-(t+a0+b0+d)) by omega,UniformTM.run_add,marker]
            exact ((through path finite (v-(t+a0+b0+d)) (by omega)).trans smallP).trans (prefixSpace k R)
          · rw [show v=(t+a0+b0+d+e)+(v-(t+a0+b0+d+e)) by omega,UniformTM.run_add,at98]
            apply weightHeads k R n L _ nr sourceL
            exact (heads (v-(t+a0+b0+d+e)) (by omega)).trans (by omega)
#print axioms counts
#print axioms raw_grow
end VirtualFinalClosure.RawCapGrow
