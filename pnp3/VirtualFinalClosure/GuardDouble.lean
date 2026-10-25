import VirtualFinalClosure.GuardTransfer
import VirtualFinalClosure.GuardCross
namespace VirtualFinalClosure.GuardDouble
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("PostWeight.Kernel","PostWeight","Banks","Banks",(2:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",(0:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","digit","digit",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","occupied","occupied",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","take3","take3",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","take5","take5",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","add4","add4",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","add3","add3",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","doubleDec3","dec3",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","doubleQuota","quota",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","doubleInc4a","inc4a",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","doubleInc4b","inc4b",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","doubleQuotaRoute","toQuota",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","doubleTo4","to4",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","doubleBack3","back3",(1:Nat)),
      ("VirtualFinalClosure.GuardTransfer","VirtualFinalClosure.GuardTransfer","prepared","transfer",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","put","put",(0:Nat)),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",(0:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong literal BE transfer interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal BE transfer interface {mod}/{key}"
private theorem sub_step (i a : Nat) (h : a < i) : i-(a+1)+2=i-a+1 := by omega
/-- Real decrement/copy/double loop. Quota exhaustion is a genuine live
abortD5 with its exact residual, and proves that the doubled prefix exceeds W.
Every successful increment is justified by the consumed physical quota. -/
private theorem loop (k P m L n F width ell i W a : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Banks T L n F width) (fit : F+5*width+n+7 ≤ P)
    (_ic : i ≤ W) (wc : W ≤ width) (ai : a ≤ i) (quotaFit : i+a ≤ W)
    (b0 : ∀ p,F+1 < p → p < F+width+2 → ∃ v,T p=some v)
    (b1 : ∀ p,F+width+2 < p → p < F+width+n+3 → ∃ v,T p=some v) :
    ∃ t,t ≤ (i-a+1)*(32*(width+1)) ∧
      ((2*i ≤ W ∧ GPath (M:=machine k) P t
        (C k 99 m (F+2*width+n+4) (image T L n F width ell (i-a) (2*a) (W-i-a)))
        (C k 121 m (F+2*width+n+4) (image T L n F width ell 0 (2*i) (W-2*i)))) ∨
       (W < 2*i ∧ ∃ e,a ≤ e ∧ e < i ∧ W=i+e ∧ GPath (M:=machine k) P t
        (C k 99 m (F+2*width+n+4) (image T L n F width ell (i-a) (2*a) (W-i-a)))
        (C k 213 m (F+4*width+n+6) (image T L n F width ell (i-e-1) (2*e) 0)))) := by
  generalize measure : i-a=q
  induction q using Nat.strong_induction_on generalizing a with
  | h q ih=>
    rw [←measure]
    let A:=image T L n F width ell (i-a) (2*a) (W-i-a)
    have dec:=dec3 k P m (F+2*width+n+4) width (i-a) A hm (by omega) (by omega)
      (delimiters fr ell (i-a) (2*a) (W-i-a) 3 (by decide))
      (by have h:=delimiters fr ell (i-a) (2*a) (W-i-a) 4 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
      (by intro p lo hi;exact digit fr ell (i-a) (2*a) (W-i-a) 3 p (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
    by_cases empty : i=a
    · have zero : i-a=0:=by omega
      have rem : W-i-a=W-2*i:=by omega
      have copies : 2*a=2*i:=by omega
      simp only [zero,if_true,Nat.mul_zero,Nat.zero_add] at dec
      refine ⟨3,?_,Or.inl ⟨by omega,?_⟩⟩
      · rw [zero];simp only [Nat.zero_add,Nat.one_mul];omega
      · simpa only [A,zero,rem,copies] using dec
    · have positive : 0 < i-a:=by omega
      let B:=image T L n F width ell (i-a-1) (2*a) (W-i-a)
      have take : put A (F+2*width+n+4+(i-a)) (some false)=B:=take3 fr ell (i-a) (2*a) (W-i-a) positive (by omega)
      simp only [if_neg (by omega : ¬i-a=0),take] at dec
      have route:=toQuota k P m F width n B hm fit (delimiters fr ell (i-a-1) (2*a) (W-i-a))
        (occupied fr b0 b1 ell (i-a-1) (2*a) (W-i-a))
      have paid:=quota k P m (F+4*width+n+6) width (W-i-a) B hm (by omega) (by omega)
        (delimiters fr ell (i-a-1) (2*a) (W-i-a) 5 (by decide))
        (by have h:=delimiters fr ell (i-a-1) (2*a) (W-i-a) 6 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
        (by intro p lo hi;exact digit fr ell (i-a-1) (2*a) (W-i-a) 5 p (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
      by_cases noQuota : W-i-a=0
      · simp only [noQuota,if_true,Nat.mul_zero,Nat.zero_add] at paid
        have path:=joinPath (joinPath dec route) paid
        refine ⟨(2*(i-a)+3)+((width+2)+(width+2))+3,?_,Or.inr ⟨by omega,a,le_rfl,by omega,by omega,?_⟩⟩
        · nlinarith only [positive,_ic,wc,Nat.zero_le a]
        · simpa only [A,B,noQuota] using path
      · have qp : 0 < W-i-a:=by omega
        let D:=image T L n F width ell (i-a-1) (2*a) (W-i-a-1)
        have spent : put B (F+4*width+n+6+(W-i-a)) (some false)=D:=
          take5 fr ell (i-a-1) (2*a) (W-i-a) qp (by omega)
        simp only [if_neg noQuota,spent] at paid
        have forward:=to4 k P m F width n D hm fit (delimiters fr ell (i-a-1) (2*a) (W-i-a-1))
          (occupied fr b0 b1 ell (i-a-1) (2*a) (W-i-a-1))
        have outFits : 2*a+2 ≤ W:=by omega
        have incA:=inc4a k P m (F+3*width+n+5) width (2*a) D hm (by omega) (by omega)
          (delimiters fr ell (i-a-1) (2*a) (W-i-a-1) 4 (by decide))
          (by have h:=delimiters fr ell (i-a-1) (2*a) (W-i-a-1) 5 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
          (by intro p lo hi;exact digit fr ell (i-a-1) (2*a) (W-i-a-1) 4 p (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
        let E:=image T L n F width ell (i-a-1) (2*a+1) (W-i-a-1)
        have one : put D (F+3*width+n+5+2*a+1) (some true)=E:=add4 fr ell (i-a-1) (2*a) (W-i-a-1) (by omega)
        simp only [if_pos (by omega : 2*a < width),one] at incA
        have incB:=inc4b k P m (F+3*width+n+5) width (2*a+1) E hm (by omega) (by omega)
          (delimiters fr ell (i-a-1) (2*a+1) (W-i-a-1) 4 (by decide))
          (by have h:=delimiters fr ell (i-a-1) (2*a+1) (W-i-a-1) 5 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
          (by intro p lo hi;exact digit fr ell (i-a-1) (2*a+1) (W-i-a-1) 4 p (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
        let G:=image T L n F width ell (i-(a+1)) (2*(a+1)) (W-i-(a+1))
        have two : put E (F+3*width+n+5+(2*a+1)+1) (some true)=G:=by
          have h:=add4 fr ell (i-a-1) (2*a+1) (W-i-a-1) (by omega)
          simpa only [show i-a-1=i-(a+1) by omega,show W-i-a-1=W-i-(a+1) by omega,show 2*a+1+1=2*(a+1) by omega] using h
        simp only [if_pos (by omega : 2*a+1 < width),two] at incB
        have returning:=back3 k P m F width n G hm fit (delimiters fr ell (i-(a+1)) (2*(a+1)) (W-i-(a+1)))
          (occupied fr b0 b1 ell (i-(a+1)) (2*(a+1)) (W-i-(a+1)))
        obtain ⟨t,tp,result⟩:=ih (i-(a+1)) (by omega) (a+1) (by omega) (by omega) rfl
        have front:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath dec route) paid) forward) incA) incB) returning
        let cost:=(2*(i-a)+3)+((width+2)+(width+2))+(2*(W-i-a)+3)+(width+2)+(2*(2*a)+3)+(2*(2*a+1)+3)+(width+2)
        have bounded : cost ≤ 32*(width+1):=by dsimp only [cost];omega
        refine ⟨cost+t,?_,?_⟩
        · have decreased:=sub_step i a (by omega)
          calc
            cost+t ≤ 32*(width+1)+(i-(a+1)+1)*(32*(width+1)):=Nat.add_le_add bounded tp
            _ = (i-a+1)*(32*(width+1)):=by rw [←decreased];ring
        · rcases result with ⟨valid,rest⟩|⟨invalid,e,ae,ei,eq,rest⟩
          · exact Or.inl ⟨valid,joinPath front rest⟩
          · exact Or.inr ⟨invalid,e,by omega,ei,eq,joinPath front rest⟩
/-- The entire doubled-prefix phase, INCLUDING actual copy-back, reaches
indexBit or a literal quota abort. This is a component of the full BE driver. -/
private theorem prepared (k P m L n F width ell i W : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Banks T L n F width) (fit : F+5*width+n+7 ≤ P)
    (ic : i ≤ W) (wc : W ≤ width)
    (b0 : ∀ p,F+1 < p → p < F+width+2 → ∃ v,T p=some v)
    (b1 : ∀ p,F+width+2 < p → p < F+width+n+3 → ∃ v,T p=some v) :
    ∃ t,t ≤ 128*(width+1)^2 ∧
      ((2*i ≤ W ∧ GPath (M:=machine k) P t
        (C k 99 m (F+2*width+n+4) (image T L n F width ell i 0 (W-i)))
        (C k 136 m (F+2*width+n+4) (image T L n F width ell (2*i) 0 (W-2*i)))) ∨
       (W < 2*i ∧ ∃ e,e < i ∧ W=i+e ∧ GPath (M:=machine k) P t
        (C k 99 m (F+2*width+n+4) (image T L n F width ell i 0 (W-i)))
        (C k 213 m (F+4*width+n+6) (image T L n F width ell (i-e-1) (2*e) 0)))) := by
  obtain ⟨t,tp,result⟩:=loop k P m L n F width ell i W 0 T hm fr fit ic wc (by omega) (by omega) b0 b1
  simp only [Nat.sub_zero,Nat.mul_zero] at result tp
  rcases result with ⟨valid,path⟩|⟨invalid,e,_lo,ei,eq,path⟩
  · obtain ⟨u,up,rest⟩:=transfer k P m L n F width ell 0 (2*i) (W-2*i) T hm fr fit (by omega) b0 b1
    simp only [Nat.zero_add] at rest
    have joined:=joinPath path rest
    refine ⟨t+u,?_,Or.inl ⟨valid,joined⟩⟩
    have tb:=Nat.mul_le_mul_right (32*(width+1)) (show i+1 ≤ width+1 by omega)
    have ub:=Nat.mul_le_mul (show 2*i+1 ≤ width+1 by omega) (show 16*width+32 ≤ 32*(width+1) by omega)
    nlinarith only [tp,up,tb,ub,Nat.zero_le width,Nat.zero_le (width^2)]
  · refine ⟨t,?_,Or.inr ⟨invalid,e,ei,eq,path⟩⟩
    have tb:=Nat.mul_le_mul_right (32*(width+1)) (show i+1 ≤ width+1 by omega)
    nlinarith only [tp,tb,Nat.zero_le width,Nat.zero_le (width^2)]
#print axioms sub_step
#print axioms loop
#print axioms prepared
end VirtualFinalClosure.GuardDouble
