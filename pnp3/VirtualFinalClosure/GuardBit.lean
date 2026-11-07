import VirtualFinalClosure.GuardDouble
import VirtualFinalClosure.GuardCross
import VirtualFinalClosure.ModeRows
namespace VirtualFinalClosure.GuardBit
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
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","add3","add3",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","indexQuota","quota",(1:Nat)),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","indexInc3","inc3",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","indexBitOne","toQuota",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","indexTo3","to3",(1:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","take5","take5",(1:Nat)),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","resolved_row","resolvedRow",(1:Nat)),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",(1:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",(0:Nat)),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",(0:Nat)),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",(0:Nat)),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",(1:Nat)),
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
private theorem bit_row (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 136 m) none=(nc k (if sourceMode m=1 then 137 else 152) m,none,.stay) := by
  have resolution : resolveCode k 244 (changeMeta 0 m)=
      (CertificateGuardClosure.machine k).stateCount+(if sourceMode m=1 then 137 else 152):=by
    rw [mode0 m hm];rfl
  have row:=resolvedRow k 136 m 244 (if sourceMode m=1 then 137 else 152) 0 1 0 none
    (by decide) hm (by run_tac cellTac 408) resolution
  rw [mode0 m hm] at row
  exact row
/-- Adds the ACTUAL finite-control source bit to the doubled BE value, paying
one literal unary quota cell if true. It never branches on a proof-side index. -/
private theorem prepared (k P m L n F width ell v W : Nat) (T : Nat → Option Bool) (bit : Bool)
    (hm : m < 144) (fr : Banks T L n F width) (fit : F+5*width+n+7 ≤ P)
    (vc : v ≤ W) (wc : W ≤ width) (carried : sourceMode m=1 ↔ bit=true)
    (b0 : ∀ p,F+1 < p → p < F+width+2 → ∃ b,T p=some b)
    (b1 : ∀ p,F+width+2 < p → p < F+width+n+3 → ∃ b,T p=some b) :
    ∃ t,t ≤ 32*(width+1) ∧
      ((v+(if bit then 1 else 0) ≤ W ∧ GPath (M:=machine k) P t
        (C k 136 m (F+2*width+n+4) (image T L n F width ell v 0 (W-v)))
        (C k 152 m (F+2*width+n+4) (image T L n F width ell (v+(if bit then 1 else 0)) 0 (W-(v+(if bit then 1 else 0)))))) ∨
       (W < v+(if bit then 1 else 0) ∧ GPath (M:=machine k) P t
        (C k 136 m (F+2*width+n+4) (image T L n F width ell v 0 (W-v)))
        (C k 213 m (F+4*width+n+6) (image T L n F width ell v 0 0)))) := by
  let A:=image T L n F width ell v 0 (W-v)
  have blankA:=delimiters fr ell v 0 (W-v)
  have first:=keep (M:=machine k) (P:=P) (nc k 136 m)
    (nc k (if sourceMode m=1 then 137 else 152) m) (F+2*width+n+4) (F+2*width+n+4) A .stay
    (by omega) (by omega) (by have h : A (F+2*width+n+4)=none:=blankA 3 (by decide);rw [h];exact bit_row k m hm) rfl
  cases bit with
  | false=>
    have notOne : sourceMode m≠1:=by intro h;have no:=carried.mp h;cases no
    rw [if_neg notOne] at first
    refine ⟨1,by omega,Or.inl ⟨by simpa using vc,?_⟩⟩
    simpa only [Bool.false_eq_true,if_false,Nat.add_zero] using first
  | true=>
    have one : sourceMode m=1:=carried.mpr rfl
    rw [if_pos one] at first
    have route:=toQuota k P m F width n A hm fit blankA (occupied fr b0 b1 ell v 0 (W-v))
    have dec:=quota k P m (F+4*width+n+6) width (W-v) A hm (by omega) (by omega)
      (blankA 5 (by decide)) (by have h:=blankA 6 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
      (by intro p lo hi;exact digit fr ell v 0 (W-v) 5 p (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
    by_cases empty : W-v=0
    · simp only [empty,if_true,Nat.mul_zero,Nat.zero_add] at dec
      have path:=joinPath (joinPath first route) dec
      refine ⟨1+((width+2)+(width+2))+3,by omega,Or.inr ⟨by simpa using (show W < v+1 by omega),?_⟩⟩
      simpa only [A,empty] using path
    · let B:=image T L n F width ell v 0 (W-v-1)
      have spent : put A (F+4*width+n+6+(W-v)) (some false)=B:=
        take5 fr ell v 0 (W-v) (by omega) (by omega)
      simp only [if_neg empty,spent] at dec
      have forward:=to3 k P m F width n B hm fit (delimiters fr ell v 0 (W-v-1)) (occupied fr b0 b1 ell v 0 (W-v-1))
      have inc:=inc3 k P m (F+2*width+n+4) width v B hm (by omega) (by omega)
        (delimiters fr ell v 0 (W-v-1) 3 (by decide))
        (by have h:=delimiters fr ell v 0 (W-v-1) 4 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
        (by intro p lo hi;exact digit fr ell v 0 (W-v-1) 3 p (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
      have update : put B (F+2*width+n+4+v+1) (some true)=image T L n F width ell (v+1) 0 (W-(v+1)):=by
        simpa only [show W-v-1=W-(v+1) by omega] using add3 fr ell v 0 (W-v-1) (by omega)
      simp only [if_pos (by omega : v < width),update] at inc
      have path:=joinPath (joinPath (joinPath (joinPath first route) dec) forward) inc
      refine ⟨1+((width+2)+(width+2))+(2*(W-v)+3)+((width+2)+(width+2))+(2*v+3),by omega,
        Or.inl ⟨by simpa using (show v+1 ≤ W by omega),?_⟩⟩
      simpa only [if_true] using path
#print axioms bit_row
#print axioms prepared
end VirtualFinalClosure.GuardBit
