import VirtualFinalClosure.GuardBit
import VirtualFinalClosure.GuardCross
namespace VirtualFinalClosure.GuardArithmeticRound
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
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","ellDec","ellDec",(1:Nat)),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","ellPaid","ellPaid",(1:Nat)),
      ("VirtualFinalClosure.GuardDouble","VirtualFinalClosure.GuardDouble","prepared","double",(1:Nat)),
      ("VirtualFinalClosure.GuardBit","VirtualFinalClosure.GuardBit","prepared","bitStep",(1:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",(0:Nat)),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","take2","take2",(1:Nat)),
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
/-- ENTIRE native arithmetic part of one BE-index iteration: consume one
real ell mark, double with the W quota, copy back, add the carried actual bit.
The source-pointer advance is the subsequent physical part of the same driver. -/
private theorem prepared (k P m L n F width ell i W : Nat) (T : Nat → Option Bool) (bit : Bool)
    (hm : m < 144) (fr : Banks T L n F width) (fit : F+5*width+n+7 ≤ P)
    (ellPositive : 0 < ell) (ellFits : ell ≤ width) (ic : i ≤ W) (wc : W ≤ width)
    (carried : sourceMode m=1 ↔ bit=true)
    (b0 : ∀ p,F+1 < p → p < F+width+2 → ∃ b,T p=some b)
    (b1 : ∀ p,F+width+2 < p → p < F+width+n+3 → ∃ b,T p=some b) :
    ∃ t,t ≤ 256*(width+1)^2 ∧
      ((2*i+(if bit then 1 else 0) ≤ W ∧ GPath (M:=machine k) P t
        (C k 93 m (F+width+n+3) (image T L n F width ell i 0 (W-i)))
        (C k 152 m (F+2*width+n+4) (image T L n F width (ell-1) (2*i+(if bit then 1 else 0)) 0 (W-(2*i+(if bit then 1 else 0)))))) ∨
       (W < 2*i+(if bit then 1 else 0) ∧ ∃ v out,GPath (M:=machine k) P t
        (C k 93 m (F+width+n+3) (image T L n F width ell i 0 (W-i)))
        (C k 213 m (F+4*width+n+6) (image T L n F width (ell-1) v out 0)))) := by
  let A:=image T L n F width ell i 0 (W-i)
  let B:=image T L n F width (ell-1) i 0 (W-i)
  have dec:=ellDec k P m (F+width+n+3) width ell A hm ellFits (by omega)
    (delimiters fr ell i 0 (W-i) 2 (by decide))
    (by have h:=delimiters fr ell i 0 (W-i) 3 (by decide); convert h using 1; dsimp only [SerializedBody.delimiter]; congr 1; omega)
    (by intro p lo hi;exact digit fr ell i 0 (W-i) 2 p (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter]; omega))
  have update : put A (F+width+n+3+ell) (some false)=B:=take2 fr ell i 0 (W-i) ellPositive ellFits
  simp only [if_neg (by omega : ¬ell=0),update] at dec
  have route:=ellPaid k P m F width n B hm fit (delimiters fr (ell-1) i 0 (W-i))
    (occupied fr b0 b1 (ell-1) i 0 (W-i))
  obtain ⟨d,dp,doubled⟩:=double k P m L n F width (ell-1) i W T hm fr fit ic wc b0 b1
  rcases doubled with ⟨large,path⟩|⟨bad,e,ei,we,path⟩
  · obtain ⟨b,bp,bitResult⟩:=bitStep k P m L n F width (ell-1) (2*i) W T bit hm fr fit large wc carried b0 b1
    have front:=joinPath (joinPath dec route) path
    refine ⟨(2*ell+3)+(width+2)+d+b,?_,?_⟩
    · nlinarith only [dp,bp,ellFits,Nat.zero_le width,Nat.zero_le (width^2)]
    · rcases bitResult with ⟨good,rest⟩|⟨bad,rest⟩
      · exact Or.inl ⟨good,joinPath front rest⟩
      · exact Or.inr ⟨bad,2*i,0,joinPath front rest⟩
  · refine ⟨(2*ell+3)+(width+2)+d,?_,Or.inr ⟨by cases bit <;> omega,i-e-1,2*e,?_⟩⟩
    · nlinarith only [dp,ellFits,Nat.zero_le width,Nat.zero_le (width^2)]
    · exact joinPath (joinPath dec route) path
#print axioms prepared
end VirtualFinalClosure.GuardArithmeticRound
