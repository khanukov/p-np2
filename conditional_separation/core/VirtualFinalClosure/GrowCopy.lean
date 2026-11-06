import VirtualFinalClosure.GrowSeek
namespace VirtualFinalClosure.GrowCopy
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual growing-bank path interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank path interface {mod}/{key}"
  for key in ["r067_0","r068_1","r068_2","r069_0","r069_1","r069_2","r070_0","r071_0","r071_1","r072_0","r072_1","r073_0","r066_0","r066_1","r066_2"] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.GrowStepRows." && name.toString.endsWith (".VirtualFinalClosure.GrowStepRows."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous key) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank row {key}"
private theorem unchanged (T : Nat → Option Bool) (h i : Nat) (b : Option Bool)
    (ne : i≠h) : put T h b i=T i := by
  change (if i=h then b else T i)=T i
  rw [if_neg ne]
/-- ONE actual growing-copy orbit. The old bank is marked in place; exactly
one new occupied false is appended beyond its real blank delimiter. -/
private theorem copy_round (k P m B width a : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (ha : a < width) (fit : B+2*width+2 ≤ P)
    (base : T B=none) (separator : T (B+width+1)=none)
    (old : ∀ i,B < i → i ≤ B+width → T i=some (decide (i ≤ B+a)))
    (temporary : ∀ i,B+width+1 < i → i ≤ B+width+1+a → T i=some false)
    (appendBlank : T (B+width+a+2)=none) :
    GPath (M:=machine k) P (2*width+2*a+7) (C k 67 m B T)
      (C k 67 m B (put (put T (B+a+1) (some true)) (B+width+a+2) (some false))) := by
  let h:=B+a+1
  let D:=B+width+1
  let U:=put T h (some true)
  let V:=put U (D+a+1) (some false)
  have hEq : h=B+a+1 := rfl
  have dEq : D=B+width+1 := rfl
  have outsideU (i : Nat) (ne : i≠h) : U i=T i := unchanged T h i (some true) ne
  have outsideV (i : Nat) (ne : i≠D+a+1) : V i=U i := unchanged U (D+a+1) i (some false) ne
  have start:=keep (M:=machine k) (P:=P) (nc k 67 m) (nc k 68 m) B (B+1) T .right
    (by omega) (by omega) (by rw [base];exact r067_0 k m hm) rfl
  have marked:=sweepR (M:=machine k) (P:=P) (nc k 68 m) T (B+1) a (by omega) (by
    intro i lo hi
    rw [old i (by omega) (by omega)]
    rw [decide_eq_true (by omega)]
    exact r068_2 k m hm)
  rw [show B+1+a=h by omega] at marked
  have picked : T h=some false := by
    rw [old h (by omega) (by omega),decide_eq_false (by omega)]
  have take:=hop (M:=machine k) (P:=P) (nc k 68 m) (nc k 69 m) h (h+1) T (some true) .right
    (by omega) (by omega) (by rw [picked];exact r068_1 k m hm) rfl
  have rest:=sweepR (M:=machine k) (P:=P) (nc k 69 m) U (h+1) (width-a-1) (by omega) (by
    intro i lo hi
    rw [outsideU i (by omega),old i (by omega) (by omega),decide_eq_false (by omega)]
    exact r069_1 k m hm)
  rw [show h+1+(width-a-1)=D by omega] at rest
  have uD : U D=none := (outsideU D (by omega)).trans separator
  have turn:=keep (M:=machine k) (P:=P) (nc k 69 m) (nc k 70 m) D D U .stay
    (by omega) (by omega) (by rw [uD];exact r069_0 k m hm) rfl
  have enterTemp:=keep (M:=machine k) (P:=P) (nc k 70 m) (nc k 71 m) D (D+1) U .right
    (by omega) (by omega) (by rw [uD];exact r070_0 k m hm) rfl
  have temp:=sweepR (M:=machine k) (P:=P) (nc k 71 m) U (D+1) a (by omega) (by
    intro i lo hi
    rw [outsideU i (by omega),temporary i (by omega) (by omega)]
    exact r071_1 k m hm)
  have append : U (D+1+a)=none := by
    rw [outsideU _ (by omega),show D+1+a=B+width+a+2 by omega,appendBlank]
  have write:=hop (M:=machine k) (P:=P) (nc k 71 m) (nc k 72 m) (D+1+a) (D+a) U (some false) .left
    (by omega) (by omega) (by rw [append];exact r071_0 k m hm) (by dsimp only [dest];omega)
  have backTemp:=sweepL (M:=machine k) (P:=P) (nc k 72 m) V D a (by omega) (by
    intro i lo hi
    rw [outsideV i (by omega),outsideU i (by omega),temporary i (by omega) (by omega)]
    exact r072_1 k m hm)
  have vD : V D=none := (outsideV D (by omega)).trans uD
  have backTurn:=keep (M:=machine k) (P:=P) (nc k 72 m) (nc k 73 m) D D V .stay
    (by omega) (by omega) (by rw [vD];exact r072_0 k m hm) rfl
  have toOld:=keep (M:=machine k) (P:=P) (nc k 73 m) (nc k 66 m) D (B+width) V .left
    (by omega) (by omega) (by rw [vD];exact r073_0 k m hm) (by dsimp only [dest];omega)
  have backOld:=sweepL (M:=machine k) (P:=P) (nc k 66 m) V B width (by omega) (by
    intro i lo hi
    rw [outsideV i (by omega)]
    by_cases atPick : i=h
    · subst i
      have cell : U h=some true := by dsimp only [U,put];rw [if_pos rfl]
      rw [cell];exact r066_2 k m hm
    · rw [outsideU i atPick,old i lo hi]
      cases b : decide (i ≤ B+a)
      · exact r066_1 k m hm
      · exact r066_2 k m hm)
  have vB : V B=none := (outsideV B (by omega)).trans ((outsideU B (by omega)).trans base)
  have endStep:=keep (M:=machine k) (P:=P) (nc k 66 m) (nc k 67 m) B B V .stay
    (by omega) (by omega) (by rw [vB];exact r066_0 k m hm) rfl
  rw [show D+1+a=D+a+1 by omega] at temp write
  have path:=joinPath start marked
  have path:=joinPath path take
  have path:=joinPath path rest
  have path:=joinPath path turn
  have path:=joinPath path enterTemp
  have path:=joinPath path temp
  have path:=joinPath path write
  have path:=joinPath path backTemp
  have path:=joinPath path backTurn
  have path:=joinPath path toOld
  have path:=joinPath path backOld
  have path:=joinPath path endStep
  have price : 1+a+1+(width-a-1)+1+1+a+1+a+1+1+width+1=2*width+2*a+7 := by omega
  rw [price] at path
  simpa only [V,U,D,h,show B+width+1+a+1=B+width+a+2 by omega] using path
#print axioms unchanged
#print axioms copy_round
end VirtualFinalClosure.GrowCopy
