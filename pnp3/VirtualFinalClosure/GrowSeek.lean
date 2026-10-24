import VirtualFinalClosure.GrowStepRows
namespace VirtualFinalClosure.GrowSeek
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
  for key in ["r064_0","r065_0","r065_1","r066_0","r066_1"] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.GrowStepRows." && name.toString.endsWith (".VirtualFinalClosure.GrowStepRows."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous key) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank row {key}"
/-- Literal reset-to-copy traversal. In particular bank0 false is occupied,
not a blank delimiter, even when all other five banks were physically erased. -/
private theorem seek (k P m B width E : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (positive : 0 < width) (room : B+width+1 ≤ E) (fit : E ≤ P)
    (base : T B=none) (cells : ∀ i,B < i → i ≤ B+width → T i=some false)
    (gap : ∀ i,B+width+1 ≤ i → i ≤ E → T i=none) :
    GPath (M:=machine k) P (E-(B+width+1)+width+2)
      (C k 64 m E T) (C k 67 m B T) := by
  have entry:=keep (M:=machine k) (P:=P) (nc k 64 m) (nc k 65 m) E (E-1) T .left
    fit (by omega) (by rw [gap E room le_rfl];exact r064_0 k m hm) rfl
  have blanks:=sweepL (M:=machine k) (P:=P) (nc k 65 m) T (B+width) (E-(B+width+1))
    (by omega) (by
      intro i lo hi
      rw [gap i (by omega) (by omega)]
      exact r065_0 k m hm)
  rw [show B+width+(E-(B+width+1))=E-1 by omega] at blanks
  have turn:=keep (M:=machine k) (P:=P) (nc k 65 m) (nc k 66 m) (B+width) (B+(width-1)) T .left
    (by omega) (by omega) (by rw [cells _ (by omega) le_rfl];exact r065_1 k m hm)
    (by dsimp only [dest];omega)
  have back:=sweepL (M:=machine k) (P:=P) (nc k 66 m) T B (width-1) (by omega) (by
    intro i lo hi
    rw [cells i lo (by omega)]
    exact r066_1 k m hm)
  have finish:=keep (M:=machine k) (P:=P) (nc k 66 m) (nc k 67 m) B B T .stay
    (by omega) (by omega) (by rw [base];exact r066_0 k m hm) rfl
  have path:=joinPath (joinPath (joinPath (joinPath entry blanks) turn) back) finish
  convert path using 1;omega
#print axioms seek
end VirtualFinalClosure.GrowSeek
