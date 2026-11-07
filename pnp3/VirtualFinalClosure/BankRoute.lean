import VirtualFinalClosure.Geometry
namespace VirtualFinalClosure.BankRoute
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong generic framed route term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique framed route interface {mod}/{key}"
/-- Literal adjacent-bank crossing on an opaque machine; occupied false and
true are both traversed, and width0 means genuinely adjacent blank delimiters. -/
private theorem right {M : UniformTM} (enter scan finish : Fin M.stateCount)
    (P D width : Nat) (T : Nat → Option Bool) (fit : D+width+1 ≤ P)
    (left : T D=none) (right : T (D+width+1)=none)
    (occupied : ∀ i,D < i → i < D+width+1 → ∃ b,T i=some b)
    (rEnter : M.step enter none=(scan,none,.right))
    (rScan : ∀ b : Bool,M.step scan (some b)=(scan,some b,.right))
    (rFinish : M.step scan none=(finish,none,.stay)) :
    GPath (M:=M) P (width+2) (node enter D T) (node finish (D+width+1) T) := by
  have a:=keep (M:=M) (P:=P) enter scan D (D+1) T .right
    (by omega) (by omega) (by rw [left];exact rEnter) rfl
  have b:=sweepR (M:=M) (P:=P) scan T (D+1) width (by omega) (by
    intro i lo hi;obtain ⟨b,cell⟩:=occupied i (by omega) (by omega);rw [cell];exact rScan b)
  have c:=keep (M:=M) (P:=P) scan finish (D+1+width) (D+width+1) T .stay
    (by omega) fit (by rw [show D+1+width=D+width+1 by omega,right];exact rFinish)
    (by dsimp only [dest];omega)
  convert joinPath (joinPath a b) c using 1; omega
private theorem left {M : UniformTM} (enter scan finish : Fin M.stateCount)
    (P D width : Nat) (T : Nat → Option Bool) (fit : D+width+1 ≤ P)
    (left : T D=none) (right : T (D+width+1)=none)
    (occupied : ∀ i,D < i → i < D+width+1 → ∃ b,T i=some b)
    (rEnter : M.step enter none=(scan,none,.left))
    (rScan : ∀ b : Bool,M.step scan (some b)=(scan,some b,.left))
    (rFinish : M.step scan none=(finish,none,.stay)) :
    GPath (M:=M) P (width+2) (node enter (D+width+1) T) (node finish D T) := by
  have a:=keep (M:=M) (P:=P) enter scan (D+width+1) (D+width) T .left
    fit (by omega) (by rw [right];exact rEnter) (by dsimp only [dest];omega)
  have b:=sweepL (M:=M) (P:=P) scan T D width (by omega) (by
    intro i lo hi;obtain ⟨b,cell⟩:=occupied i lo (by omega);rw [cell];exact rScan b)
  have c:=keep (M:=M) (P:=P) scan finish D D T .stay
    (by omega) (by omega) (by rw [left];exact rFinish) rfl
  convert joinPath (joinPath a b) c using 1; omega
#print axioms right
#print axioms left
end VirtualFinalClosure.BankRoute
