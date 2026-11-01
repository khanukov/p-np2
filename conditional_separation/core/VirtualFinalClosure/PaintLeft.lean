import VirtualFinalClosure.PaintPath
namespace VirtualFinalClosure.PaintLeft
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
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual growing-bank path interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank path interface {mod}/{key}"
private theorem add_back (T : Nat → Option Bool) (h width : Nat) (b : Option Bool) :
    block (put T (h+width+1) b) (h+1) width b=block T (h+1) (width+1) b := by
  funext i
  dsimp only [block,put]
  by_cases last : i=h+width+1
  · subst i
    rw [if_neg (by omega),if_pos rfl,if_pos (by omega)]
  · rw [if_neg last]
    have same : (h+1 ≤ i ∧ i < h+1+width) ↔ (h+1 ≤ i ∧ i < h+1+(width+1)) := by omega
    simp only [same]
/-- Physical writing LEFT scan; head0 is never subtracted below the actual
lower endpoint. Same existing hop/path semantics, arbitrary exterior tape. -/
private theorem paint_left {M : UniformTM} (q : Fin M.stateCount) (P h width : Nat)
    (T : Nat → Option Bool) (b : Option Bool) (fit : h+width ≤ P)
    (occupied : ∀ i,h < i → i ≤ h+width → ∃ v,T i=some v)
    (row : ∀ v : Bool,M.step q (some v)=(q,b,.left)) :
    GPath (M:=M) P width (node q (h+width) T) (node q h (block T (h+1) width b)) := by
  induction width generalizing T with
  | zero=>
    have image : block T (h+1) 0 b=T := by
      funext i
      dsimp only [block]
      rw [if_neg (by omega)]
    rw [image]
    exact nilPath _ (by change h ≤ P;omega)
  | succ width ih=>
    obtain ⟨v,cell⟩:=occupied (h+width+1) (by omega) (by omega)
    have entry:=hop (M:=M) (P:=P) q q (h+width+1) (h+width) T b .left
      (by omega) (by omega) (by rw [cell];exact row v) (by dsimp only [dest];omega)
    have tail:=ih (put T (h+width+1) b) (by omega) (by
      intro i lo hi
      change ∃ v,(if i=h+width+1 then b else T i)=some v
      rw [if_neg (by omega)]
      exact occupied i lo (by omega))
    have path:=joinPath entry tail
    rw [add_back] at path
    simpa only [Nat.add_comm 1 width,Nat.add_assoc] using path
#print axioms add_back
#print axioms paint_left
end VirtualFinalClosure.PaintLeft
