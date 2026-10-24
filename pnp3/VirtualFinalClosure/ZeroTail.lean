import VirtualFinalClosure.SourceFinish
import VirtualFinalClosure.GuardFinishRoutes
namespace VirtualFinalClosure.ZeroTail
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceFinish","VirtualFinalClosure.SourceFinish","dispatch","dispatch",(1:Nat)),
      ("VirtualFinalClosure.SourceFinish","VirtualFinalClosure.SourceFinish","restore_hole","restore",1),
      ("VirtualFinalClosure.GuardFinishRoutes","VirtualFinalClosure.GuardFinishRoutes","back","back",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protectedFrame",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.SL","sourceLow",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.sourceEnd","sourceEnd",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong real zero-suffix continuation {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique real zero-suffix continuation {mod}/{key}"
/-- The ACTUAL seen0 dispatcher restores the saved occupied p-bit and every
other source cell remains literal, then returns physically to D0/q238. It does
not compute W or reject a virtual witness; final cleanup/dispatch is subsequent. -/
private theorem prepared (k P m S L H Q F p : Nat) (T : Nat → Option Bool) (b : Bool)
    (hm : m < 144) (zero : seen m=0) (fr : Frame T S L H Q F)
    (gap : H+Q+1 < F) (fit : F+1 ≤ P) (physical : p < S)
    (mode : sourceMode m=(if b then 1 else 0)) (hole : T p=none)
    (source : ∀ i,p < i → i < S → ∃ bit,T i=some bit) :
    GPath (M:=machine k) P (F-p+5) (C k 40 m p T)
      (C k 238 m (F+1) (put T p (some b))) := by
  have sl:=sourceLow fr
  have frCopy:=fr
  obtain ⟨_sl,lh,_q,room,_,_,_,_,_,_,_,_,_⟩:=frCopy
  have d:=dispatch k P m p T hm (by omega) hole
  rw [zero,if_neg (by decide : ¬(0=1))] at d
  have r:=restore k P m S p T b hm physical (by omega) mode (sourceEnd fr) hole source
  let U:=put T p (some b)
  have restored : Frame U S L H Q F:=protectedFrame fr (by
    intro i lo _hi
    dsimp only [U,put]
    rw [if_neg (by omega)])
  have route:=back k P m S L H Q F U hm restored gap fit
  have path:=joinPath (joinPath d r) route
  convert path using 1; omega
#print axioms prepared
end VirtualFinalClosure.ZeroTail
