import VirtualFinalClosure.MarkerState
import VirtualFinalClosure.GuardFlags
namespace VirtualFinalClosure.MarkerMeaning
open Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_fields","fields",(1:Nat)),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","flag_preserved","flagPreserved",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","bad_preserved","badPreserved",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_bound","bound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong finite paid-flag preservation term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique finite paid-flag preservation {mod}/{key}"
private theorem initial (f : Fin 4) : flag (8+f.val)=f.val ∧ bad (8+f.val)=0:=by
  fin_cases f <;> decide
private theorem marker (f : Fin 4) (bits : Nat → Bool) (r : Nat) :
    flag (modes (8+f.val) bits r)=f.val ∧ bad (modes (8+f.val) bits r)=0:=by
  rw [(fields (8+f.val) bits r).1,(fields (8+f.val) bits r).2.2]
  exact initial f
private theorem reentry (f : Fin 4) (bits : Nat → Bool) (r : Nat) :
    flag (changeMeta 4 (modes (8+f.val) bits r))=f.val ∧
      bad (changeMeta 4 (modes (8+f.val) bits r))=0:=by
  have valid : modes (8+f.val) bits r < 144:=bound _ _ _ (by have h:=f.isLt;omega)
  rw [flagPreserved 4 _ valid,badPreserved 4 _ valid (by decide) (by decide)]
  exact marker f bits r
#print axioms initial
#print axioms marker
#print axioms reentry
end VirtualFinalClosure.MarkerMeaning
