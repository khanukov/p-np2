import VirtualFinalClosure.GuardForwardRows
import VirtualFinalClosure.GuardCross
namespace VirtualFinalClosure.GuardRoutes
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.GenericRoutes","VirtualFinalClosure.GenericRoutes","left_route","leftRoute",1),
      ("VirtualFinalClosure.GenericRoutes","VirtualFinalClosure.GenericRoutes","right_route","rightRoute",1),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","advanceD3","fromD3",1),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","advanceAtD0","toD2",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row158_0","row158_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row159_1","row159_1",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row160_0","row160_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row160_2","row160_2",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row161_0","row161_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row161_2","row161_2",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row162_0","row162_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row163_0","row163_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row164_0","row164_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row172_0","row172_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row173_0","row173_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row174_0","row174_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row175_0","row175_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row176_0","row176_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row177_0","row177_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row177_2","row177_2",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row178_0","row178_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row178_1","row178_1",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row162","row162",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row164","row164",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row173","row173",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row175","row175",1) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
private theorem to_source (k P m S L H Q F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Frame T S L H Q F) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P (((width+2)+(n+2)+(width+2))+(F-S+3))
      (C k 152 m (F+2*width+n+4) T) (C k 165 m S T) := by
  have front:=fromD3 k P m F width n T hm fit blank occupied
  have route:=leftRoute (nc k 158 m) (nc k 159 m) (nc k 160 m) (nc k 161 m)
    (nc k 162 m) (nc k 163 m) (nc k 164 m) (nc k 165 m) P S L H Q F T fr (by omega)
    (row158_0 k m hm) (row159_1 k m hm) (row160_0 k m hm) (row160_2 k m hm)
    (row161_0 k m hm) (row161_2 k m hm) (row162_0 k m hm) (row162 k m hm)
    (row163_0 k m hm) (row164_0 k m hm) (row164 k m hm)
  exact joinPath front route
private theorem to_banks (k P m S L H Q F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Frame T S L H Q F) (gap : H+Q+1 < F) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((F-S+3)+((width+2)+(n+2)))
      (C k 172 m S T) (C k 93 m (F+width+n+3) T) := by
  have route:=rightRoute (nc k 172 m) (nc k 173 m) (nc k 174 m) (nc k 175 m)
    (nc k 176 m) (nc k 177 m) (nc k 178 m) (nc k 179 m) P S L H Q F T fr gap (by omega)
    (row172_0 k m hm) (row173_0 k m hm) (row173 k m hm) (row174_0 k m hm)
    (row175_0 k m hm) (row175 k m hm) (row176_0 k m hm) (row177_0 k m hm)
    (row177_2 k m hm) (row178_0 k m hm) (row178_1 k m hm)
  have back:=toD2 k P m F width n T hm fit blank occupied
  exact joinPath route back
#print axioms to_source
#print axioms to_banks
end VirtualFinalClosure.GuardRoutes
