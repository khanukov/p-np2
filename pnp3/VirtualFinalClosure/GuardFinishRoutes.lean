import VirtualFinalClosure.GuardFinishRows
import VirtualFinalClosure.GuardCross
namespace VirtualFinalClosure.GuardFinishRoutes
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.sourceEnd","sourceEnd",1),
      ("VirtualFinalClosure.GenericRoutes","VirtualFinalClosure.GenericRoutes","left_route","leftRoute",1),
      ("VirtualFinalClosure.GenericRoutes","VirtualFinalClosure.GenericRoutes","right_route","rightRoute",1),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","guardDoneD2","fromD2",1),
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","abortD5","fromD5",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row187_0","row187_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row188_1","row188_1",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row189_0","row189_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row189_2","row189_2",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row190_0","row190_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row190_2","row190_2",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row191_0","row191_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row192_0","row192_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row193_0","row193_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row223_0","row223_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row224_1","row224_1",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row225_0","row225_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row225_2","row225_2",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row226_0","row226_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row226_2","row226_2",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row227_0","row227_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row228_0","row228_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row229_0","row229_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row230_0","row230_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row231_0","row231_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row232_0","row232_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row233_0","row233_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row234_0","row234_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row235_0","row235_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row236_0","row236_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row236_2","row236_2",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row237_0","row237_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row237_1","row237_1",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row191","row191",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row193","row193",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row227","row227",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row229","row229",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row232","row232",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row234","row234",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
private theorem good (k P m S L H Q F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Frame T S L H Q F) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P (((n+2)+(width+2))+(F-S+3))
      (C k 183 m (F+width+n+3) T) (C k 194 m S T) := by
  have front:=fromD2 k P m F width n T hm fit blank occupied
  have route:=leftRoute (nc k 187 m) (nc k 188 m) (nc k 189 m) (nc k 190 m)
    (nc k 191 m) (nc k 192 m) (nc k 193 m) (nc k 194 m) P S L H Q F T fr (by omega)
    (row187_0 k m hm) (row188_1 k m hm) (row189_0 k m hm) (row189_2 k m hm)
    (row190_0 k m hm) (row190_2 k m hm) (row191_0 k m hm) (row191 k m hm)
    (row192_0 k m hm) (row193_0 k m hm) (row193 k m hm)
  exact joinPath front route
private theorem bad (k P m S L H Q F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Frame T S L H Q F) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P (((width+2)+(width+2)+(width+2)+(n+2)+(width+2))+(F-S+3)+1)
      (C k 213 m (F+4*width+n+6) T) (C k 194 (changeMode 5 m) S T) := by
  have front:=fromD5 k P m F width n T hm fit blank occupied
  have route:=leftRoute (nc k 223 m) (nc k 224 m) (nc k 225 m) (nc k 226 m)
    (nc k 227 m) (nc k 228 m) (nc k 229 m) (nc k 230 m) P S L H Q F T fr (by omega)
    (row223_0 k m hm) (row224_1 k m hm) (row225_0 k m hm) (row225_2 k m hm)
    (row226_0 k m hm) (row226_2 k m hm) (row227_0 k m hm) (row227 k m hm)
    (row228_0 k m hm) (row229_0 k m hm) (row229 k m hm)
  have marked:=keep (M:=machine k) (P:=P) (nc k 230 m) (nc k 194 (changeMode 5 m)) S S T .stay
    (by obtain ⟨sl,lh,_q,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega)
    (by obtain ⟨sl,lh,_q,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega)
    (by rw [sourceEnd fr];exact row230_0 k m hm) rfl
  exact joinPath (joinPath front route) marked
private theorem back (k P m S L H Q F : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fr : Frame T S L H Q F) (gap : H+Q+1 < F) (fit : F+1 ≤ P) :
    GPath (M:=machine k) P (F-S+3) (C k 231 m S T) (C k 238 m (F+1) T) := by
  exact rightRoute (nc k 231 m) (nc k 232 m) (nc k 233 m) (nc k 234 m)
    (nc k 235 m) (nc k 236 m) (nc k 237 m) (nc k 238 m) P S L H Q F T fr gap fit
    (row231_0 k m hm) (row232_0 k m hm) (row232 k m hm) (row233_0 k m hm)
    (row234_0 k m hm) (row234 k m hm) (row235_0 k m hm) (row236_0 k m hm)
    (row236_2 k m hm) (row237_0 k m hm) (row237_1 k m hm)
#print axioms good
#print axioms bad
#print axioms back
end VirtualFinalClosure.GuardFinishRoutes
