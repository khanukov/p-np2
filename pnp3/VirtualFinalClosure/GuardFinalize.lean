import VirtualFinalClosure.GuardCleanup
import VirtualFinalClosure.LeafFinish
namespace VirtualFinalClosure.GuardFinalize
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardCleanup","VirtualFinalClosure.GuardCleanup","prepared","cleanup",(1:Nat)),
      ("VirtualFinalClosure.LeafFinish","VirtualFinalClosure.LeafFinish","prepared","leaf",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.room","room",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.separator","separator",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.assignmentEnd","assignmentEnd",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("SmallIngress.Runtime","SmallIngress","put","put",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong executed guard-to-FINAL interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique executed guard-to-FINAL interface {mod}/{key}"
private theorem scratch_low (U : Nat → Option Bool) (F C n i : Nat) (low : i≤F+1) :
    Cursor.Target.scratch U F C n i=U i:=by
  dsimp only [Cursor.Target.scratch]
  rw [if_neg (by omega)]
private theorem flags (m : Fin 144) : flag (changeMeta 7 m.val)=flag m.val ∧ bad (changeMeta 7 m.val)=bad m.val:=by
  fin_cases m <;> decide
/-- Native q238 performs the real cleanup, canonical five-edge false-assignment
leaf, and literal FINAL edge. This closes execution of the guard continuation;
identifying its flags with the entire original rho is a separate raw obligation. -/
private theorem prepared (k N B P S L n Q F C a b c d : Nat) (U : Nat → Option Bool) (m : Fin 144)
    (positive : 0 < n) (fr : Frame U S L (L+n+1) Q F) (banks : Banks U L n F C)
    (b0 : ∀ i,F+1 < i → i < F+C+2 → ∃ v,U i=some v)
    (b1 : ∀ i,F+C+2 < i → i < F+C+n+3 → ∃ v,U i=some v)
    (assn : ∀ i,L < i → i < L+n+1 → U i=some false)
    (fit : F+5*C+n+7≤P) (finite : P < tapeLength N B) :
    let h0 : F+1 < tapeLength N B:=by omega
    let start : Config (machine k).stateCount N B:=
      ⟨nc k 238 m.val,⟨F+1,h0⟩,fun j=>image U L n F C a b c d j.val⟩
    ∃ (t : Nat) (hH : L+n+1 < tapeLength N B),t≤F-(L+n+1)+18*C+6*n+51 ∧
      (machine k).run t start=
        ⟨if flag m.val%2=1 ∧ bad m.val=0 then (machine k).accept else (machine k).reject,
          ⟨L+n+1,hH⟩,fun j=>put (Cursor.Target.scratch U F C n) (L+n+1) (some false) j.val⟩ ∧
      (∀ u,u≤t → ((machine k).run u start).head.val≤P):=by
  intro h0 start
  have geometry:=room fr
  have lowH : L+n+1≤F+1:=by omega
  let m2 : Fin 144:=⟨changeMeta 7 m.val,metaBound 7 _⟩
  let T:=Cursor.Target.scratch U F C n
  obtain ⟨t,hH,tp,done,heads⟩:=cleanup k N B P S L n Q F C a b c d U m fr banks b0 b1 assn fit finite
  have finalLeaf:=leaf k N B P L n m2 T (fun _=>false) positive (by omega) finite
    ((scratch_low U F C n L (by omega)).trans (separator fr))
    ((scratch_low U F C n (L+n+1) lowH).trans (assignmentEnd fr))
    (by
      intro j
      change Cursor.Target.scratch U F C n (L+n-j.val)=some false
      rw [scratch_low U F C n (L+n-j.val) (by omega)]
      exact assn _ (by have h:=j.isLt;omega) (by omega))
  obtain ⟨leafDone,_safeLeaf,leafHeads⟩:=finalLeaf
  have eqFlags : (flag m2.val%2=1 ∧ bad m2.val=0) ↔ (flag m.val%2=1 ∧ bad m.val=0):=by
    dsimp only [m2]
    rw [(flags m).1,(flags m).2]
  refine ⟨t+6,hH,by omega,?_,?_⟩
  · rw [UniformTM.run_add,done]
    simpa only [eqFlags,T] using leafDone
  · intro u hu
    by_cases early : u≤t
    · exact heads u early
    · rw [show u=t+(u-t) by omega,UniformTM.run_add,done]
      exact leafHeads (u-t) (by omega)
#print axioms scratch_low
#print axioms flags
#print axioms prepared
end VirtualFinalClosure.GuardFinalize
