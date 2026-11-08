import VirtualFinalClosure.ReplayConfig
import IngressAllocation.WorkspaceTrace
namespace VirtualFinalClosure.WorkspaceReplay
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("IngressAllocation.WorkspaceTrace","IngressAllocation","workspace_heads","workspaceHeads",(1:Nat)),
      ("VirtualFinalClosure.ReplayBounds","VirtualFinalClosure.ReplayBounds","workspace_floor","workspaceFloor",1),
      ("VirtualFinalClosure.ReplayConfig","VirtualFinalClosure.ReplayConfig","run_lift","runLift",1),
      ("VirtualFinalClosure.ReplayConfig","VirtualFinalClosure.ReplayConfig","lift","lift",0),
      ("VirtualFinalClosure.ReplayPlain","VirtualFinalClosure.ReplayPlain","body_minimum","bodyMinimum",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_value","packValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual workspace replay/footprint interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual workspace replay/footprint interface {mod}/{key}"
private theorem q_value (k i : Nat) (hi : i ≤ 201) : (Cursor.q k i).val=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
private theorem slot_value (k : Nat) (q : Fin (Cursor.machine k).stateCount) (m : Fin 144) :
    (control k (tableControl k q.val) m).val=144*(375+q.val)+m.val := by
  have value : (control k (tableControl k q.val) m).val=144*(tableControl k q.val).val+m.val :=
    packValue k (tableControl k q.val).val m.val
      (by have h:=(tableControl k q.val).isLt;omega) m.isLt
  rw [tableValue k q.val q.isLt] at value
  exact value
/-- SAME literal candidate: actual q98 -> local FIRST q201 on the restored
workspace. Generic n includes0; arbitrary exterior/p-hole below S is preserved.
EVERY prefix Config and physical head bound refer to the SAME actual witness. -/
private theorem workspace (k N B S L n Q F r : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (sl : S < L) (paid : 0 < Q) (room : L+n+1+Q < F)
    (eof : T S=none) (reg : ∀ i,S < i → i < L → T i=some false)
    (sep : T L=none) (assn : ∀ i,L < i → i < L+n+1 → T i=some false)
    (right : T (L+n+1)=none)
    (marks : ∀ i,L+n+1 < i → i ≤ L+n+1+Q → T i=some true)
    (gap : ∀ i,L+n+1+Q < i → i < F → T i=none)
    (fence : T F=some false) (d0 : T (F+1)=none)
    (bank0 : ∀ i,F+1 < i → i < F+r+2 → T i=some true)
    (fresh : ∀ i,F+r+2 ≤ i → i ≤ F+5*r+n+7 → T i=none)
    (fit : F+5*r+n+7 < tapeLength N B) :
    let old : Config (Cursor.machine k).stateCount N B:=
      ⟨Cursor.rReady k,⟨S,by omega⟩,fun i=>T i.val⟩
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k 98) m,⟨S,by omega⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 128*(n+r+1)*(F+5*r+n+9) ∧
      (machine k).run t start=
        ⟨control k (tableControl k 201) m,⟨F+1,by omega⟩,
          fun i=>CappedWorkspace.Target.image T L n F r i.val⟩ ∧
      (∀ u,u < t → ∀ flag : Fin 144,((machine k).run u start).state≠control k (tableControl k 201) flag) ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ F+5*r+n+7) ∧
      (∀ u,u ≤ t → (machine k).run u start=lift k m ((Cursor.machine k).run u old)) ∧
      (∀ u,u ≤ t → ((machine k).run u start).state≠(machine k).accept ∧
        ((machine k).run u start).state≠(machine k).reject ∧
        ∀ (j : Fin 3) (flag : Fin 144),((machine k).run u start).state≠control k (bodyControl k j) flag) := by
  intro old start
  obtain ⟨t,price,actual,first,heads⟩:=workspaceHeads k N B S L n Q F r T sl paid room eof reg sep assn right marks gap fence d0 bank0 fresh fit
  have startValue : old.state.val=98 := by
    change (Cursor.rReady k).val=98
    exact q_value k 98 (by decide)
  have finishValue : ((Cursor.machine k).run t old).state.val=201 := by
    rw [actual]
    exact q_value k 201 le_rfl
  have lower:=workspaceFloor k N B t old startValue finishValue first
  have range : ∀ u,u ≤ t → 98 ≤ ((Cursor.machine k).run u old).state.val ∧
      ((Cursor.machine k).run u old).state.val ≤ 201 := by
    intro u hu
    refine ⟨lower u hu,?_⟩
    by_cases early : u < t
    · exact (first u early).le
    · have equal : u=t := by omega
      subst u
      exact finishValue.le
  have initial : start=lift k m old := by
    apply Config.ext_parts
    · exact (congrArg (fun i=>control k (tableControl k i) m) startValue).symm
    · rfl
    · rfl
  have simulation:=runLift k m old t range first
  have done:=(simulation t le_rfl)
  rw [←initial,actual] at done
  have ended : (machine k).run t start=
      ⟨control k (tableControl k 201) m,⟨F+1,by omega⟩,
        fun i=>CappedWorkspace.Target.image T L n F r i.val⟩ := by
    simpa only [lift,q_value k 201 le_rfl] using done
  have values (u : Nat) (hu : u ≤ t) :
      ((machine k).run u start).state.val=144*(375+((Cursor.machine k).run u old).state.val)+m.val := by
    rw [initial,simulation u hu]
    exact slot_value k ((Cursor.machine k).run u old).state m
  refine ⟨t,price,ended,?_,?_,?_,?_⟩
  · intro u hu flag equal
    have currentValue:=values u hu.le
    have nextValue:=slot_value k (Cursor.q k 201) flag
    rw [q_value k 201 le_rfl] at nextValue
    have actualValue:=congrArg Fin.val equal
    rw [currentValue] at actualValue
    rw [nextValue] at actualValue
    have small:=first u hu
    change ((Cursor.machine k).run u old).state.val < 201 at small
    have fm:=m.isLt
    omega
  · intro u hu
    rw [initial,simulation u hu]
    exact heads u hu
  · intro u hu
    rw [initial]
    exact simulation u hu
  · intro u hu
    have currentValue:=values u hu
    have band:=range u hu
    have term:=terminalValues k
    have oldTerms:=oldTerminals k
    rw [oldTerms.1,oldTerms.2] at term
    refine ⟨?_,?_,?_⟩
    · intro equal
      have same:=congrArg Fin.val equal
      rw [currentValue,term.1] at same
      omega
    · intro equal
      have same:=congrArg Fin.val equal
      rw [currentValue,term.2] at same
      omega
    · intro j flag equal
      have high:=bodyMinimum k j
      have targetValue : (control k (bodyControl k j) flag).val=144*(bodyControl k j).val+flag.val :=
        packValue k (bodyControl k j).val flag.val (by have h:=(bodyControl k j).isLt;omega) flag.isLt
      have same:=congrArg Fin.val equal
      rw [currentValue,targetValue] at same
      have mf:=m.isLt
      omega
#print axioms q_value
#print axioms slot_value
#print axioms workspace
end VirtualFinalClosure.WorkspaceReplay
