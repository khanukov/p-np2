import VirtualFinalClosure.CleanupPrepared
import VirtualFinalClosure.CleanupEntry
import VirtualFinalClosure.ConfigStay
namespace VirtualFinalClosure.DirtyReady
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.CleanupPrepared","VirtualFinalClosure.CleanupPrepared","prepared","cleanup",(1:Nat)),
      ("VirtualFinalClosure.CleanupEntry","VirtualFinalClosure.CleanupEntry","cleanup_row","entryRow",1),
      ("VirtualFinalClosure.CleanupEntry","VirtualFinalClosure.CleanupEntry","cleanup_phase","phaseTwo",1),
      ("VirtualFinalClosure.ConfigStay","VirtualFinalClosure.ConfigStay","one","oneStay",1),
      ("VirtualReady.Kernel","VirtualReady","Frame","Frame",2),
      ("VirtualReady.Kernel","VirtualReady","Frame.blank","delimiters",1),
      ("VirtualReady.Kernel","VirtualReady","D","D",0),
      ("VirtualReady.Kernel","VirtualReady","stage","stage",0),
      ("VirtualReady.Kernel","VirtualReady","paint","paint",0),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong arbitrary dirty-cleanup term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique arbitrary dirty-cleanup term {mod}/{key}"
/-- The real seen0 tail may retain dirty assignment/power-cap banks. This
literal cleanup accepts their occupied frame and physically erases them; no
false-assignment or fabricated GuardImage premise is required. Its result tape
is the explicit pre-run T passed through the executed paint stages. -/
private theorem prepared (k N B P L n Q F width : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (fr : Frame T L n Q F width) (fit : F+5*width+n+7≤P) (finite : P<tapeLength N B) :
    let h0 : F+1<tapeLength N B:=by omega
    let start : Config (machine k).stateCount N B:=⟨nc k 238 m.val,⟨F+1,h0⟩,fun i=>T i.val⟩
    ∃ (t : Nat) (hH : L+n+1<tapeLength N B),t≤F-(L+n+1)+18*width+6*n+45 ∧
      (machine k).run t start=
        ⟨control k (tableControl k (936+93*k)) ⟨changeMeta 7 m.val,metaBound 7 _⟩,
          ⟨L+n+1,hH⟩,fun i=>paint (stage T F width n 6) (L+1) (L+n+1) i.val⟩ ∧
      (∀ u,u≤t → ((machine k).run u start).head.val≤P):=by
  intro h0 start
  let md : Fin 144:=⟨changeMeta 7 m.val,metaBound 7 _⟩
  have blank : T (F+1)=none:=by
    have cell:=delimiters fr 0 (by decide)
    change T (F+1)=none at cell
    exact cell
  have first : (machine k).run 1 start=
      (⟨control k (tableControl k (798+93*k)) md,⟨F+1,h0⟩,fun i=>T i.val⟩ : Config (machine k).stateCount N B):=by
    apply oneStay
    change (machine k).step (nc k 238 m.val) (T (F+1))=(_,T (F+1),.stay)
    rw [blank,entryRow k m.val m.isLt]
  obtain ⟨t,hH,tp,done,heads,_first⟩:=cleanup k N B P L n Q F width T md (phaseTwo _) fr fit finite
  have qv : (Cursor.q k (798+93*k)).val=798+93*k:=Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
  have initial : lift k md (⟨Cursor.q k (798+93*k),⟨F+1,h0⟩,fun i=>T i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨control k (tableControl k (798+93*k)) md,⟨F+1,h0⟩,fun i=>T i.val⟩:=by
    dsimp only [lift]
    rw [qv]
  rw [initial] at done heads
  refine ⟨1+t,hH,by omega,?_,?_⟩
  · rw [UniformTM.run_add,first]
    exact done
  · intro u hu
    by_cases zero : u=0
    · subst u;change F+1≤P;omega
    · rw [show u=1+(u-1) by omega,UniformTM.run_add,first]
      exact heads (u-1) (by omega)
#print axioms prepared
end VirtualFinalClosure.DirtyReady
