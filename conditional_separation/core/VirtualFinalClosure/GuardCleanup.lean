import VirtualFinalClosure.ConfigStay
import VirtualFinalClosure.CleanupPrepared
import VirtualFinalClosure.CleanupEntry
import VirtualFinalClosure.CleanupFrame
namespace VirtualFinalClosure.GuardCleanup
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ConfigStay","VirtualFinalClosure.ConfigStay","one","oneStay",(1:Nat)),
      ("VirtualFinalClosure.CleanupEntry","VirtualFinalClosure.CleanupEntry","cleanup_row","entryRow",(1:Nat)),
      ("VirtualFinalClosure.CleanupEntry","VirtualFinalClosure.CleanupEntry","cleanup_phase","phaseTwo",1),
      ("VirtualFinalClosure.CleanupPrepared","VirtualFinalClosure.CleanupPrepared","prepared","cleanup",1),
      ("VirtualFinalClosure.CleanupFrame","VirtualFinalClosure.CleanupFrame","actual","actualFrame",1),
      ("VirtualFinalClosure.CleanupFrame","VirtualFinalClosure.CleanupFrame","image_cleared","cleared",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("PostWeight.Kernel","PostWeight","Banks.room","bankRoom",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong guard-to-cleanup physical term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique guard-to-cleanup physical term {mod}/{key}"
private theorem q_value (k i : Nat) (fit : i < Cursor.stateCount k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt fit
/-- The guard's REAL final row followed by the COMPLETE original dirty-bank
cleanup, cut at its FIRST live old-mode2 boundary. Both BE success and quota
abort counters are allowed, without a fit assumption on the residual values. -/
private theorem prepared (k N B P S L n Q F width a b c d : Nat)
    (U : Nat → Option Bool) (m : Fin 144)
    (fr : Frame U S L (L+n+1) Q F) (banks : Banks U L n F width)
    (b0 : ∀ i,F+1 < i → i < F+width+2 → ∃ b,U i=some b)
    (b1 : ∀ i,F+width+2 < i → i < F+width+n+3 → ∃ b,U i=some b)
    (assn : ∀ i,L < i → i < L+n+1 → U i=some false)
    (fit : F+5*width+n+7 ≤ P) (finite : P < tapeLength N B) :
    let h0 : F+1 < tapeLength N B:=by omega
    let A:=image U L n F width a b c d
    let start : Config (machine k).stateCount N B:=⟨nc k 238 m.val,⟨F+1,h0⟩,fun j=>A j.val⟩
    ∃ (t : Nat) (hH : L+n+1 < tapeLength N B),
      t ≤ 1+(F-(L+n+1)+18*width+6*n+44) ∧
      (machine k).run t start=
        ⟨control k (tableControl k (936+93*k)) ⟨changeMeta 7 m.val,metaBound 7 _⟩,
          ⟨L+n+1,hH⟩,fun j=>Cursor.Target.scratch U F width n j.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ P):=by
  intro h0 A start
  have cleanFrame:=actualFrame fr banks b0 b1 a b c d
  have room:=bankRoom banks
  have blank : A (F+1)=none:=delimiters banks a b c d 0 (by decide)
  have first : (machine k).run 1 start=
      (⟨control k (tableControl k (798+93*k)) ⟨changeMeta 7 m.val,metaBound 7 _⟩,
        ⟨F+1,h0⟩,fun j=>A j.val⟩ : Config (machine k).stateCount N B):=by
    apply oneStay
    change (machine k).step (nc k 238 m.val) (A (F+1))=(_,A (F+1),.stay)
    rw [blank,entryRow k m.val m.isLt]
  obtain ⟨t,hH,price,done,heads,_firstReady⟩:=cleanup k N B P L n Q F width A
    ⟨changeMeta 7 m.val,metaBound 7 _⟩ (phaseTwo _) cleanFrame fit finite
  have lifted : lift k ⟨changeMeta 7 m.val,metaBound 7 _⟩
      (⟨Cursor.q k (798+93*k),⟨F+1,h0⟩,fun j=>A j.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨control k (tableControl k (798+93*k)) ⟨changeMeta 7 m.val,metaBound 7 _⟩,
        ⟨F+1,h0⟩,fun j=>A j.val⟩:=by
    dsimp only [lift]
    rw [q_value k _ (by unfold Cursor.stateCount;omega)]
  have actualDone := (congrArg (fun c=>(machine k).run t c) lifted.symm).trans done
  refine ⟨1+t,hH,by omega,?_,?_⟩
  · calc
      (machine k).run (1+t) start=(machine k).run t ((machine k).run 1 start):=UniformTM.run_add _ _ _ _
      _=(machine k).run t _:=congrArg (fun c=>(machine k).run t c) first
      _= _:=actualDone
      _= _:=by
        apply Config.ext_parts
        · rfl
        · rfl
        · exact congrArg (fun T=>fun j : Fin (tapeLength N B)=>T j.val) (cleared U L n F width a b c d room assn)
  · intro u hu
    by_cases zero : u=0
    · subst u;exact (by change F+1 ≤ P;omega)
    · have split : u=1+(u-1):=by omega
      have startEq : (machine k).run u start=(machine k).run (u-1)
          (lift k ⟨changeMeta 7 m.val,metaBound 7 _⟩
            (⟨Cursor.q k (798+93*k),⟨F+1,h0⟩,fun j=>A j.val⟩ : Config (Cursor.machine k).stateCount N B)):=by
        calc
          (machine k).run u start=(machine k).run (1+(u-1)) start:=congrArg (fun v=>(machine k).run v start) split
          _=(machine k).run (u-1) ((machine k).run 1 start):=UniformTM.run_add _ _ _ _
          _= _:=congrArg (fun c=>(machine k).run (u-1) c) first
          _= _:=congrArg (fun c=>(machine k).run (u-1) c) lifted.symm
      exact (congrArg (fun c=>c.head.val) startEq).trans_le (heads (u-1) (by omega))
#print axioms q_value
#print axioms prepared
end VirtualFinalClosure.GuardCleanup
