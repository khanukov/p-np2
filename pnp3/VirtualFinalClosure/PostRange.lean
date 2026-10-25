import CarryReadyCompletion.Native
import VirtualFinalClosure.FullReplay
namespace VirtualFinalClosure.PostRange
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualReady.Kernel","VirtualReady","Node","Node",(2:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.mk","node",(3:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.state","state",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.head","head",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.tape","tape",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","embed","embed",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Path","Path",(2:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Path.nil","nilPath",(3:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Path.cons","consPath",(3:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Path.execute","execute",(1:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Edge.after","edgeAfter",(1:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","Good","Good",(0:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","D","D",(0:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","active_limits","activeLimits",(1:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","loc_bounds","locBounds",(1:Nat)),
      ("CarryReadyCompletion.Native","CarryReadyCompletion","good_tail","goodTail",(1:Nat)),
      ("CarryReadyCompletion.Native","CarryReadyCompletion","first613_edge","first613",(1:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual post-W prefix interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual post-W prefix interface {mod}/{key}"
private theorem good_bounds {k F r n : Nat} {c : Node k} (good : Good k F r n c) :
    430+93*k ≤ (state c).val ∧ (state c).val ≤ 613+93*k ∧ F+1 ≤ head c ∧ head c ≤ F+5*r+n+7 := by
  obtain ⟨i,l,ilo,ihi,st,hl,live,loc,_shape⟩:=good
  have active:=activeLimits live
  have bounds:=locBounds hl loc
  have value : (Cursor.q k (i+93*k)).val=i+93*k:=Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
  rw [st,value]
  have br:=bounds.2
  have bl:=bounds.1
  change F+1 ≤ head c at bl
  change head c ≤ F+5*r+n+7 at br
  rcases active with h|h <;> omega
/-- Every prefix node of the REAL native post-W path retains its certified
control/physical-bank location; endpoint equality alone is not used as a floor. -/
private theorem path_trace {k N B P F r n t : Nat} {c d : Node k}
    (path : Path k P t c d) (good : Good k F r n c)
    (last : state d=Cursor.q k (613+93*k)) (fit : P < tapeLength N B) :
    ∀ (hc : head c < tapeLength N B) (u : Nat),u ≤ t →
      ∃ (v : Node k) (hv : head v < tapeLength N B),
        (Cursor.machine k).run u (embed c hc)=embed v hv ∧ Good k F r n v ∧
          (u < t → state v≠Cursor.q k (613+93*k)) := by
  induction path with
  | nil c hp=>
    intro hc u hu
    have zero : u=0:=by omega
    subst u
    exact ⟨c,hc,rfl,good,by omega⟩
  | @cons t c d e edge rest ih=>
    have next:=goodTail edge rest good last
    intro hc u hu
    cases u with
    | zero=>exact ⟨c,hc,rfl,good,fun _=>first613 edge rest good last⟩
    | succ u=>
      have hd : head d < tapeLength N B:=(edgeAfter edge).trans_lt fit
      have one : Path k P 1 c d:=consPath edge (nilPath d (edgeAfter edge))
      have oneRun:=execute (N:=N) (B:=B) one fit
      obtain ⟨v,hv,run,vg,vfirst⟩:=ih next.1 last hd u (by omega)
      refine ⟨v,hv,?_,vg,?_⟩
      · rw [show u+1=1+u by omega,UniformTM.run_add,oneRun]
        exact run
      · intro early;exact vfirst (by omega)
#print axioms good_bounds
#print axioms path_trace
end VirtualFinalClosure.PostRange
