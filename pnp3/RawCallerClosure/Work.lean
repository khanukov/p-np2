import RawCallerClosure.Transport
import TotalIngressClosure.FirstEvents
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName,kind) in [
    (`TotalIngressClosure.EventSafety,`TotalIngressClosure,"leaf_row","leafRow","theorem"),
    (`TotalIngressClosure.EventSafety,`TotalIngressClosure,"old_entry_disjoint","entryDisjoint","theorem"),
    (`TotalIngressClosure.FirstEvents,`TotalIngressClosure,"leaf_terminal","leafTerminal","theorem"),
    (`PhysicalCallerClosure.Rows,`PhysicalCallerClosure,"old_injective","oldInjective","theorem"),
    (`PhysicalCallerClosure.Controller,`PhysicalCallerClosure,"liftOld","liftOld","definition"),
    (`PhysicalCallerClosure.Controller,`PhysicalCallerClosure,"native","native","definition"),
    (`RawCallerClosure.Rows,`RawCallerClosure,"old_body","oldBody","theorem")] do
    let found:=e.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++owner.toString++".") && n.toString.endsWith ("."++ns.toString++"."++leaf)
    let [(n,ci)]:=found | throwError "Nonunique immutable WORK term"
    let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
    unless actual==kind do throwError "Wrong WORK kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong WORK owner"
    logInfo m!"ordinary-work|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private def bodyWork (k : Nat) (v : Bool) : Fin (BodyIngress.machine k).stateCount :=
  BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k v))
private def work (k : Nat) (v : Bool) : Fin (CertificateGuardClosure.machine k).stateCount :=
  CertificateGuardClosure.old k (TotalIngressClosure.old k (bodyWork k v))
private theorem body_work_row (k : Nat) (v : Bool) (b : Option Bool) :
    (BodyIngress.machine k).step (bodyWork k v) b=(bodyWork k v,b,.stay) := leafRow k v b
private theorem body_work_terminal (k : Nat) (v : Bool) : bodyWork k v≠(BodyIngress.machine k).reject :=
  (leafTerminal (k:=k) v).2
private theorem caller_work_row (k : Nat) (v : Bool) (b : Option Bool) :
    (PhysicalCallerClosure.callerMachine k).step (PhysicalCallerClosure.oldState k (bodyWork k v)) b=
      (PhysicalCallerClosure.oldState k (bodyWork k v),b,.stay) := by
  rw [PhysicalCallerClosure.old_rows k _ b (by
    intro mode
    exact entryDisjoint k (CarryWindow.embed k (CanonicalLeaf.result k v)) mode)]
  rw [body_work_row k v b]
private theorem chain_row (A L G : UniformTM) (q : Fin A.stateCount) (b : Option Bool) :
    (L.seq (G.seq (L.seq A))).step (L.seqRight _ (G.seqRight _ (L.seqRight A q))) b=
      (L.seqRight _ (G.seqRight _ (L.seqRight A (A.step q b).1)),(A.step q b).2) := by
  rw [UniformTM.seq_step_right,UniformTM.seq_step_right,UniformTM.seq_step_right]
private theorem work_row (k : Nat) (v : Bool) (b : Option Bool) :
    (machine k).step (old k (work k v)) b=(old k (work k v),b,.stay) := by
  have eq:old k (work k v)=callerState k (PhysicalCallerClosure.oldState k (bodyWork k v)):=oldBody k _
  rw [eq]
  have h:=chain_row (PhysicalCallerClosure.callerMachine k) FixedPairParser.machine CertificateGuardClosure.guard
    (PhysicalCallerClosure.oldState k (bodyWork k v)) b
  rw [caller_work_row k v b] at h
  exact h
private theorem caller_injective (k : Nat) : Function.Injective (callerState k) := by
  intro s t eq
  exact FixedPairParser.machine.seqRight_injective _
    (CertificateGuardClosure.guard.seqRight_injective _ (FixedPairParser.machine.seqRight_injective _ eq))
private theorem caller_accept (k : Nat) : callerState k (PhysicalCallerClosure.callerMachine k).accept=(machine k).accept := rfl
private theorem caller_reject (k : Nat) : callerState k (PhysicalCallerClosure.callerMachine k).reject=(machine k).reject := rfl
private theorem work_ne_reject (k : Nat) (v : Bool) : old k (work k v)≠(machine k).reject := by
  rw [show old k (work k v)=callerState k (PhysicalCallerClosure.oldState k (bodyWork k v)) from oldBody k _]
  intro bad
  have eq:=caller_injective k (bad.trans (caller_reject k).symm)
  exact body_work_terminal k v (oldInjective k eq)
private theorem caller_done_not_old (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) :
    PhysicalCallerClosure.oldState k s≠PhysicalCallerClosure.rowsDone k := by
  intro bad
  have vals:=congrArg Fin.val bad
  dsimp only [PhysicalCallerClosure.oldState,PhysicalCallerClosure.rowsDone,liftOld,native] at vals
  have bound:=s.isLt
  omega
private theorem work_ne_done (k : Nat) (v : Bool) : old k (work k v)≠callerState k (PhysicalCallerClosure.rowsDone k) := by
  rw [show old k (work k v)=callerState k (PhysicalCallerClosure.oldState k (bodyWork k v)) from oldBody k _]
  intro eq
  exact caller_done_not_old k _ (caller_injective k eq)
private theorem old_not_done (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) :
    old k s≠callerState k (PhysicalCallerClosure.rowsDone k) := by
  intro bad
  have vals:=congrArg Fin.val bad
  dsimp only [old,callerState,UniformTM.seqRight,PhysicalCallerClosure.rowsDone,native] at vals
  have bound:=s.isLt
  change s.val < 10+(67+(10+(BodyIngress.machine k).stateCount)) at bound
  omega
private theorem row_fixed (M : UniformTM) (q : Fin M.stateCount)
    (row:∀ b,M.step q b=(q,b,.stay)) {N B : Nat}
    (c : Config M.stateCount N B) (atWork:c.state=q) : ∀ t,M.run t c=c := by
  have step:M.stepConfig c=c:=by
    apply Config.ext_parts
    · change (M.step c.state (c.tape c.head)).1=c.state
      rw [atWork,row]
    · apply Fin.ext
      change (moveHead c.head (M.step c.state (c.tape c.head)).2.2).val=c.head.val
      rw [atWork,row];rfl
    · funext i
      dsimp only [UniformTM.stepConfig]
      rw [atWork,row]
      by_cases eq:i=c.head
      · subst i;rw [if_pos rfl]
      · rw [if_neg eq]
  intro t
  induction t with
  | zero=>rfl
  | succ t ih=>rw [UniformTM.run,ih,step]
private theorem no_work_to_finish (k : Nat) {N B t : Nat} (c : Config (machine k).stateCount N B)
    (finish:((machine k).run t c).state=(machine k).reject ∨
      ((machine k).run t c).state=callerState k (PhysicalCallerClosure.rowsDone k)) :
    ∀ u,u≤t → ∀ v,((machine k).run u c).state≠old k (work k v) := by
  intro u hu v bad
  have fixed:=row_fixed (machine k) (old k (work k v)) (work_row k v) ((machine k).run u c) bad (t-u)
  rw [←UniformTM.run_add,show u+(t-u)=t by omega] at fixed
  have atWork:((machine k).run t c).state=old k (work k v):=(congrArg Config.state fixed).trans bad
  rcases finish with h|h
  · exact work_ne_reject k v (atWork.symm.trans h)
  · exact work_ne_done k v (atWork.symm.trans h)
end RawCallerClosure
