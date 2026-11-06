import VirtualFinalClosure.ReferenceCut
namespace VirtualFinalClosure.InertCut
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let found:=(← getEnv).constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.ReferenceCut." && name.toString.endsWith ".VirtualFinalClosure.ReferenceCut.first_event"
  match found with
  | [(name,.thmInfo ci)]=>
    logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `firstEvent name::st.openDecls}
  | _=>throwError "Nonunique ordinary first-event induction"
private theorem step_fixed (M : UniformTM) (q : Fin M.stateCount)
    (rows : ∀ b,M.step q b=(q,b,.stay)) {N B : Nat} (c : Config M.stateCount N B)
    (atQ : c.state=q) : M.stepConfig c=c:=by
  apply Config.ext_parts
  · change (M.step c.state (c.tape c.head)).1=c.state
    rw [atQ,rows]
  · change moveHead c.head (M.step c.state (c.tape c.head)).2.2=c.head
    rw [atQ,rows]
    rfl
  · funext i
    change (if i=c.head then (M.step c.state (c.tape c.head)).2.1 else c.tape i)=c.tape i
    rw [atQ,rows]
    by_cases hit : i=c.head
    · rw [if_pos hit,hit]
    · rw [if_neg hit]
private theorem run_fixed (M : UniformTM) (q : Fin M.stateCount)
    (rows : ∀ b,M.step q b=(q,b,.stay)) {N B : Nat} (c : Config M.stateCount N B)
    (atQ : c.state=q) (t : Nat) : M.run t c=c:=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change M.stepConfig (M.run t c)=c
    rw [ih]
    exact step_fixed M q rows c atQ
/-- Activate an OLD inert work control at its ACTUAL first arrival, retaining
its entire Config. Existence is proof-only ordinary induction; runtime has no
observer, supplied elapsed value or time-dependent transition. -/
private theorem first (M : UniformTM) (q : Fin M.stateCount)
    (rows : ∀ b,M.step q b=(q,b,.stay)) {N B : Nat} (c : Config M.stateCount N B)
    (t : Nat) (atQ : (M.run t c).state=q) :
    ∃ s,s ≤ t ∧ M.run s c=M.run t c ∧
      ∀ u,u < s → (M.run u c).state≠q:=by
  obtain ⟨s,st,hit,before⟩:=firstEvent c (fun d=>d.state=q) t atQ
  refine ⟨s,st,?_,before⟩
  have fixed:=run_fixed M q rows (M.run s c) hit (t-s)
  rw [show t=s+(t-s) by omega,M.run_add,fixed]
#print axioms step_fixed
#print axioms run_fixed
#print axioms first
end VirtualFinalClosure.InertCut
