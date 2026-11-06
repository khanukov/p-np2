import TotalIngressClosure.CountdownHeads
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for key in ["guard_step","raw_rows"] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.IngressRepair.Transport." &&
      n.toString.endsWith (".IngressRepair."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous key) n::s.openDecls}
    | _=>throwError "Nonunique original repaired row {key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
/-- The repair can stop earlier but cannot invent a head address: after its
literal stay-reject the head is an actual earlier old head. -/
private theorem repair_head_origin (k : Nat) {N B : Nat}
    (c:Config (IngressRepair.machine k).stateCount N B) (t : Nat) :
    (IngressRepair.machine k).run t c=(AllArityCursor.machine k).run t c ∨
      (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject ∧
       ∃ u,u ≤ t ∧ ((IngressRepair.machine k).run t c).head=((AllArityCursor.machine k).run u c).head):=by
  induction t with
  | zero=>left;simp only [UniformTM.run]
  | succ t ih=>
    rcases ih with same | ⟨rejected,u,hu,head⟩
    · by_cases guard:((AllArityCursor.machine k).run t c).state.val=138 ∧
          ((AllArityCursor.machine k).run t c).tape ((AllArityCursor.machine k).run t c).head=none
      · right
        rw [UniformTM.run,same,guard_step k _ guard.1 guard.2]
        exact ⟨rfl,t,by omega,rfl⟩
      · left
        rw [UniformTM.run,same,UniformTM.run]
        have row:=raw_rows k _ _ guard
        simp only [UniformTM.stepConfig,row]
    · have stay: (IngressRepair.machine k).run (t+1) c=(IngressRepair.machine k).run t c:=
        (IngressRepair.machine k).run_reject_of_le c rejected (by omega)
      right
      rw [stay]
      exact ⟨rejected,u,by omega,head⟩
set_option maxRecDepth 4000 in
private theorem repaired_heads (k : Nat) {N B : Nat}
    (c:Config (IngressRepair.machine k).stateCount N B) (t P : Nat)
    (heads:∀ u,u ≤ t → ((AllArityCursor.machine k).run u c).head.val ≤ P) :
    ∀ u,u ≤ t → ((IngressRepair.machine k).run u c).head.val ≤ P:=by
  intro u hu
  rcases repair_head_origin k c u with same | ⟨_,v,hv,eq⟩
  · rw [same];exact heads u hu
  · rw [eq];exact heads v (hv.trans hu)
end TotalIngressClosure
