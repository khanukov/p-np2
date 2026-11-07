import StandardTMBridgeClosure.Simulation
import StandardTMBridgeClosure.Clock
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing
private def virtual (k : Nat) (b : Bool) := NormalFinalClosure.old2 k (RawCallerClosure.old k
    (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))))
private theorem virtual_fresh (k : Nat) (b : Bool) :
    virtual k b≠(NormalFinalClosure.machine2 k).accept ∧ virtual k b≠(NormalFinalClosure.machine2 k).reject := by
  have value:(virtual k b).val=87+(IngressRepair.machine k).stateCount+(if b then 7 else 6):=by
    change 10+(67+(10+((IngressRepair.machine k).stateCount+(if b then 7 else 6))))=_
    omega
  have accept:(NormalFinalClosure.machine2 k).accept.val=87+(IngressRepair.machine k).accept.val:=by
    change 10+(67+(10+(IngressRepair.machine k).accept.val))=_
    omega
  have reject:(NormalFinalClosure.machine2 k).reject.val=87+(IngressRepair.machine k).reject.val:=by
    change 10+(67+(10+(IngressRepair.machine k).reject.val))=_
    omega
  have ha:=(IngressRepair.machine k).accept.isLt
  have hr:=(IngressRepair.machine k).reject.isLt
  have positive:0 < (if b then 7 else 6 : Nat):=by cases b <;> decide
  constructor
  · intro eq
    have same:=congrArg Fin.val eq
    rw [value,accept] at same
    omega
  · intro eq
    have same:=congrArg Fin.val eq
    rw [value,reject] at same
    omega
private theorem ready_halt (M : UniformTM)
    (d : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)))
    (q : Fin M.stateCount) (label:d.q=some (q,0)) :
    TM0.step (compile M) d=none ↔ q=M.accept ∨ q=M.reject := by
  by_cases terminal:q=M.accept ∨ q=M.reject
  · simp [TM0.step,compile,label,terminal]
  · simp [TM0.step,compile,label,terminal]
/-- The counting iterator is a genuine actual trace in the pinned library
transition relation, not a replacement execution model. -/
theorem steps_reaches (M : UniformTM) (n : Nat)
    (a b : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)))
    (trace:steps M n a=some b) : TM0.Reaches (compile M) a b := by
  induction n generalizing a with
  | zero=>
    have eq:a=b:=Option.some.inj trace
    subst b
    exact Relation.ReflTransGen.refl
  | succ n ih=>
    cases edge:TM0.step (compile M) a with
    | none=>simp only [steps,edge,Option.bind_none] at trace;cases trace
    | some c=>
      have rest:steps M n c=some b:=by simpa only [steps,edge,Option.bind_some] using trace
      exact Relation.ReflTransGen.head edge (ih c rest)
theorem steps_reaches_full (M : UniformTM) (n : Nat)
    (a b : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)))
    (trace:steps M n a=some b) :
    Relation.ReflTransGen (fun s t=>t ∈ TM0.step (compile M) s) a b := steps_reaches M n a b trace
#print axioms steps_reaches
#print axioms steps_reaches_full
end StandardTMBridgeClosure
