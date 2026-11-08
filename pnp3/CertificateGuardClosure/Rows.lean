import CertificateGuardClosure.Machine
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1
/-- Every sealed ingress row, including its existing repaired producer row and
both literal absorbing verdicts, is retained under a genuine injective inclusion. -/
theorem component_rows (k : Nat) :
    Function.Injective (old k) ∧
    old k (TotalIngressClosure.machine k).accept=(machine k).accept ∧
    old k (TotalIngressClosure.machine k).reject=(machine k).reject ∧
    ∀ (s:Fin (TotalIngressClosure.machine k).stateCount) (b:Option Bool),
      (machine k).step (old k s) b=
        (old k (((TotalIngressClosure.machine k).step s b).1),((TotalIngressClosure.machine k).step s b).2) := by
  refine ⟨?_,rfl,rfl,?_⟩
  · intro a b h
    exact guard.seqRight_injective (TotalIngressClosure.machine k)
      (FixedPairParser.machine.seqRight_injective (guard.seq (TotalIngressClosure.machine k)) h)
  · intro s b
    change (FixedPairParser.machine.seq (guard.seq (TotalIngressClosure.machine k))).step
      (FixedPairParser.machine.seqRight (guard.seq (TotalIngressClosure.machine k)) (guard.seqRight (TotalIngressClosure.machine k) s)) b=_
    rw [UniformTM.seq_step_right,UniformTM.seq_step_right]
    rfl
end CertificateGuardClosure
