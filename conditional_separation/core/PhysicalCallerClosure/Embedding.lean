import PhysicalCallerClosure.AmbientSurface
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
private theorem body_step (k N B : Nat) (c : Config SerializedBody.machine.stateCount N B) :
    (BodyIngress.machine k).stepConfig (BodyIngress.bodyConfig k c)=
      BodyIngress.bodyConfig k (SerializedBody.machine.stepConfig c) := by
  unfold UniformTM.stepConfig
  dsimp only [BodyIngress.bodyConfig]
  rw [BodyIngress.body_rows]
/-- Literal whole-configuration embedding into the actual combined ingress table. -/
theorem body_run (k N B t : Nat) (c : Config SerializedBody.machine.stateCount N B) :
    (BodyIngress.machine k).run t (BodyIngress.bodyConfig k c)=
      BodyIngress.bodyConfig k (SerializedBody.machine.run t c) := by
  induction t with
  | zero=>rfl
  | succ t ih=>rw [UniformTM.run,ih,body_step,UniformTM.run]
theorem body_run_mirror :
    ∀ (k N B t : Nat) (c : Config SerializedBody.machine.stateCount N B),
    (BodyIngress.machine k).run t
      ⟨BodyIngress.body k c.state,c.head,c.tape⟩=
      ⟨BodyIngress.body k (SerializedBody.machine.run t c).state,
        (SerializedBody.machine.run t c).head,(SerializedBody.machine.run t c).tape⟩ := body_run
private theorem body_injective (k : Nat) : Function.Injective (BodyIngress.body k) := by
  intro s t eq
  by_cases s0:s.val=0
  · have sEq:s=SerializedBody.machine.accept:=Fin.ext s0
    subst s
    by_cases t0:t.val=0
    · exact Fin.ext (by exact t0.symm)
    by_cases t1:t.val=1
    · have tEq:t=SerializedBody.machine.reject:=Fin.ext t1
      subst t
      have bad:=(congrArg Fin.val eq)
      change (CarryWindow.machine k).accept.val=(CarryWindow.machine k).reject.val at bad
      exact False.elim ((CarryWindow.machine k).accept_ne_reject (Fin.ext bad))
    · have small:=(CarryWindow.machine k).accept.isLt
      have bad:=congrArg Fin.val eq
      dsimp only [BodyIngress.body] at bad
      rw [if_neg t0,if_neg t1] at bad
      change (CarryWindow.machine k).accept.val=(CarryWindow.machine k).stateCount+t.val at bad
      omega
  by_cases s1:s.val=1
  · have sEq:s=SerializedBody.machine.reject:=Fin.ext s1
    subst s
    by_cases t1:t.val=1
    · exact Fin.ext (by exact t1.symm)
    by_cases t0:t.val=0
    · have tEq:t=SerializedBody.machine.accept:=Fin.ext t0
      subst t
      have bad:=congrArg Fin.val eq
      change (CarryWindow.machine k).reject.val=(CarryWindow.machine k).accept.val at bad
      exact False.elim ((CarryWindow.machine k).accept_ne_reject (Fin.ext bad.symm))
    · have small:=(CarryWindow.machine k).reject.isLt
      have bad:=congrArg Fin.val eq
      dsimp only [BodyIngress.body] at bad
      rw [if_neg t0,if_neg t1] at bad
      change (CarryWindow.machine k).reject.val=(CarryWindow.machine k).stateCount+t.val at bad
      omega
  by_cases t0:t.val=0
  · have tEq:t=SerializedBody.machine.accept:=Fin.ext t0
    subst t
    have small:=(CarryWindow.machine k).accept.isLt
    have bad:=congrArg Fin.val eq
    dsimp only [BodyIngress.body] at bad
    rw [if_neg s0,if_neg s1] at bad
    change (CarryWindow.machine k).stateCount+s.val=(CarryWindow.machine k).accept.val at bad
    omega
  by_cases t1:t.val=1
  · have tEq:t=SerializedBody.machine.reject:=Fin.ext t1
    subst t
    have small:=(CarryWindow.machine k).reject.isLt
    have bad:=congrArg Fin.val eq
    dsimp only [BodyIngress.body] at bad
    rw [if_neg s0,if_neg s1] at bad
    change (CarryWindow.machine k).stateCount+s.val=(CarryWindow.machine k).reject.val at bad
    omega
  apply Fin.ext
  have bad:=congrArg Fin.val eq
  dsimp only [BodyIngress.body] at bad
  rw [if_neg s0,if_neg s1,if_neg t0,if_neg t1] at bad
  change (CarryWindow.machine k).stateCount+s.val=(CarryWindow.machine k).stateCount+t.val at bad
  omega
#print axioms body_run
#print axioms body_run_mirror
end PhysicalCallerClosure
