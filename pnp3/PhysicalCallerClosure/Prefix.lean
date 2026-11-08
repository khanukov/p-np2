import PhysicalCallerClosure.Rows
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
private theorem old_step {k N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (uncut:∀ mode : Fin 3,c.state≠BodyIngress.body k (SerializedBody.entry mode)) :
    (callerMachine k).stepConfig ⟨oldState k c.state,c.head,c.tape⟩=
      ⟨oldState k ((BodyIngress.machine k).stepConfig c).state,
        ((BodyIngress.machine k).stepConfig c).head,((BodyIngress.machine k).stepConfig c).tape⟩ := by
  unfold UniformTM.stepConfig
  dsimp only
  rw [old_rows k c.state (c.tape c.head) uncut]
/-- Actual same-budget every-prefix transport before the first of the three cuts. -/
theorem caller_prefix {k N B t : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (first : ∀ u,u<t → ∀ mode : Fin 3,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.entry mode)) :
    ∀ u,u≤t → (callerMachine k).run u ⟨oldState k c.state,c.head,c.tape⟩=
      ⟨oldState k ((BodyIngress.machine k).run u c).state,
        ((BodyIngress.machine k).run u c).head,((BodyIngress.machine k).run u c).tape⟩ := by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>rw [UniformTM.run,ih (by omega),old_step _ (first u (by omega)),UniformTM.run]
theorem caller_prefix_mirror :
    ∀ {k N B t : Nat} (c : Config (BodyIngress.machine k).stateCount N B),
    (∀ u,u<t → ∀ mode : Fin 3,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.entry mode)) →
    ∀ u,u≤t → (callerMachine k).run u ⟨oldState k c.state,c.head,c.tape⟩=
      ⟨oldState k ((BodyIngress.machine k).run u c).state,
        ((BodyIngress.machine k).run u c).head,((BodyIngress.machine k).run u c).tape⟩ := caller_prefix
private theorem eval_step {k N B : Nat} (c : Config SerializedBody.machine.stateCount N B)
    (work:4≤c.state.val) :
    (callerMachine k).stepConfig ⟨evalState k c.state,c.head,c.tape⟩=
      ⟨evalState k (SerializedBody.machine.stepConfig c).state,
        (SerializedBody.machine.stepConfig c).head,(SerializedBody.machine.stepConfig c).tape⟩ := by
  unfold UniformTM.stepConfig
  dsimp only
  rw [eval_rows k c.state (c.tape c.head) work]
/-- BODY callbacks are activated only after its actual first terminal arrival. -/
theorem eval_prefix {k N B t : Nat} (c : Config SerializedBody.machine.stateCount N B)
    (work : ∀ u,u<t → 4≤(SerializedBody.machine.run u c).state.val) :
    ∀ u,u≤t → (callerMachine k).run u ⟨evalState k c.state,c.head,c.tape⟩=
      ⟨evalState k (SerializedBody.machine.run u c).state,
        (SerializedBody.machine.run u c).head,(SerializedBody.machine.run u c).tape⟩ := by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>rw [UniformTM.run,ih (by omega),eval_step _ (work u (by omega)),UniformTM.run]
theorem eval_prefix_mirror :
    ∀ {k N B t : Nat} (c : Config SerializedBody.machine.stateCount N B),
    (∀ u,u<t → 4≤(SerializedBody.machine.run u c).state.val) →
    ∀ u,u≤t → (callerMachine k).run u ⟨evalState k c.state,c.head,c.tape⟩=
      ⟨evalState k (SerializedBody.machine.run u c).state,
        (SerializedBody.machine.run u c).head,(SerializedBody.machine.run u c).tape⟩ := eval_prefix
#print axioms caller_prefix
#print axioms caller_prefix_mirror
#print axioms eval_prefix
#print axioms eval_prefix_mirror
end PhysicalCallerClosure
