import FullBodyClosure.Return
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1
/-- Proof-side composition of actual complete finite configurations; not runtime data. -/
def Native {N B : Nat} (t : Nat) (initial final : Config 7500 N B) : Prop :=
  SerializedBody.machine.run t initial=final ∧
    ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val
private def pin_Native : ∀ {N B : Nat},Nat → Config 7500 N B → Config 7500 N B → Prop :=
  (Native : ∀ {N B : Nat},Nat → Config 7500 N B → Config 7500 N B → Prop)
theorem native_trans {N B t s : Nat} {a b c : Config 7500 N B}
    (first : Native t a b) (second : Native s b c) : Native (t+s) a c := by
  rcases first with ⟨firstRun,firstBefore⟩
  rcases second with ⟨secondRun,secondBefore⟩
  constructor
  · rw [SerializedBody.machine.run_add,firstRun,secondRun]
  · intro u hu
    by_cases early : u < t
    · exact firstBefore u early
    · rw [show u=t+(u-t) by omega,SerializedBody.machine.run_add,firstRun]
      exact secondBefore (u-t) (by omega)
theorem native_trans_mirror :
    ∀ {N B t s : Nat} {a b c : Config 7500 N B},
    (SerializedBody.machine.run t a=b ∧ ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u a).state.val) →
    (SerializedBody.machine.run s b=c ∧ ∀ u,u < s → 4 ≤ (SerializedBody.machine.run u b).state.val) →
    SerializedBody.machine.run (t+s) a=c ∧
      ∀ u,u < t+s → 4 ≤ (SerializedBody.machine.run u a).state.val := native_trans
#print axioms FullBodyClosure.Native
#print axioms FullBodyClosure.pin_Native
#print axioms FullBodyClosure.native_trans
#print axioms FullBodyClosure.native_trans_mirror
end FullBodyClosure
