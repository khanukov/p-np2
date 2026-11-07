import VirtualFinalClosure.Finite
namespace VirtualFinalClosure.FirstLiteral
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
/-- Ordinary bounded induction selects the real first literal verdict while
preserving its WHOLE absorbing Config. No runtime clock, choice or finder is
constructed, and this lemma is never used to pad a live work handoff. -/
private theorem first (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B) (T : Nat) :
    ∃ t,t ≤ T ∧ (∀ u,u < t → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject) ∧
      M.run t c=M.run T c := by
  induction T with
  | zero=>exact ⟨0,le_rfl,by intro u hu;omega,rfl⟩
  | succ T ih=>
    by_cases accept : (M.run T c).state=M.accept
    · obtain ⟨t,le,before,equal⟩:=ih
      exact ⟨t,by omega,before,equal.trans (M.run_accept_of_le c accept (Nat.le_succ T)).symm⟩
    · by_cases reject : (M.run T c).state=M.reject
      · obtain ⟨t,le,before,equal⟩:=ih
        exact ⟨t,by omega,before,equal.trans (M.run_reject_of_le c reject (Nat.le_succ T)).symm⟩
      · exact ⟨T+1,le_rfl,fun u hu=>M.no_terminal_of_le c accept reject u (by omega),rfl⟩
#print axioms first
end VirtualFinalClosure.FirstLiteral
