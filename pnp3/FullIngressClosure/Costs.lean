import FullIngressClosure.Target
namespace FullIngressClosure
/-- Exact sum of the fourteen charged segments of one literal clone round. -/
theorem clone_sum (a b c : Nat) :
    1+(a+(1+(b+(1+(c+(1+(1+(c+(1+(b+(1+(a+(1)))))))))))))=2*a+2*c+2*b+8 := by omega
theorem check_clone_sum (a b c : Nat) :
    1+(a+(1+(b+(1+(c+(1+(1+(c+(1+(b+(1+(a+(1)))))))))))))=2*a+2*c+2*b+8 := by
  exact clone_sum a b c
/-- Count of distinct delimiter hops, derived from their literal strict order. -/
theorem discrete_span (D : Nat → Nat) (a b : Nat) (ab : a ≤ b)
    (rise : ∀ j,a ≤ j → j < b → D j < D (j+1)) : b-a ≤ D b-D a := by
  have grow : ∀ d,a+d ≤ b → D a+d ≤ D (a+d) := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.add_zero]; exact le_rfl
    | succ d ih =>
      intro hd
      have old:=ih (by omega)
      have step:=rise (a+d) (by omega) (by omega)
      rw [show a+d+1=a+(d+1) by omega] at step
      omega
  have bound:=grow (b-a) (by omega)
  rw [show a+(b-a)=b by omega] at bound
  omega
theorem check_discrete_span (D : Nat → Nat) (a b : Nat) (ab : a ≤ b)
    (rise : ∀ j,a ≤ j → j < b → D j < D (j+1)) : b-a ≤ D b-D a := by
  exact discrete_span D a b ab rise
end FullIngressClosure
