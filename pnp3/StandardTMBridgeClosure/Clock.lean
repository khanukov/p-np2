import StandardTMBridgeClosure.Target
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing
private theorem overhead (c N : Nat) : 1+2*polyClock c N ≤ polyClock (4*c+4) N := by
  by_cases zero:N=0
  · subst N
    by_cases cz:c=0
    · subst c;decide
    · have big:4*c+4≠0:=by omega
      simp only [polyClock,zero_pow cz,zero_pow big,Nat.zero_add]
      omega
  by_cases one:N=1
  · subst N;simp only [polyClock,one_pow];omega
  have two:2 ≤ N:=by omega
  have power:N^(c+1) ≤ N^(4*c+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have double:2*N^c ≤ N^(4*c+4):=by
    calc 2*N^c ≤ N*N^c:=Nat.mul_le_mul_right _ two
         _ = N^(c+1):=by rw [Nat.pow_succ];exact Nat.mul_comm _ _
         _ ≤ N^(4*c+4):=power
  unfold polyClock
  omega
/-- Exact boot/write/move overhead absorbed for every input length. -/
theorem degree_bound (k N : Nat) :
    1+2*polyClock (NormalClockClosure.degree k) N ≤ polyClock (degree k) N := overhead _ _
theorem degree_bound_full (k N : Nat) :
    1+2*(N^(4503599627370496*(k+1)+64)+(4503599627370496*(k+1)+64)) ≤
      N^(4*(4503599627370496*(k+1)+64)+4)+(4*(4503599627370496*(k+1)+64)+4) := degree_bound k N
/-- Fixed finite alphabet and finite labels; there is no hidden Nat register. -/
theorem finite_control (M : UniformTM) :
    Fintype.card (Bool × Option Bool)=6 ∧
    Fintype.card (Option (Fin M.stateCount × Fin 4))=1+4*M.stateCount := by
  constructor
  · decide
  · simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin]
    omega
theorem finite_control_full (M : UniformTM) :
    Fintype.card (Bool × Option Bool)=6 ∧
    Fintype.card (Option (Fin M.stateCount × Fin 4))=1+4*M.stateCount := finite_control M
/-- Explicit computable pullback to the original Boolean input language. -/
theorem encoding (x : List Bool) :
    (encode x).length=x.length ∧
    (encode x).map (fun a : Bool × Option Bool=>a.2.getD false)=x := by
  constructor
  · simp only [encode,List.length_map]
  · induction x with
    | nil=>rfl
    | cons b xs ih=>exact congrArg (List.cons b) ih

theorem encoding_full (x : List Bool) :
    (encode x).length=x.length ∧
    (encode x).map (fun a : Bool × Option Bool=>a.2.getD false)=x := encoding x
#print axioms degree_bound
#print axioms degree_bound_full
#print axioms finite_control
#print axioms finite_control_full
#print axioms encoding
#print axioms encoding_full
end StandardTMBridgeClosure
