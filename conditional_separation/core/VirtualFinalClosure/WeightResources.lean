import VirtualFinalClosure.Resources
namespace VirtualFinalClosure.WeightResources
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("weight_bound","weightBound"),("one_le_power","oneLePower")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.Resources." && name.toString.endsWith (".VirtualFinalClosure.Resources."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual W resource proof {key}"
private theorem horizon (k R n : Nat) (nr : n ≤ R) :
    Cursor.Target.W k n+3*R+1 ≤ 8*(k+1)*(R+1)^(k+1) ∧
      3*R+2+10*(Cursor.Target.W k n+3*R+1)+n+9 ≤ 128*(k+1)*(R+1)^(k+1) := by
  have w:=weightBound k R n nr
  have p : R+1 ≤ (R+1)^(k+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<R+1) (show 1 ≤ k+1 by omega)
  have scale : R+1 ≤ (k+1)*(R+1)^(k+1):=p.trans (by nlinarith only [Nat.zero_le k,Nat.zero_le ((R+1)^(k+1))])
  constructor <;> nlinarith only [w,scale,nr]
private theorem room (k R n : Nat) (nr : n ≤ R) :
    3*R+2+10*(Cursor.Target.W k n+3*R+1)+n+7 < tapeLength R (allocation k R) := by
  have d:=(horizon k R n nr).2
  have pn : (R+1)^(k+1) ≤ (R+1)^(k+12):=Nat.pow_le_pow_right (by omega) (by omega)
  have pk : k+1 ≤ (k+1)^4:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 1 ≤ 4 by decide)
  have low : 128*(k+1)*(R+1)^(k+1) ≤ 128*(k+1)^4*(R+1)^(k+12):=
    Nat.mul_le_mul (Nat.mul_le_mul_left 128 pk) pn
  have positive :=oneLePower R (k+12)
  have kp : 1 ≤ (k+1)^4:=by
    simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 0 ≤ 4 by decide)
  dsimp only [tapeLength,allocation]
  have nonzero : 1 ≤ (k+1)^4*(R+1)^(k+12):=by nlinarith only [positive,kp]
  simp only [Nat.mul_assoc] at d low ⊢
  omega
private theorem phase_price (k R n C t : Nat) (nr : n ≤ R)
    (price : t ≤ (Cursor.Target.W k n-C+1)*(4194304*(k+1)*(3*R+2+10*(Cursor.Target.W k n+3*R+1)+n+9)^3)) :
    t ≤ 140737488355328*(k+1)^5*(R+1)^(4*k+4) := by
  have wb:=weightBound k R n nr
  have d:=(horizon k R n nr).2
  have pos:=oneLePower R (k+1)
  have kpos : 1 ≤ (k+1)*(R+1)^(k+1):=by nlinarith only [pos,Nat.zero_le k]
  have count : Cursor.Target.W k n-C+1 ≤ 5*(k+1)*(R+1)^(k+1) := by
    have small:=Nat.sub_le (Cursor.Target.W k n) C
    nlinarith only [small,wb,kpos]
  calc
    t ≤ (Cursor.Target.W k n-C+1)*(4194304*(k+1)*(3*R+2+10*(Cursor.Target.W k n+3*R+1)+n+9)^3):=price
    _ ≤ (5*(k+1)*(R+1)^(k+1))*(4194304*(k+1)*(128*(k+1)*(R+1)^(k+1))^3):=
      Nat.mul_le_mul count (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left d 3))
    _ = 43980465111040*(k+1)^5*(R+1)^(4*k+4):=by
      rw [mul_pow,mul_pow,←pow_mul]
      ring_nf
    _ ≤ _:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
private theorem heads (k R n L h : Nat) (nr : n ≤ R) (lr : L ≤ 2*R+2)
    (bound : h ≤ L+16*(3*R+2+10*(Cursor.Target.W k n+3*R+1)+n+8)) : h ≤ spaceBound k R := by
  have d:=(horizon k R n nr).2
  have p : R+1 ≤ (R+1)^(k+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<R+1) (show 1 ≤ k+1 by omega)
  have scale : R+1 ≤ (k+1)*(R+1)^(k+1):=p.trans (by nlinarith only [Nat.zero_le k,Nat.zero_le ((R+1)^(k+1))])
  have small : h ≤ 4096*(k+1)*(R+1)^(k+1):=by nlinarith only [bound,d,lr,scale]
  have pn : (R+1)^(k+1) ≤ (R+1)^(k+3):=Nat.pow_le_pow_right (by omega) (by omega)
  have hk : 4096*(k+1) ≤ 1048576*(k+1)^2:=by nlinarith only [Nat.zero_le k,Nat.zero_le (k^2)]
  exact small.trans (Nat.mul_le_mul hk pn)
#print axioms horizon
#print axioms room
#print axioms phase_price
#print axioms heads
end VirtualFinalClosure.WeightResources
