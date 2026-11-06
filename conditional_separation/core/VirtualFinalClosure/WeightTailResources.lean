import VirtualFinalClosure.WeightResources
namespace VirtualFinalClosure.WeightTailResources
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("Resources","weight_bound","weightBound"),("Resources","one_le_power","oneLePower"),("WeightResources","horizon","horizon")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private.VirtualFinalClosure."++mod++".") && name.toString.endsWith (".VirtualFinalClosure."++mod++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual W resource proof {key}"
private theorem post_price (k R n C t : Nat) (nr : n ≤ R)
    (capacity : C ≤ 2*(Cursor.Target.W k n+3*R+1))
    (price : t ≤ 4096*(Cursor.Target.W k n+1)*(3*R+2+5*C+n+8)^2) :
    t ≤ 536870912*(k+1)^3*(R+1)^(3*k+3) := by
  have w:=weightBound k R n nr
  have d:=(horizon k R n nr).2
  have one:=oneLePower R (k+1)
  have scale : 1 ≤ (k+1)*(R+1)^(k+1):=by nlinarith only [one,Nat.zero_le k]
  have count : Cursor.Target.W k n+1 ≤ 5*(k+1)*(R+1)^(k+1):=by nlinarith only [w,scale]
  have extent : 3*R+2+5*C+n+8 ≤ 128*(k+1)*(R+1)^(k+1):=by nlinarith only [d,capacity]
  calc
    t ≤ 4096*(Cursor.Target.W k n+1)*(3*R+2+5*C+n+8)^2:=price
    _ ≤ 4096*(5*(k+1)*(R+1)^(k+1))*(128*(k+1)*(R+1)^(k+1))^2:=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4096 count) (Nat.pow_le_pow_left extent 2)
    _ = 335544320*(k+1)^3*(R+1)^(3*k+3):=by rw [mul_pow,mul_pow,←pow_mul];ring_nf
    _ ≤ _:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
private theorem total_price (k R t d : Nat)
    (tp : t ≤ 281474976710656*(k+1)^5*(R+1)^(4*k+4))
    (dp : d ≤ 536870912*(k+1)^3*(R+1)^(3*k+3)) :
    t+d ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4) := by
  have pn : (R+1)^(3*k+3) ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have pk : (k+1)^3 ≤ (k+1)^5:=Nat.pow_le_pow_right (by omega) (by decide)
  have scaled:=dp.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 536870912 pk) pn)
  nlinarith only [tp,scaled,Nat.zero_le ((k+1)^5*(R+1)^(4*k+4))]
#print axioms post_price
#print axioms total_price
end VirtualFinalClosure.WeightTailResources
