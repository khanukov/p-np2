import VirtualFinalClosure.WeightTailResources
import VirtualFinalClosure.CapMeaning
namespace VirtualFinalClosure.TightPrices
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","horizon","horizon"),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","phase_price","weightPrice"),
      ("VirtualFinalClosure.WeightTailResources","VirtualFinalClosure.WeightTailResources","post_price","postPrice"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","weight_bound","weightBound"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","one_le_power","oneLe"),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","weight_lower","weightLower")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact tight-driver price term {mod}/{key}"
private theorem length_price (k R n C a : Nat) (nr : n ≤ R)
    (cost : a ≤ (bitLength n-C+1)*(8192*(3*R+2+10*Cursor.Target.W k n+n+9)^2)) :
    a ≤ 1073741824*(k+1)^3*(R+1)^(3*k+3):=by
  have w:=weightBound k R n nr
  have ell:= (weightLower k n).1
  have d:=(horizon k R n nr).2
  have one:=oneLe R (k+1)
  have scale : 1 ≤ (k+1)*(R+1)^(k+1):=by nlinarith only [one,Nat.zero_le k]
  have count : bitLength n-C+1 ≤ 5*(k+1)*(R+1)^(k+1):=by
    have sub:=Nat.sub_le (bitLength n) C
    nlinarith only [sub,w,ell,scale]
  have extent : 3*R+2+10*Cursor.Target.W k n+n+9 ≤ 128*(k+1)*(R+1)^(k+1):=by omega
  calc
    a ≤ (bitLength n-C+1)*(8192*(3*R+2+10*Cursor.Target.W k n+n+9)^2):=cost
    _ ≤ (5*(k+1)*(R+1)^(k+1))*(8192*(128*(k+1)*(R+1)^(k+1))^2):=
      Nat.mul_le_mul count (Nat.mul_le_mul_left 8192 (Nat.pow_le_pow_left extent 2))
    _ = 671088640*(k+1)^3*(R+1)^(3*k+3):=by
      rw [mul_pow,mul_pow,←pow_mul]
      ring_nf
    _ ≤ _:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
private theorem total (k R n C C0 C1 t a b u : Nat) (nr : n ≤ R)
    (initial : t ≤ 16777216*(R+1)^3)
    (capacity : C1 ≤ 2*Cursor.Target.W k n)
    (ap : a ≤ (bitLength n-C+1)*(8192*(3*R+2+10*Cursor.Target.W k n+n+9)^2))
    (bp : b ≤ (Cursor.Target.W k n-C0+1)*(4194304*(k+1)*(3*R+2+10*Cursor.Target.W k n+n+9)^3))
    (up : u ≤ 4096*(Cursor.Target.W k n+1)*(3*R+2+5*C1+n+8)^2) :
    t+a+b+u ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4):=by
  have aBound:=length_price k R n C a nr ap
  have bBound:=weightPrice k R n C0 b nr (bp.trans (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))))
  have uBound:=postPrice k R n C1 u nr (by omega) up
  have pn : (R+1)^(3*k+3) ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have pk : (k+1)^3 ≤ (k+1)^5:=Nat.pow_le_pow_right (by omega) (by decide)
  have aScaled:=aBound.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 1073741824 pk) pn)
  have uScaled:=uBound.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 536870912 pk) pn)
  have basePower : (R+1)^3 ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have kOne : 1 ≤ (k+1)^5:=by simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0 < k+1) (show 0 ≤ 5 by decide)
  have tScaled:=initial.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 16777216 kOne) basePower)
  nlinarith only [aScaled,bBound,uScaled,tScaled,Nat.zero_le ((k+1)^5*(R+1)^(4*k+4))]
#print axioms length_price
#print axioms total
end VirtualFinalClosure.TightPrices
