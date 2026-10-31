import VirtualFinalClosure.GuardResources
namespace VirtualFinalClosure.FinalResources
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","weight_bound","weightBound"),
      ("VirtualFinalClosure.GuardResources","VirtualFinalClosure.GuardResources","phase_price","guardPrice")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact final resource proof {mod}/{key}"
private theorem room (k R : Nat) : spaceBound k R < tapeLength R (allocation k R):=by
  have pn : (R+1)^(k+3) ≤ (R+1)^(k+12):=Nat.pow_le_pow_right (by omega) (by omega)
  have pk : (k+1)^2 ≤ (k+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have lower : 281474976710656*(k+1)^2*(R+1)^(k+3) ≤ allocation k R:=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ pk) pn
  have positive : 1 ≤ (k+1)^2*(R+1)^(k+3):=by
    have pos : 0<(k+1)^2*(R+1)^(k+3):=by positivity
    omega
  dsimp only [spaceBound,tapeLength]
  simp only [Nat.mul_assoc] at lower ⊢
  omega
private theorem cleanup_price (k R n C H d : Nat) (nr : n ≤ R) (capacity : C ≤ 2*Cursor.Target.W k n)
    (price : d ≤ (3*R+2)-H+18*C+6*n+51) :
    d ≤ 256*(k+1)*(R+1)^(k+1):=by
  have wb:=weightBound k R n nr
  have rp : R+1 ≤ (R+1)^(k+1):=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<R+1) (show 1 ≤ k+1 by omega)
  have scale : R+1 ≤ (k+1)*(R+1)^(k+1):=rp.trans (by nlinarith only [Nat.zero_le k,Nat.zero_le ((R+1)^(k+1))])
  have sub:=Nat.sub_le (3*R+2) H
  nlinarith only [price,capacity,wb,nr,scale,sub]
private theorem total (k R n C s v d : Nat) (nr : n ≤ R) (capacity : C ≤ 2*Cursor.Target.W k n)
    (before : s ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4))
    (vp : v ≤ 1+((C+2)+(n+2))+(bitLength (Cursor.Target.W k n)+1)*(512*(C+1)^2+16*(3*R+2+C+n+8))+128*(3*R+2+C+n+8))
    (fits : bitLength (Cursor.Target.W k n) ≤ C)
    (dp : d ≤ (3*R+2)+18*C+6*n+51) : s+v+d ≤ deadline k R:=by
  have guard:=guardPrice k R n C (bitLength (Cursor.Target.W k n)) v nr (by omega) fits vp
  have clean:=cleanup_price k R n C 0 d nr capacity (by simpa only [Nat.sub_zero] using dp)
  have pk : (k+1)^3 ≤ (k+1)^5:=Nat.pow_le_pow_right (by omega) (by decide)
  have pn : (R+1)^(3*k+3) ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have gp:=guard.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2147483648 pk) pn)
  have kk : k+1 ≤ (k+1)^5:=by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 1 ≤ 5 by decide)
  have nn : (R+1)^(k+1) ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have cp:=clean.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 256 kk) nn)
  have sum : s+v+d ≤ 1125899906842624*(k+1)^5*(R+1)^(4*k+4):=by
    nlinarith only [before,gp,cp,Nat.zero_le ((k+1)^5*(R+1)^(4*k+4))]
  have k5 : (k+1)^5 ≤ (k+1)^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have n5 : (R+1)^(4*k+4) ≤ (R+1)^(4*k+24):=Nat.pow_le_pow_right (by omega) (by omega)
  exact sum.trans (Nat.mul_le_mul (Nat.mul_le_mul (by decide : 1125899906842624 ≤ 18446744073709551616) k5) n5)
private theorem small_price (k R t : Nat) (price : t ≤ 268435456*(k+1)*(R+1)^3) : t ≤ deadline k R:=by
  have pk : k+1 ≤ (k+1)^8:=by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 1 ≤ 8 by decide)
  have pn : (R+1)^3 ≤ (R+1)^(4*k+24):=Nat.pow_le_pow_right (by omega) (by omega)
  exact price.trans (Nat.mul_le_mul (Nat.mul_le_mul (by decide : 268435456 ≤ 18446744073709551616) pk) pn)
#print axioms room
#print axioms cleanup_price
#print axioms total
#print axioms small_price
end VirtualFinalClosure.FinalResources
