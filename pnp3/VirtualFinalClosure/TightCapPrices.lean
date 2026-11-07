import VirtualFinalClosure.TightPrices
namespace VirtualFinalClosure.TightCapPrices
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.TightPrices","VirtualFinalClosure.TightPrices","length_price","lengthPrice"),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","phase_price","weightPrice"),
      ("VirtualFinalClosure.WeightTailResources","VirtualFinalClosure.WeightTailResources","post_price","postPrice")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual all-cap price term {mod}/{key}"
private theorem initial_price (k R n r t a b d e : Nat) (nr : n ≤ R) (rr : r ≤ R)
    (tp : t ≤ 4194304*(R+1)^3) (ap : a ≤ 16*(3*R+2+5*r+n+8))
    (bp : b ≤ 2097152*(k+1)*(n+r+1)^2*(3*R+2+5*r+n+9))
    (dp : d ≤ 64*(R+1)^2) (ep : e ≤ 128*(R+1)^2) :
    t+a+b+d+e ≤ 268435456*(k+1)*(R+1)^3:=by
  have extent : 3*R+2+5*r+n+9 ≤ 11*(R+1):=by omega
  have count : n+r+1 ≤ 2*(R+1):=by omega
  have bBound:=bp.trans (Nat.mul_le_mul
    (Nat.mul_le_mul_left (2097152*(k+1)) (Nat.pow_le_pow_left count 2)) extent)
  have one : 1 ≤ (k+1)*(R+1):=by nlinarith only [Nat.zero_le k,Nat.zero_le R]
  nlinarith only [tp,ap,bBound,dp,ep,one,nr,rr,Nat.zero_le k,Nat.zero_le R,
    Nat.zero_le (R^2),Nat.zero_le (R^3),Nat.zero_le (k*R),Nat.zero_le (k*R^2),Nat.zero_le (k*R^3)]
private theorem total (k R n C C0 C1 t a b u : Nat) (nr : n ≤ R)
    (initial : t ≤ 268435456*(k+1)*(R+1)^3) (capacity : C1 ≤ 2*Cursor.Target.W k n)
    (ap : a ≤ (bitLength n-C+1)*(8192*(3*R+2+10*Cursor.Target.W k n+n+9)^2))
    (bp : b ≤ (Cursor.Target.W k n-C0+1)*(4194304*(k+1)*(3*R+2+10*Cursor.Target.W k n+n+9)^3))
    (up : u ≤ 4096*(Cursor.Target.W k n+1)*(3*R+2+5*C1+n+8)^2) :
    t+a+b+u ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4):=by
  have aBound:=lengthPrice k R n C a nr ap
  have bBound:=weightPrice k R n C0 b nr (bp.trans (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))))
  have uBound:=postPrice k R n C1 u nr (by omega) up
  have pn : (R+1)^(3*k+3) ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have pk : (k+1)^3 ≤ (k+1)^5:=Nat.pow_le_pow_right (by omega) (by decide)
  have aScaled:=aBound.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 1073741824 pk) pn)
  have uScaled:=uBound.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 536870912 pk) pn)
  have pp : (R+1)^3 ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have kp : k+1 ≤ (k+1)^5:=by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < k+1) (show 1 ≤ 5 by decide)
  have tScaled:=initial.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 268435456 kp) pp)
  nlinarith only [aScaled,bBound,uScaled,tScaled,Nat.zero_le ((k+1)^5*(R+1)^(4*k+4))]
private theorem prefix_space (k R : Nat) : 256*(R+1)^2 ≤ spaceBound k R:=by
  have pn : (R+1)^2 ≤ (R+1)^(k+3):=Nat.pow_le_pow_right (by omega) (by omega)
  have coeff : 256 ≤ 1048576*(k+1)^2:=by nlinarith only [Nat.zero_le k,Nat.zero_le (k^2)]
  exact Nat.mul_le_mul coeff pn
#print axioms initial_price
#print axioms total
#print axioms prefix_space
end VirtualFinalClosure.TightCapPrices
