import VirtualFinalClosure.WeightResources
namespace VirtualFinalClosure.GuardResources
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("horizon","horizon")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.WeightResources." && name.toString.endsWith (".VirtualFinalClosure.WeightResources."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual W resource proof {key}"
private theorem cube_price (D C F n ell t : Nat) (positive : 1 ≤ D)
    (c : C+1 ≤ D) (x : F+C+n+8 ≤ D) (e : ell+1 ≤ D)
    (price : t ≤ 1+((C+2)+(n+2))+(ell+1)*(512*(C+1)^2+16*(F+C+n+8))+128*(F+C+n+8)) :
    t ≤ 1024*D^3 := by
  have square : (C+1)^2 ≤ D^2:=Nat.pow_le_pow_left c 2
  have middle : (ell+1)*(512*(C+1)^2+16*(F+C+n+8)) ≤ D*(512*D^2+16*D):=
    Nat.mul_le_mul e (Nat.add_le_add (Nat.mul_le_mul_left _ square) (Nat.mul_le_mul_left _ x))
  have one : D ≤ D^2:=by simpa only [Nat.mul_one,pow_two] using Nat.mul_le_mul_left D positive
  have two : D^2 ≤ D^3:=by
    calc
      D^2 = D^2*1:=(Nat.mul_one _).symm
      _ ≤ D^2*D:=Nat.mul_le_mul_left _ positive
      _ = D^3:=(pow_succ D 2).symm
  nlinarith only [price,middle,c,x,one,two,positive]
private theorem phase_price (k R n C ell t : Nat) (nr : n ≤ R)
    (cap : C ≤ 2*(Cursor.Target.W k n+3*R+1)) (ef : ell ≤ C)
    (price : t ≤ 1+((C+2)+(n+2))+(ell+1)*(512*(C+1)^2+16*(3*R+2+C+n+8))+128*(3*R+2+C+n+8)) :
    t ≤ 2147483648*(k+1)^3*(R+1)^(3*k+3) := by
  let D:=3*R+2+10*(Cursor.Target.W k n+3*R+1)+n+9
  have positivity : 1 ≤ D:=by dsimp only [D];omega
  have small:=cube_price D C (3*R+2) n ell t positivity
    (by dsimp only [D];omega) (by dsimp only [D];omega) (by dsimp only [D];omega) price
  have horizon:=(horizon k R n nr).2
  calc
    t ≤ 1024*D^3:=small
    _ ≤ 1024*(128*(k+1)*(R+1)^(k+1))^3:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left horizon 3)
    _ = _:=by rw [mul_pow,mul_pow,←pow_mul];ring_nf
private theorem total_price (k R t d : Nat)
    (raw : t ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4))
    (tail : d ≤ 2147483648*(k+1)^3*(R+1)^(3*k+3)) :
    t+d ≤ deadline k R := by
  have pk : (k+1)^3 ≤ (k+1)^5:=Nat.pow_le_pow_right (by omega) (by decide)
  have pn : (R+1)^(3*k+3) ≤ (R+1)^(4*k+4):=Nat.pow_le_pow_right (by omega) (by omega)
  have small : d ≤ 2147483648*(k+1)^5*(R+1)^(4*k+4):=tail.trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ pk) pn)
  have sum : t+d ≤ 1125899906842624*(k+1)^5*(R+1)^(4*k+4):=by
    nlinarith only [raw,small,Nat.zero_le ((k+1)^5*(R+1)^(4*k+4))]
  have kp : (k+1)^5 ≤ (k+1)^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have np : (R+1)^(4*k+4) ≤ (R+1)^(4*k+24):=Nat.pow_le_pow_right (by omega) (by omega)
  exact sum.trans (Nat.mul_le_mul
    (Nat.mul_le_mul (by decide : 1125899906842624 ≤ 18446744073709551616) kp) np)
#print axioms cube_price
#print axioms phase_price
#print axioms total_price
end VirtualFinalClosure.GuardResources
