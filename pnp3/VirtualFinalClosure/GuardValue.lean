import VirtualFinalClosure.GuardDriver
namespace VirtualFinalClosure.GuardValue
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardDriver","VirtualFinalClosure.GuardDriver","value","value",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
private theorem affine (bits : Nat → Bool) (S h ell i : Nat) :
    value bits S h ell i=i*2^ell+value bits S h ell 0 := by
  induction ell generalizing h i with
  | zero=>simp only [value,Nat.pow_zero,Nat.mul_one,Nat.add_zero]
  | succ ell ih=>
    dsimp only [value]
    rw [ih (min (h+1) S) (2*i+(if h < S ∧ bits h=true then 1 else 0)),
      ih (min (h+1) S) (2*0+(if h < S ∧ bits h=true then 1 else 0)),Nat.pow_succ]
    ring
private theorem next_min (S h : Nat) : min (min h S+1) S=min (h+1) S:=by omega
private theorem physical_bit {S : Nat} (z : Bitstring S) (h : Nat) :
    (if min h S < S ∧ padRead z (min h S)=true then 1 else 0)=(if padRead z h then 1 else 0) := by
  by_cases inside : h < S
  · rw [Nat.min_eq_left inside.le]
    simp only [inside,true_and]
  · have bit : padRead z h=false:=by dsimp only [padRead];rw [dif_neg (by omega)]
    rw [Nat.min_eq_right (by omega),if_neg (by omega),bit]
    simp only [Bool.false_eq_true,if_false]
/-- The accumulator actually computed by the native BE loop agrees with the
AUTHORITATIVE strict BE reader on the complete padded convention window.
The source uses BIG-endian active index bits; no LE assignment convention enters. -/
private theorem read {S M : Nat} (z : Bitstring S) (offset width : Nat) (fit : offset+width ≤ M) :
    readNatBE (padWord z M) offset width=
      some (value (padRead z) S (min offset S) width 0) := by
  induction width generalizing offset with
  | zero=>rfl
  | succ width ih=>
    have pos : offset < M:=by omega
    have rest:=ih (offset+1) (by omega)
    rw [readNatBE,readBit?,dif_pos pos,rest]
    apply congrArg some
    have zero : 2*0=0:=rfl
    have form:=affine (padRead z) S (min (min offset S+1) S) width
      (2*0+(if min offset S < S ∧ padRead z (min offset S)=true then 1 else 0))
    change (if padRead z offset then 2^width else 0)+
      value (padRead z) S (min (offset+1) S) width 0=
      value (padRead z) S (min (min offset S+1) S) width
        (2*0+(if min offset S < S ∧ padRead z (min offset S)=true then 1 else 0))
    rw [form,next_min,physical_bit z offset]
    cases padRead z offset <;> simp
#print axioms affine
#print axioms next_min
#print axioms physical_bit
#print axioms read
end VirtualFinalClosure.GuardValue
