import VirtualFinalClosure.Target
namespace VirtualFinalClosure.Wire
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for key in ["pack","count","rawStep","tailStep","oldStep","encodeMeta","changeMeta","resolve","flag","mode","phase","seen","bad"] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith "_private.VirtualFinalClosure.ElasticMachine." &&
      n.toString.endsWith (".VirtualFinalClosure.Elastic."++key)
    match found with
    | [(n,.defnInfo ci)]=>
      logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous ("wire_"++key)) n::st.openDecls}
    | _=>throwError "Nonunique actual native definition {key}"
private def pack_type : ∀ k,Nat → Nat → Fin (machine k).stateCount := wire_pack
private def tail_type : Nat → Nat → Nat → Option Bool → Nat × Nat × Option Bool × Move := wire_tailStep
private def raw_type : ∀ k,Fin (machine k).stateCount → Option Bool →
    Fin (machine k).stateCount × Option Bool × Move := wire_rawStep
private theorem pack_value (k q m : Nat)
    (hq : q < (CertificateGuardClosure.machine k).stateCount+239) (hm : m < 144) :
    (wire_pack k q m).val=144*q+m := by
  change (144*q+m)%(144*((CertificateGuardClosure.machine k).stateCount+239))=144*q+m
  exact Nat.mod_eq_of_lt (by omega)
private theorem pack_div (k q m : Nat)
    (hq : q < (CertificateGuardClosure.machine k).stateCount+239) (hm : m < 144) :
    (wire_pack k q m).val/144=q ∧ (wire_pack k q m).val%144=m := by
  rw [pack_value k q m hq hm]
  omega
private theorem terminal_values (k : Nat) :
    (machine k).accept.val=144*(CertificateGuardClosure.machine k).accept.val+8 ∧
    (machine k).reject.val=144*(CertificateGuardClosure.machine k).reject.val+8 := by
  constructor
  · exact pack_value k _ 8 (by have h:=(CertificateGuardClosure.machine k).accept.isLt;omega) (by decide)
  · exact pack_value k _ 8 (by have h:=(CertificateGuardClosure.machine k).reject.isLt;omega) (by decide)
/-- Literal native row expansion, including the actual terminal normalizer.
This lemma executes no host controller and assumes no prepared arithmetic result. -/
private theorem native_step (k q m : Nat) (b : Option Bool) (hq : q < 239) (hm : m < 144) :
    (machine k).step (wire_pack k ((CertificateGuardClosure.machine k).stateCount+q) m) b=
      (let a:=wire_tailStep k q m b
       (wire_pack k a.1
          (if a.1=(CertificateGuardClosure.machine k).accept.val ∨
              a.1=(CertificateGuardClosure.machine k).reject.val then 8 else a.2.1),a.2.2)) := by
  let O:=CertificateGuardClosure.machine k
  have bound : O.stateCount+q < O.stateCount+239 := by omega
  have hv:=pack_value k (O.stateCount+q) m bound hm
  have div:=pack_div k (O.stateCount+q) m bound hm
  have av:=O.accept.isLt
  have rv:=O.reject.isLt
  have terms:=terminal_values k
  change (machine k).accept.val=144*O.accept.val+8 ∧ (machine k).reject.val=144*O.reject.val+8 at terms
  have ha : wire_pack k (O.stateCount+q) m ≠ (machine k).accept := by
    apply Fin.ne_of_val_ne
    rw [hv,terms.1]
    omega
  have hr : wire_pack k (O.stateCount+q) m ≠ (machine k).reject := by
    apply Fin.ne_of_val_ne
    rw [hv,terms.2]
    omega
  rw [UniformTM.step_of_ne (M:=machine k) (q:=wire_pack k (O.stateCount+q) m) ha hr b]
  change wire_rawStep k (wire_pack k (O.stateCount+q) m) b=_
  dsimp only [wire_rawStep]
  rw [div.1,div.2,if_neg (by omega : ¬O.stateCount+q < O.stateCount)]
  rw [show O.stateCount+q-O.stateCount=q by omega]
  rfl
#print axioms pack_type
#print axioms tail_type
#print axioms raw_type
#print axioms pack_value
#print axioms pack_div
#print axioms terminal_values
#print axioms native_step
end VirtualFinalClosure.Wire
