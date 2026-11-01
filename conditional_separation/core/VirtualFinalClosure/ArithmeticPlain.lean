import VirtualFinalClosure.OldWire
import VirtualFinalClosure.InterceptRows
namespace VirtualFinalClosure.ArithmeticPlain
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",(1:Nat)),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual replay-mode row interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual replay-mode row interface {mod}/{key}"
private theorem body_minimum (k : Nat) (j : Fin 3) : 704 < (bodyControl k j).val := by
  fin_cases j
  · change 704 < 10+(67+(10+((288+Cursor.stateCount k+8+25)+4)))
    unfold Cursor.stateCount
    omega
  · change 704 < 10+(67+(10+((288+Cursor.stateCount k+8+25)+5)))
    unfold Cursor.stateCount
    omega
  · change 704 < 10+(67+(10+((288+Cursor.stateCount k+8+25)+6)))
    unfold Cursor.stateCount
    omega
/-- Literal replay region through q329, excluding the two live length-cap
entries. All modes are covered; active dispatch is proved absent row by row. -/
private theorem old_plain (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (m : Nat) (b : Option Bool) (lower : 473 ≤ s.val) (upper : s.val < 704)
    (no250 : s≠tableControl k 250) (no304 : s≠tableControl k 304)
    (after : 473 ≤ ((CertificateGuardClosure.machine k).step s b).1.val ∧
      ((CertificateGuardClosure.machine k).step s b).1.val ≤ 704) :
    oldRow k s.val m b=(((CertificateGuardClosure.machine k).step s b).1.val,m,
      ((CertificateGuardClosure.machine k).step s b).2.1,((CertificateGuardClosure.machine k).step s b).2.2) := by
  let O:=CertificateGuardClosure.machine k
  have hs : (⟨s.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=s :=
    Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have leaves : ¬(s=leafControl k false ∨ s=leafControl k true) := by
    have notLeaf (v : Bool) : s≠leafControl k v := by
      intro equal
      have same:=congrArg Fin.val equal
      rw [leafValue] at same
      unfold Cursor.stateCount at same
      cases v <;> omega
    exact fun h=>h.elim (notLeaf false) (notLeaf true)
  have notSpecial (i : Nat) (large : 329 ≤ i) (bound : i < Cursor.stateCount k) : s≠tableControl k i := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [tableValue k i bound] at values
    omega
  have not430:=notSpecial (430+93*k) (by omega) (by unfold Cursor.stateCount;omega)
  have not613:=notSpecial (613+93*k) (by omega) (by unfold Cursor.stateCount;omega)
  dsimp only [oldRow]
  rw [hs,if_neg leaves]
  rw [if_neg (by intro h;rcases h.2.2 with h|h;exact no250 h;exact no304 h)]
  rw [if_neg (fun h=>notSpecial (798+93*k) (by omega) (by unfold Cursor.stateCount;omega) h.2.2)]
  rw [if_neg (fun h=>not430 h.2),if_neg (fun h=>not613 h.2.2)]
  have noBody : ¬∃ j : Fin 3,(O.step s b).1=bodyControl k j := by
    rintro ⟨j,equal⟩
    have values:=congrArg Fin.val equal
    have high:=body_minimum k j
    have small : (O.step s b).1.val ≤ 704 := after.2
    omega
  rw [if_neg noBody]
  have noPaid (i : Nat) (small : i < 98) : s≠tableControl k i := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [tableValue k i (by unfold Cursor.stateCount;omega)] at values
    omega
  rw [if_neg (fun h=>noPaid 43 (by decide) h.2),
    if_neg (fun h=>noPaid 47 (by decide) h.2),if_neg (fun h=>noPaid 51 (by decide) h.2)]
/-- Actual SAME-machine effective row with UNCHANGED finite metadata. This is
proved for all finite modes; it does not assume a passive flag projection. -/
private theorem step_plain (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (m : Nat) (b : Option Bool) (hm : m < 144) (lower : 473 ≤ s.val) (upper : s.val < 704)
    (no250 : s≠tableControl k 250) (no304 : s≠tableControl k 304)
    (after : 473 ≤ ((CertificateGuardClosure.machine k).step s b).1.val ∧
      ((CertificateGuardClosure.machine k).step s b).1.val ≤ 704) :
    (machine k).step (control k s ⟨m,hm⟩) b=
      (control k ((CertificateGuardClosure.machine k).step s b).1 ⟨m,hm⟩,
        ((CertificateGuardClosure.machine k).step s b).2) := by
  have terms:=oldTerminals k
  have noAccept : s≠(CertificateGuardClosure.machine k).accept := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [terms.1] at values
    omega
  have noReject : s≠(CertificateGuardClosure.machine k).reject := by
    intro equal
    have values:=congrArg Fin.val equal
    rw [terms.2] at values
    omega
  have notFinal : ¬(((CertificateGuardClosure.machine k).step s b).1.val=(CertificateGuardClosure.machine k).accept.val ∨
      ((CertificateGuardClosure.machine k).step s b).1.val=(CertificateGuardClosure.machine k).reject.val) := by
    rw [terms.1,terms.2]
    omega
  rw [wire k s m b hm noAccept noReject,old_plain k s m b lower upper no250 no304 after]
  dsimp only
  rw [if_neg notFinal]
  rfl
#print axioms body_minimum
#print axioms old_plain
#print axioms step_plain
end VirtualFinalClosure.ArithmeticPlain
