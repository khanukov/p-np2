import VirtualFinalClosure.EventValues
import VirtualFinalClosure.CapEntry
namespace VirtualFinalClosure.InterceptRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","rawStep","raw",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_div","packDiv",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_value","packValue",1),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal original-cap intercept term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique literal original-cap intercept term {mod}/{key}"
private theorem old_terminals (k : Nat) :
    (CertificateGuardClosure.machine k).accept.val=414 ∧ (CertificateGuardClosure.machine k).reject.val=415 := by
  constructor
  · change 375+39%Cursor.stateCount k=414
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]
  · change 375+40%Cursor.stateCount k=415
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]
private theorem from_old_row (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (m q : Nat) (hm : m<144) (hq : q<239)
    (outside : s≠(CertificateGuardClosure.machine k).accept ∧ s≠(CertificateGuardClosure.machine k).reject)
    (row : oldRow k s.val m none=((CertificateGuardClosure.machine k).stateCount+q,m,none,.stay)) :
    (machine k).step (pack k s.val m) none=(nc k q m,none,.stay) := by
  let O:=CertificateGuardClosure.machine k
  have bound : s.val<O.stateCount+239 := s.isLt.trans_le (Nat.le_add_right O.stateCount 239)
  have div:=packDiv k s.val m bound hm
  have val:=packValue k s.val m bound hm
  have terminals:=terminalValues k
  have a : pack k s.val m≠(machine k).accept := by
    intro hit
    have same:=congrArg Fin.val hit
    rw [val,terminals.1] at same
    have eq:s=O.accept:=Fin.ext (by omega)
    exact outside.1 eq
  have r : pack k s.val m≠(machine k).reject := by
    intro hit
    have same:=congrArg Fin.val hit
    rw [val,terminals.2] at same
    have eq:s=O.reject:=Fin.ext (by omega)
    exact outside.2 eq
  rw [UniformTM.step_of_ne (machine k) a r none]
  change raw k (pack k s.val m) none=_
  dsimp only [raw]
  rw [div.1,div.2,if_pos s.isLt,row]
  have av:=O.accept.isLt
  have rv:=O.reject.isLt
  rw [if_neg (by omega : ¬(O.stateCount+q=O.accept.val ∨ O.stateCount+q=O.reject.val))]
  rfl
/-- The first live bitLength overflow row is actually executed into native0.
Both parity controls are covered; the head and scanned NONE are unchanged. -/
private theorem length_step (k i : Nat) (f : Fin 4) (which : i=250 ∨ i=304) :
    (machine k).step (control k (tableControl k i) ⟨8+f.val,by have h:=f.isLt;omega⟩) none=
      (nc k 0 (8+f.val),none,.stay) := by
  let s:=tableControl k i
  let m:=8+f.val
  have hm : m<144 := by have h:=f.isLt;dsimp only [m];omega
  have bound : i<Cursor.stateCount k := by rcases which with rfl|rfl <;> unfold Cursor.stateCount <;> omega
  have ph : phase m=0 := by fin_cases f <;> decide
  have outside : s≠(CertificateGuardClosure.machine k).accept ∧ s≠(CertificateGuardClosure.machine k).reject := by
    obtain ⟨av,rv⟩:=old_terminals k
    have value:=tableValue k i bound
    constructor <;> intro bad <;> have same:=congrArg Fin.val bad
    · rw [av] at same
      change (tableControl k i).val=414 at same
      rw [value] at same
      rcases which with rfl|rfl <;> omega
    · rw [rv] at same
      change (tableControl k i).val=415 at same
      rw [value] at same
      rcases which with rfl|rfl <;> omega
  have leaves : ¬(s=leafControl k false ∨ s=leafControl k true) := by
    have noLeaf (b : Bool) : s≠leafControl k b := by
      intro bad
      have same:=congrArg Fin.val bad
      change (tableControl k i).val=(leafControl k b).val at same
      rw [tableValue k i bound,leafValue] at same
      unfold Cursor.stateCount at same
      rcases which with rfl|rfl <;> cases b <;> omega
    exact fun h=>h.elim (noLeaf false) (noLeaf true)
  have row : oldRow k s.val m none=((CertificateGuardClosure.machine k).stateCount+0,m,none,.stay) := by
    have hs : (⟨s.val%(CertificateGuardClosure.machine k).stateCount,
        Nat.mod_lt _ (by have h:=(CertificateGuardClosure.machine k).start.isLt;omega)⟩ :
        Fin (CertificateGuardClosure.machine k).stateCount)=s := Fin.ext (Nat.mod_eq_of_lt s.isLt)
    dsimp only [oldRow]
    rw [hs,if_neg leaves,if_pos (by
      refine ⟨by omega,rfl,?_⟩
      rcases which with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr rfl)]
  exact from_old_row k s m 0 hm (by decide) outside row
#print axioms old_terminals
#print axioms from_old_row
#print axioms length_step
end VirtualFinalClosure.InterceptRows
