import VirtualFinalClosure.GuardCross
import VirtualFinalClosure.GrowthCycle
import VirtualFinalClosure.RepeatEntry
namespace VirtualFinalClosure.GuardEntry
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardCross","VirtualFinalClosure.GuardCross","guardStart","guardStart",(1:Nat)),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","old_terminals",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","from_old_row","from_old_row",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual repeated-growth execution interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual repeated-growth execution interface {mod}/{key}"
private theorem row (k m : Nat) (hm : m < 144) (ph : phase m=1) :
    (machine k).step (control k (tableControl k (613+93*k)) ⟨m,hm⟩) none=(nc k 89 m,none,.stay) := by
  let i:=613+93*k
  let s:=tableControl k i
  have bound : i < Cursor.stateCount k:=by dsimp only [i];unfold Cursor.stateCount;omega
  have value:=tableValue k i bound
  have outside : s≠(CertificateGuardClosure.machine k).accept ∧ s≠(CertificateGuardClosure.machine k).reject:=by
    obtain ⟨av,rv⟩:=old_terminals k
    constructor <;> intro equal <;> have same:=congrArg Fin.val equal
    · rw [av] at same
      change (tableControl k i).val=414 at same
      rw [value] at same;dsimp only [i] at same;omega
    · rw [rv] at same
      change (tableControl k i).val=415 at same
      rw [value] at same;dsimp only [i] at same;omega
  have different (j : Nat) (bj : j < Cursor.stateCount k) (neq : i≠j) : s≠tableControl k j:=by
    intro equal
    have same:=congrArg Fin.val equal
    change (tableControl k i).val=(tableControl k j).val at same
    rw [value,tableValue k j bj] at same;omega
  have leaves : ¬(s=leafControl k false ∨ s=leafControl k true):=by
    have ne (b : Bool) : s≠leafControl k b:=by
      intro equal
      have same:=congrArg Fin.val equal
      change (tableControl k i).val=(leafControl k b).val at same
      rw [value,leafValue] at same
      unfold Cursor.stateCount at same
      dsimp only [i] at same;cases b <;> omega
    exact fun h=>h.elim (ne false) (ne true)
  have raw : oldRow k s.val m none=((CertificateGuardClosure.machine k).stateCount+89,m,none,.stay):=by
    have hs : (⟨s.val%(CertificateGuardClosure.machine k).stateCount,
        Nat.mod_lt _ (by have h:=(CertificateGuardClosure.machine k).start.isLt;omega)⟩ :
        Fin (CertificateGuardClosure.machine k).stateCount)=s:=Fin.ext (Nat.mod_eq_of_lt s.isLt)
    dsimp only [oldRow]
    rw [hs,if_neg leaves,if_neg (by
      intro h
      rcases h.2.2 with h|h
      · exact different 250 (by unfold Cursor.stateCount;omega) (by dsimp only [i];omega) h
      · exact different 304 (by unfold Cursor.stateCount;omega) (by dsimp only [i];omega) h)]
    rw [if_neg (fun h=>different (798+93*k) (by unfold Cursor.stateCount;omega) (by dsimp only [i];omega) h.2.2)]
    rw [if_neg (fun h=>different (430+93*k) (by unfold Cursor.stateCount;omega) (by dsimp only [i];omega) h.2)]
    rw [if_pos ⟨ph,rfl,rfl⟩]
  exact from_old_row k s m 89 hm (by decide) outside raw
/-- Literal live q613 NONE handoff, then crosses the observed capacity bank0
and actual n-wide bank1 to the native BE ellDec entry. No head retag occurs. -/
private theorem path (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (ph : phase m=1) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P (1+((width+2)+(n+2)))
      (node (control k (tableControl k (613+93*k)) ⟨m,hm⟩) (F+1) T)
      (C k 93 m (F+width+n+3) T) := by
  have enter:=keep (M:=machine k) (P:=P) (control k (tableControl k (613+93*k)) ⟨m,hm⟩)
    (nc k 89 m) (F+1) (F+1) T .stay (by omega) (by omega)
    (by
      have at0 : T (F+1)=none:=blank 0 (by decide)
      rw [at0];exact row k m hm ph) rfl
  have cross:=guardStart k P m F width n T hm fit blank occupied
  exact joinPath enter cross
#print axioms row
#print axioms path
end VirtualFinalClosure.GuardEntry
