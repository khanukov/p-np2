import VirtualFinalClosure.LengthReplay
import VirtualFinalClosure.CapEntry
namespace VirtualFinalClosure.RepeatEntry
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",(0:Nat)),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","old_terminals",(1:Nat)),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","from_old_row","from_old_row",(1:Nat)),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",(1:Nat)),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",(1:Nat)),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","resolved_row","resolvedRow",(1:Nat)),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",(1:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",(0:Nat)),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",(0:Nat)),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",(0:Nat)),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",(0:Nat)),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","row0_0","row0_0",(1:Nat)),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","row1_0","row1_0",(1:Nat)),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","row1","row1",(1:Nat)),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","row2_0","row2_0",(1:Nat)),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","row3_0","row3_0",(1:Nat)),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","row3","row3",(1:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual replay-cap entry interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual replay-cap entry interface {mod}/{key}"
private theorem length_step (k i m : Nat) (hm : m < 144) (ph : phase m=1) (which : i=250 ∨ i=304) :
    (machine k).step (control k (tableControl k i) ⟨m,hm⟩) none=(nc k 0 m,none,.stay) := by
  let s:=tableControl k i
  have bound : i<Cursor.stateCount k := by rcases which with rfl|rfl <;> unfold Cursor.stateCount <;> omega
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
/-- Phase1 takes the literal grow/reset edge and does NOT rescan or overwrite
its saved source hole. Phase0's marker path is deliberately not reused. -/
private theorem row4 (k m : Nat) (hm : m < 144) (ph : phase m=1) :
    (machine k).step (nc k 4 m) none=(nc k 52 m,none,.stay) := by
  have resolution : resolveCode k 240 (changeMode 0 m)=(CertificateGuardClosure.machine k).stateCount+52 := by
    rw [mode0 m hm]
    change _+(if phase m=1 then 52 else 5)=_
    rw [if_pos ph]
  have r:=resolvedRow k 4 m 240 52 0 1 0 none (by decide) hm (by run_tac cellTac 12) resolution
  rw [mode0 m hm] at r
  exact r
private theorem from_d0 (k P F m : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (ph : phase m=1) (fit : F+1 ≤ P) (d0 : T (F+1)=none) :
    GPath (M:=machine k) P 1 (C k 4 m (F+1) T) (C k 52 m (F+1) T) := by
  exact keep (M:=machine k) (P:=P) (nc k 4 m) (nc k 52 m) (F+1) (F+1) T .stay
    fit fit (by rw [d0];exact row4 k m hm ph) rfl
private theorem from_d2 (k P F r n : Nat) (m : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (ph : phase m=1) (fit : F+r+n+3≤P)
    (d0 : T (F+1)=none) (d1 : T (F+r+2)=none) (d2 : T (F+r+n+3)=none)
    (b0 : ∀ i,F+1 < i → i < F+r+2 → ∃ b,T i=some b)
    (b1 : ∀ i,F+r+2 < i → i < F+r+n+3 → ∃ b,T i=some b) :
    GPath (M:=machine k) P (n+r+5) (C k 0 m (F+r+n+3) T) (C k 52 m (F+1) T) := by
  have p0:=keep (M:=machine k) (P:=P) (nc k 0 m) (nc k 1 m) (F+r+n+3) (F+r+n+2) T .left
    fit (by omega) (by rw [d2];exact row0_0 k m hm) (by dsimp only [dest];omega)
  have p1:=sweepL (M:=machine k) (P:=P) (nc k 1 m) T (F+r+2) n (by omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=b1 i lo (by omega)
    rw [cell];exact row1 k m hm b)
  rw [show F+r+2+n=F+r+n+2 by omega] at p1
  have p2:=keep (M:=machine k) (P:=P) (nc k 1 m) (nc k 2 m) (F+r+2) (F+r+2) T .stay
    (by omega) (by omega) (by rw [d1];exact row1_0 k m hm) rfl
  have p3:=keep (M:=machine k) (P:=P) (nc k 2 m) (nc k 3 m) (F+r+2) (F+r+1) T .left
    (by omega) (by omega) (by rw [d1];exact row2_0 k m hm) (by dsimp only [dest];omega)
  have p4:=sweepL (M:=machine k) (P:=P) (nc k 3 m) T (F+1) r (by omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=b0 i lo (by omega)
    rw [cell];exact row3 k m hm b)
  rw [show F+1+r=F+r+1 by omega] at p4
  have p5:=keep (M:=machine k) (P:=P) (nc k 3 m) (nc k 4 m) (F+1) (F+1) T .stay
    (by omega) (by omega) (by rw [d0];exact row3_0 k m hm) rfl
  have tail:=from_d0 k P F m T hm ph (by omega) d0
  have path:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath p0 p1) p2) p3) p4) p5) tail
  convert path using 1;omega
#print axioms length_step
#print axioms row4
#print axioms from_d0
#print axioms from_d2
end VirtualFinalClosure.RepeatEntry
