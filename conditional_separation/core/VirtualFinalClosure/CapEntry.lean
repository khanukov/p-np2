import VirtualFinalClosure.ModeRows
namespace VirtualFinalClosure.CapEntry
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","resolved_row","resolvedRow",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong literal capped-entry route term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique literal capped-entry route interface {mod}/{key}"
private theorem row0_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 0 m) (none)=(nc k 1 m,none,.left) := by
  have r:=literalRow k 0 m 1 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 0)
  rw [mode0 m hm] at r
  exact r
private theorem row1_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 1 m) (none)=(nc k 2 m,none,.stay) := by
  have r:=literalRow k 1 m 2 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 3)
  rw [mode0 m hm] at r
  exact r
private theorem row1_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 1 m) (some false)=(nc k 1 m,some false,.left) := by
  have r:=literalRow k 1 m 1 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 4)
  rw [mode0 m hm] at r
  exact r
private theorem row1_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 1 m) (some true)=(nc k 1 m,some true,.left) := by
  have r:=literalRow k 1 m 1 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 5)
  rw [mode0 m hm] at r
  exact r
private theorem row2_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 2 m) (none)=(nc k 3 m,none,.left) := by
  have r:=literalRow k 2 m 3 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 6)
  rw [mode0 m hm] at r
  exact r
private theorem row3_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 3 m) (none)=(nc k 4 m,none,.stay) := by
  have r:=literalRow k 3 m 4 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 9)
  rw [mode0 m hm] at r
  exact r
private theorem row3_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 3 m) (some false)=(nc k 3 m,some false,.left) := by
  have r:=literalRow k 3 m 3 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 10)
  rw [mode0 m hm] at r
  exact r
private theorem row3_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 3 m) (some true)=(nc k 3 m,some true,.left) := by
  have r:=literalRow k 3 m 3 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 11)
  rw [mode0 m hm] at r
  exact r
private theorem row1 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 1 m) (some b)=(nc k 1 m,some b,.left) := by
  cases b
  · exact row1_1 k m hm
  · exact row1_2 k m hm
private theorem row3 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 3 m) (some b)=(nc k 3 m,some b,.left) := by
  cases b
  · exact row3_1 k m hm
  · exact row3_2 k m hm
private theorem row4 (k : Nat) (f : Fin 4) :
    (machine k).step (nc k 4 (8+f.val)) none=(nc k 5 (8+f.val),none,.stay) := by
  have hm : 8+f.val<144 := by have h:=f.isLt;omega
  have ph : phase (8+f.val)=0 := by fin_cases f <;> decide
  have resolution : resolveCode k 240 (changeMode 0 (8+f.val))=(CertificateGuardClosure.machine k).stateCount+5 := by
    rw [mode0 _ hm]
    change _+(if phase (8+f.val)=1 then 52 else 5)=_
    rw [if_neg (by omega)]
  have r:=resolvedRow k 4 (8+f.val) 240 5 0 1 0 none (by decide) hm (by run_tac cellTac 12) resolution
  rw [mode0 _ hm] at r
  exact r
private theorem row5 (k : Nat) (f : Fin 4) :
    (machine k).step (nc k 5 (8+f.val)) none=(nc k 6 (8+f.val),none,.stay) := by
  have hm : 8+f.val<144 := by have h:=f.isLt;omega
  have clear : changeMode 6 (8+f.val)=8+f.val := by fin_cases f <;> decide
  have r:=literalRow k 5 (8+f.val) 6 0 1 6 none (by decide) hm (by decide) (by run_tac cellTac 15)
  rw [clear] at r
  exact r
private theorem from_d0 (k P F : Nat) (f : Fin 4) (T : Nat → Option Bool)
    (fit : F+1≤P) (d0 : T (F+1)=none) :
    GPath (M:=machine k) P 2 (C k 4 (8+f.val) (F+1) T) (C k 6 (8+f.val) (F+1) T) := by
  have p:=keep (M:=machine k) (P:=P) (nc k 4 (8+f.val)) (nc k 5 (8+f.val)) (F+1) (F+1) T .stay
    fit fit (by rw [d0];exact row4 k f) rfl
  have q:=keep (M:=machine k) (P:=P) (nc k 5 (8+f.val)) (nc k 6 (8+f.val)) (F+1) (F+1) T .stay
    fit fit (by rw [d0];exact row5 k f) rfl
  exact joinPath p q
/-- The actual D2 entry physically crosses occupied bank1 AND bank0; it does
not shortcut the live overflow head to D0. Empty bank1 is included. -/
private theorem from_d2 (k P F r n : Nat) (f : Fin 4) (T : Nat → Option Bool)
    (fit : F+r+n+3≤P)
    (d0 : T (F+1)=none) (d1 : T (F+r+2)=none) (d2 : T (F+r+n+3)=none)
    (b0 : ∀ i,F+1 < i → i < F+r+2 → ∃ b,T i=some b)
    (b1 : ∀ i,F+r+2 < i → i < F+r+n+3 → ∃ b,T i=some b) :
    GPath (M:=machine k) P (n+r+6) (C k 0 (8+f.val) (F+r+n+3) T) (C k 6 (8+f.val) (F+1) T) := by
  let m:=8+f.val
  have hm : m<144 := by have h:=f.isLt;dsimp only [m];omega
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
  have tail:=from_d0 k P F f T (by omega) d0
  have path:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath p0 p1) p2) p3) p4) p5) tail
  convert path using 1;omega
#print axioms from_d0
#print axioms from_d2
end VirtualFinalClosure.CapEntry
