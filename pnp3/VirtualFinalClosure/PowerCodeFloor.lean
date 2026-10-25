import VirtualFinalClosure.FullReplayRows
import PowerDriver.Rows
namespace VirtualFinalClosure.PowerCodeFloor
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("PowerDriver.Rows","PowerDriver","instructions","instructions",(0:Nat)),
      ("PowerDriver.Rows","PowerDriver","phase_row","phaseRow",1),
      ("Cursor.Machine","Cursor","power0","power0",(0:Nat)),
      ("Cursor.Machine","Cursor","power1","power1",(0:Nat)),
      ("Cursor.Machine","Cursor","power2","power2",(0:Nat)),
      ("Cursor.Machine","Cursor","power3","power3",(0:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual indexed power ROM floor interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual indexed power ROM floor interface {mod}/{key}"
private theorem chunk0 (k j : Nat) (hj : j < k) :
    (power0 k j).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [power0]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true,true_and,true_or]
  repeat' apply And.intro
  all_goals omega
private theorem chunk1 (k j : Nat) (hj : j < k) :
    (power1 k j).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [power1]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true,true_and,true_or]
  repeat' apply And.intro
  all_goals omega
private theorem chunk2 (k j : Nat) (hj : j < k) :
    (power2 k j).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [power2]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true,true_and,true_or]
  repeat' apply And.intro
  all_goals omega
private theorem chunk3 (k j : Nat) (hj : j < k) :
    (power3 k j).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [power3]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals omega
/-- Ordinary symbolic kernel certificates for every indexed power row,
including the real cap target. No HOST evaluation or guessed state floor. -/
private theorem certificate (k j : Nat) (hj : j < k) :
    (instructions k j).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  have split : instructions k j=power0 k j++power1 k j++power2 k j++power3 k j:=by rfl
  rw [split,List.all_append,List.all_append,List.all_append,chunk0 k j hj,chunk1 k j hj,chunk2 k j hj,chunk3 k j hj]
  rfl
private theorem length (k j : Nat) : (instructions k j).length=246:=by rfl
private theorem row_floor (k j i : Nat) (b : Option Bool) (hj : j < k)
    (lo : 329+82*j ≤ i) (hi : i < 411+82*j) :
    ((Cursor.machine k).step (Cursor.q k i) b).1.val=40 ∨
      329 ≤ ((Cursor.machine k).step (Cursor.q k i) b).1.val ∧
      ((Cursor.machine k).step (Cursor.q k i) b).1.val ≤ 798+93*k := by
  let ix:=3*(i-(329+82*j))+(match b with | none=>0 | some false=>1 | some true=>2)
  have fits : ix < (instructions k j).length:=by
    rw [length]
    cases b with
    | none=>dsimp only [ix];omega
    | some v=>cases v <;> dsimp only [ix] <;> omega
  let code:=(instructions k j)[ix]!
  have mem : code ∈ instructions k j := by
    dsimp only [code]
    rw [getElem!_pos _ ix fits]
    exact List.getElem_mem fits
  have checked:=of_decide_eq_true ((List.all_eq_true.mp (certificate k j hj)) code mem)
  have lookup : (instructions k j)[ix]?=some code:=by
    rw [List.getElem?_eq_getElem fits]
    dsimp only [code]
    rw [getElem!_pos _ ix fits]
  have row:=phaseRow k j i code b hj lo hi lookup
  have cb : code/9 < Cursor.stateCount k:=by unfold Cursor.stateCount;rcases checked with h|h <;> omega
  rw [row]
  change (code/9)%Cursor.stateCount k=40 ∨ 329 ≤ (code/9)%Cursor.stateCount k ∧ (code/9)%Cursor.stateCount k ≤ 798+93*k
  rw [Nat.mod_eq_of_lt cb]
  exact checked
#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
#print axioms certificate
#print axioms length
#print axioms row_floor
end VirtualFinalClosure.PowerCodeFloor
