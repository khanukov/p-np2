import VirtualFinalClosure.PowerCodeFloor
import FullWeight.Rows
namespace VirtualFinalClosure.WeightCodeFloor
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("FullWeight.Rows","FullWeight","addCodes","addCodes",(0:Nat)),
      ("FullWeight.Rows","FullWeight","afterCodes","afterCodes",0),
      ("Cursor.Machine","Cursor","middle0","middle0",0),
      ("Cursor.Machine","Cursor","after0","after0",(0:Nat)),
      ("Cursor.Machine","Cursor","after1","after1",(0:Nat)),
      ("Cursor.Machine","Cursor","after2","after2",(0:Nat)),
      ("Cursor.Machine","Cursor","after3","after3",(0:Nat)),
      ("Cursor.Machine","Cursor","after4","after4",(0:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual weight ROM floor interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual weight ROM floor interface {mod}/{key}"
private theorem chunk0 (k : Nat) :
    (after0 k 0).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [after0]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact Or.inl True.intro | exact True.intro | omega
private theorem chunk1 (k : Nat) :
    (after1 k 0).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [after1]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact Or.inl True.intro | exact True.intro | omega
private theorem chunk2 (k : Nat) :
    (after2 k 0).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [after2]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact Or.inl True.intro | exact True.intro | omega
private theorem chunk3 (k : Nat) :
    (after3 k 0).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [after3]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact Or.inl True.intro | exact True.intro | omega
private theorem chunk4 (k : Nat) :
    (after4 k 0).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [after4]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact Or.inl True.intro | exact True.intro | omega
private theorem middle (k : Nat) :
    (middle0 k 0).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [middle0]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals omega
private theorem add (k j : Nat) (hj : j < k) :
    (addCodes k j).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [addCodes]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact Or.inl True.intro | exact True.intro | omega
private theorem after (k : Nat) :
    (afterCodes k).all (fun code=>decide (code/9=40 ∨ 329 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  have split : afterCodes k=after0 k 0++after1 k 0++after2 k 0++after3 k 0++after4 k 0:=by rfl
  rw [split,List.all_append,List.all_append,List.all_append,List.all_append,
    chunk0 k,chunk1 k,chunk2 k,chunk3 k,chunk4 k]
  rfl
#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
#print axioms chunk4
#print axioms middle
#print axioms add
#print axioms after
end VirtualFinalClosure.WeightCodeFloor
