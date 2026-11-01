import VirtualFinalClosure.Native
namespace VirtualFinalClosure.GuardFlags
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","encodeMeta","encodeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","modeBound",1) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong finite mode row declaration {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique finite mode row term {mod}/{key}"
private theorem flag_preserved (op m : Nat) (hm : m < 144) : flag (changeMode op m)=flag m := by
  by_cases small : op < 9
  · interval_cases op <;> dsimp only [changeMode,encodeMeta,flag,sourceMode,phase,seen,bad] <;> omega
  · have other : changeMode op m=m:=by
      dsimp only [changeMode]
      repeat' split
      all_goals omega
    rw [other]
private theorem encoded_bad (f v p s b : Nat) (hf : f < 4) (hv : v < 3)
    (hp : p < 3) (hs : s < 2) (hb : b < 2) : bad (encodeMeta f v p s b)=b := by
  dsimp only [bad,encodeMeta]
  omega
private theorem bad_preserved (op m : Nat) (hm : m < 144) (notSet : op≠5) (notCarried : op≠8) :
    bad (changeMode op m)=bad m := by
  have hf : flag m < 4:=Nat.mod_lt _ (by decide)
  have hv : sourceMode m < 3:=Nat.mod_lt _ (by decide)
  have hp : phase m < 3:=Nat.mod_lt _ (by decide)
  have hs : seen m < 2:=Nat.mod_lt _ (by decide)
  have hb : bad m < 2:=Nat.mod_lt _ (by decide)
  by_cases small : op < 9
  · interval_cases op
    · exact congrArg bad (mode0 m hm)
    · exact encoded_bad _ _ _ _ _ hf (by decide) hp hs hb
    · exact encoded_bad _ _ _ _ _ hf (by decide) hp (by decide) hb
    · exact encoded_bad _ _ _ _ _ hf (by decide) hp hs hb
    · exact encoded_bad _ _ _ _ _ hf hv (by decide) hs hb
    · exact (notSet rfl).elim
    · exact encoded_bad _ _ _ _ _ hf hv hp (by decide) hb
    · exact encoded_bad _ _ _ _ _ hf hv (by decide) hs hb
    · exact (notCarried rfl).elim
  · have other : changeMode op m=m:=by
      dsimp only [changeMode]
      repeat' split
      all_goals omega
    rw [other]
private theorem bad_set (m : Nat) : bad (changeMode 5 m)=1 := by
  dsimp only [changeMode,encodeMeta,flag,sourceMode,phase,seen,bad]
  omega
private theorem mode_set (m : Nat) :
    bad (changeMode 8 m)=(if sourceMode m=1 then 1 else bad m) := by
  dsimp only [changeMode,encodeMeta,flag,sourceMode,phase,seen,bad]
  split <;> omega
private theorem mode_preserved (op m : Nat) (hm : m < 144) (which : op=0 ∨ op=5 ∨ op=7 ∨ op=8) :
    sourceMode (changeMode op m)=sourceMode m := by
  rcases which with rfl|rfl|rfl|rfl
  all_goals dsimp only [changeMode,encodeMeta,flag,sourceMode,phase,seen,bad]
  all_goals omega
private theorem source_seen_preserved (op m : Nat) (hm : m < 144) (which : op=0 ∨ op=5 ∨ op=7 ∨ op=8) :
    seen (changeMode op m)=seen m := by
  rcases which with rfl|rfl|rfl|rfl
  all_goals dsimp only [changeMode,encodeMeta,flag,sourceMode,phase,seen,bad]
  all_goals omega
private theorem phase_one_mode (m : Nat) : sourceMode (changeMode 4 m)=sourceMode m := by
  dsimp only [changeMode,encodeMeta,flag,sourceMode,phase,seen,bad]
  omega
private theorem phase_two (m : Nat) : phase (changeMode 7 m)=2 := by
  dsimp only [changeMode,encodeMeta,flag,sourceMode,phase,seen,bad]
  omega
private theorem scan_bad (m : Nat) (hm : m < 144) (b : Bool) :
    (bad (changeMode (if b then 5 else 0) m)=0 ↔ bad m=0 ∧ b=false) := by
  cases b
  · rw [if_neg (by decide : ¬(false=true)),mode0 m hm]
    tauto
  · rw [if_pos rfl,bad_set]
    simp only [Nat.one_ne_zero,Bool.true_eq_false,and_false]
private theorem restored_bad (m : Nat) (_hm : m < 144) (b : Bool)
    (carried : sourceMode m=(if b then 1 else 0)) :
    (bad (changeMode 8 m)=0 ↔ bad m=0 ∧ b=false) := by
  rw [mode_set m,carried]
  cases b <;> simp
#print axioms flag_preserved
#print axioms encoded_bad
#print axioms bad_preserved
#print axioms bad_set
#print axioms mode_set
#print axioms mode_preserved
#print axioms source_seen_preserved
#print axioms phase_one_mode
#print axioms phase_two
#print axioms scan_bad
#print axioms restored_bad
end VirtualFinalClosure.GuardFlags
