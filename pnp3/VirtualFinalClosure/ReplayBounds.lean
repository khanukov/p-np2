import VirtualFinalClosure.GrowEntry
import CappedWorkspace.Kernel
namespace VirtualFinalClosure.ReplayBounds
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","ordinaryKernelRefl","kernelRefl",(0:Nat)),
      ("CappedWorkspace.Kernel","CappedWorkspace","row_value","rowValue",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal existing workspace row interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal existing workspace row interface {mod}/{key}"
/-- Closed finite ROM fact, proved by ordinary kernel reduction; not a host
simulation or runtime instruction. The negative kernel control is retained. -/
private theorem instruction_certificate : CappedWorkspace.instructions.all
    (fun code=>decide (code/9=40 ∨ 98 ≤ code/9 ∧ code/9 ≤ 201))=true := by
  run_tac kernelRefl
private theorem instruction_length : CappedWorkspace.instructions.length=309 := by
  run_tac kernelRefl
private theorem instruction_range (code : Nat) (member : code ∈ CappedWorkspace.instructions) :
    code/9=40 ∨ 98 ≤ code/9 ∧ code/9 ≤ 201 := by
  have checkedRows:=List.all_eq_true.mp instruction_certificate
  exact of_decide_eq_true (checkedRows code member)
private theorem row_range (k i : Nat) (b : Option Bool) (lo : 98 ≤ i) (hi : i < 201) :
    ((Cursor.machine k).step (Cursor.q k i) b).1.val=40 ∨ 98 ≤ ((Cursor.machine k).step (Cursor.q k i) b).1.val ∧ ((Cursor.machine k).step (Cursor.q k i) b).1.val ≤ 201 := by
  let index:=3*(i-98)+(match b with | none=>0 | some false=>1 | some true=>2)
  have indexBound : index < CappedWorkspace.instructions.length := by
    rw [instruction_length]
    cases b with
    | none=>dsimp only [index];omega
    | some v=>cases v <;> dsimp only [index] <;> omega
  have member : CappedWorkspace.instructions[index]! ∈ CappedWorkspace.instructions := by
    rw [getElem!_pos CappedWorkspace.instructions index indexBound]
    exact List.getElem_mem indexBound
  have range:=instruction_range _ member
  have codeBound : CappedWorkspace.instructions[index]!/9 < Cursor.stateCount k := by
    unfold Cursor.stateCount
    rcases range with h|h <;> omega
  rw [rowValue k i b lo hi]
  change (CappedWorkspace.instructions[index]!/9)%Cursor.stateCount k=40 ∨ 98 ≤ (CappedWorkspace.instructions[index]!/9)%Cursor.stateCount k ∧ (CappedWorkspace.instructions[index]!/9)%Cursor.stateCount k ≤ 201
  rw [Nat.mod_eq_of_lt codeBound]
  exact range
private theorem reject_stays {M : UniformTM} {N B : Nat} (c : Config M.stateCount N B)
    (atReject : c.state=M.reject) (u : Nat) : (M.run u c).state=M.reject := by
  induction u with
  | zero=>exact atReject
  | succ u ih=>
    change (M.step (M.run u c).state ((M.run u c).tape (M.run u c).head)).1=M.reject
    rw [ih,M.step_reject]
/-- Actual control range of the SAME native workspace execution up to first
q201. No assumption about elapsed versus tape allocation is used. -/
private theorem workspace_floor (k N B t : Nat) (c : Config (Cursor.machine k).stateCount N B)
    (start : c.state.val=98) (finish : ((Cursor.machine k).run t c).state.val=201)
    (first : ∀ u,u < t → ((Cursor.machine k).run u c).state.val < 201) :
    ∀ u,u ≤ t → 98 ≤ ((Cursor.machine k).run u c).state.val := by
  let M:=Cursor.machine k
  have reach (u : Nat) (hu : u ≤ t) : (M.run u c).state.val=40 ∨ 98 ≤ (M.run u c).state.val := by
    induction u with
    | zero=>exact Or.inr (by change 98 ≤ c.state.val;omega)
    | succ u ih=>
      rcases ih (by omega) with rejected|lower
      · have equal : (M.run u c).state=M.reject := Fin.ext rejected
        have stuck:=reject_stays (M.run u c) equal 1
        rw [←UniformTM.run_add] at stuck
        exact Or.inl (congrArg Fin.val stuck)
      · have upper:=first u (by omega)
        have state : (M.run u c).state=Cursor.q k (M.run u c).state.val := by
          apply Fin.ext
          change _=_%Cursor.stateCount k
          have bound : (M.run u c).state.val < Cursor.stateCount k := (M.run u c).state.isLt
          exact (Nat.mod_eq_of_lt bound).symm
        have row:=row_range k (M.run u c).state.val ((M.run u c).tape (M.run u c).head) lower upper
        rw [←state] at row
        exact row.imp_right And.left
  have finishM : (M.run t c).state.val=201 := finish
  intro u hu
  rcases reach u hu with rejected|lower
  · have equal : (M.run u c).state=M.reject := Fin.ext rejected
    have stuck:=reject_stays (M.run u c) equal (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at stuck
    have bad:=congrArg Fin.val stuck
    change (M.run t c).state.val=40 at bad
    have impossible : 201=40 := finishM.symm.trans bad
    omega
  · exact lower
#print axioms instruction_certificate
#print axioms instruction_length
#print axioms instruction_range
#print axioms row_range
#print axioms reject_stays
#print axioms workspace_floor
end VirtualFinalClosure.ReplayBounds
