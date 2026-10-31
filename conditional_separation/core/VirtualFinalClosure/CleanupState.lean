import VirtualFinalClosure.CleanupRows
import VirtualReady.Kernel
namespace VirtualFinalClosure.CleanupState
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualReady.Kernel","VirtualReady","ins","cleanupCodes",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","enc","oldEnc",0),
      ("VirtualReady.Kernel","VirtualReady","sym","oldSym",0),
      ("VirtualReady.Kernel","VirtualReady","mov","oldMov",0),
      ("VirtualReady.Kernel","VirtualReady","clean_row","cleanRow",1),
      ("VirtualReady.Kernel","VirtualReady","gate_row","gateRow",1),
      ("VirtualLeaf.Transport","VirtualLeaf","ready_row","readyRow",1),
      ("VirtualLeaf.Transport","VirtualLeaf","ready_index","readyIndex",1) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal cleanup-state term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal cleanup-state term {mod}/{key}"
private def region (k : Nat) (s : Fin (Cursor.machine k).stateCount) : Prop:=
  s.val=798+93*k ∨ (889+93*k ≤ s.val ∧ s.val < 934+93*k) ∨
    s.val=936+93*k ∨ s=(Cursor.machine k).reject
private def region_type : ∀ k,Fin (Cursor.machine k).stateCount → Prop:=region
private theorem q_value (k i : Nat) (fit : i < Cursor.stateCount k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt fit
private theorem clean0 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+0)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 0 (890+93*k) (none) (none) .right (by decide) (by
      change some (8012+837*k)=some (9*(890+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (890+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 0 (890+93*k) (some false) (some false) .right (by decide) (by
        change some (8015+837*k)=some (9*(890+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (890+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 0 (890+93*k) (some true) (some true) .right (by decide) (by
        change some (8018+837*k)=some (9*(890+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (890+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean1 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+1)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 1 (891+93*k) (none) (none) .left (by decide) (by
      change some (8019+837*k)=some (9*(891+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (891+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 1 (890+93*k) (some false) (some false) .right (by decide) (by
        change some (8015+837*k)=some (9*(890+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (890+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 1 (890+93*k) (some true) (some false) .right (by decide) (by
        change some (8015+837*k)=some (9*(890+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (890+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean2 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+2)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 2 (892+93*k) (none) (none) .stay (by decide) (by
      change some (8029+837*k)=some (9*(892+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (892+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 2 (891+93*k) (some false) (some false) .left (by decide) (by
        change some (8022+837*k)=some (9*(891+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (891+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 2 (891+93*k) (some true) (some true) .left (by decide) (by
        change some (8025+837*k)=some (9*(891+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (891+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean3 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+3)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 3 (893+93*k) (none) (none) .right (by decide) (by
      change some (8039+837*k)=some (9*(893+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (893+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 3 (893+93*k) (some false) (some false) .right (by decide) (by
        change some (8042+837*k)=some (9*(893+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (893+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 3 (893+93*k) (some true) (some true) .right (by decide) (by
        change some (8045+837*k)=some (9*(893+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (893+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean4 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+4)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 4 (894+93*k) (none) (none) .stay (by decide) (by
      change some (8047+837*k)=some (9*(894+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (894+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 4 (893+93*k) (some false) (some false) .right (by decide) (by
        change some (8042+837*k)=some (9*(893+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (893+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 4 (893+93*k) (some true) (some true) .right (by decide) (by
        change some (8045+837*k)=some (9*(893+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (893+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean5 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+5)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 5 (895+93*k) (none) (none) .right (by decide) (by
      change some (8057+837*k)=some (9*(895+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (895+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 5 (895+93*k) (some false) (some false) .right (by decide) (by
        change some (8060+837*k)=some (9*(895+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (895+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 5 (895+93*k) (some true) (some true) .right (by decide) (by
        change some (8063+837*k)=some (9*(895+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (895+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean6 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+6)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 6 (896+93*k) (none) (none) .left (by decide) (by
      change some (8064+837*k)=some (9*(896+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (896+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 6 (895+93*k) (some false) (some false) .right (by decide) (by
        change some (8060+837*k)=some (9*(895+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (895+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 6 (895+93*k) (some true) (some false) .right (by decide) (by
        change some (8060+837*k)=some (9*(895+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (895+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean7 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+7)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 7 (897+93*k) (none) (none) .stay (by decide) (by
      change some (8074+837*k)=some (9*(897+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (897+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 7 (896+93*k) (some false) (some false) .left (by decide) (by
        change some (8067+837*k)=some (9*(896+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (896+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 7 (896+93*k) (some true) (some true) .left (by decide) (by
        change some (8070+837*k)=some (9*(896+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (896+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean8 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+8)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 8 (898+93*k) (none) (none) .right (by decide) (by
      change some (8084+837*k)=some (9*(898+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (898+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 8 (898+93*k) (some false) (some false) .right (by decide) (by
        change some (8087+837*k)=some (9*(898+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (898+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 8 (898+93*k) (some true) (some true) .right (by decide) (by
        change some (8090+837*k)=some (9*(898+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (898+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean9 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+9)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 9 (899+93*k) (none) (none) .stay (by decide) (by
      change some (8092+837*k)=some (9*(899+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (899+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 9 (898+93*k) (some false) (some false) .right (by decide) (by
        change some (8087+837*k)=some (9*(898+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (898+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 9 (898+93*k) (some true) (some true) .right (by decide) (by
        change some (8090+837*k)=some (9*(898+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (898+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean10 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+10)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 10 (900+93*k) (none) (none) .right (by decide) (by
      change some (8102+837*k)=some (9*(900+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (900+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 10 (900+93*k) (some false) (some false) .right (by decide) (by
        change some (8105+837*k)=some (9*(900+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (900+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 10 (900+93*k) (some true) (some true) .right (by decide) (by
        change some (8108+837*k)=some (9*(900+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (900+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean11 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+11)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 11 (901+93*k) (none) (none) .left (by decide) (by
      change some (8109+837*k)=some (9*(901+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (901+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 11 (900+93*k) (some false) (some false) .right (by decide) (by
        change some (8105+837*k)=some (9*(900+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (900+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 11 (900+93*k) (some true) (some false) .right (by decide) (by
        change some (8105+837*k)=some (9*(900+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (900+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean12 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+12)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 12 (902+93*k) (none) (none) .stay (by decide) (by
      change some (8119+837*k)=some (9*(902+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (902+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 12 (901+93*k) (some false) (some false) .left (by decide) (by
        change some (8112+837*k)=some (9*(901+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (901+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 12 (901+93*k) (some true) (some true) .left (by decide) (by
        change some (8115+837*k)=some (9*(901+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (901+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean13 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+13)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 13 (903+93*k) (none) (none) .right (by decide) (by
      change some (8129+837*k)=some (9*(903+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (903+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 13 (903+93*k) (some false) (some false) .right (by decide) (by
        change some (8132+837*k)=some (9*(903+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (903+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 13 (903+93*k) (some true) (some true) .right (by decide) (by
        change some (8135+837*k)=some (9*(903+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (903+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean14 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+14)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 14 (904+93*k) (none) (none) .stay (by decide) (by
      change some (8137+837*k)=some (9*(904+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (904+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 14 (903+93*k) (some false) (some false) .right (by decide) (by
        change some (8132+837*k)=some (9*(903+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (903+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 14 (903+93*k) (some true) (some true) .right (by decide) (by
        change some (8135+837*k)=some (9*(903+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (903+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean15 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+15)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 15 (905+93*k) (none) (none) .right (by decide) (by
      change some (8147+837*k)=some (9*(905+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (905+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 15 (905+93*k) (some false) (some false) .right (by decide) (by
        change some (8150+837*k)=some (9*(905+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (905+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 15 (905+93*k) (some true) (some true) .right (by decide) (by
        change some (8153+837*k)=some (9*(905+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (905+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean16 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+16)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 16 (906+93*k) (none) (none) .left (by decide) (by
      change some (8154+837*k)=some (9*(906+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (906+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 16 (905+93*k) (some false) (some false) .right (by decide) (by
        change some (8150+837*k)=some (9*(905+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (905+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 16 (905+93*k) (some true) (some false) .right (by decide) (by
        change some (8150+837*k)=some (9*(905+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (905+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean17 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+17)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 17 (907+93*k) (none) (none) .stay (by decide) (by
      change some (8164+837*k)=some (9*(907+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (907+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 17 (906+93*k) (some false) (some false) .left (by decide) (by
        change some (8157+837*k)=some (9*(906+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (906+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 17 (906+93*k) (some true) (some true) .left (by decide) (by
        change some (8160+837*k)=some (9*(906+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (906+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean18 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+18)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 18 (908+93*k) (none) (none) .right (by decide) (by
      change some (8174+837*k)=some (9*(908+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (908+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 18 (908+93*k) (some false) (some false) .right (by decide) (by
        change some (8177+837*k)=some (9*(908+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (908+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 18 (908+93*k) (some true) (some true) .right (by decide) (by
        change some (8180+837*k)=some (9*(908+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (908+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean19 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+19)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 19 (909+93*k) (none) (none) .stay (by decide) (by
      change some (8182+837*k)=some (9*(909+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (909+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 19 (908+93*k) (some false) (some false) .right (by decide) (by
        change some (8177+837*k)=some (9*(908+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (908+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 19 (908+93*k) (some true) (some true) .right (by decide) (by
        change some (8180+837*k)=some (9*(908+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (908+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean20 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+20)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 20 (910+93*k) (none) (none) .right (by decide) (by
      change some (8192+837*k)=some (9*(910+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (910+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 20 (910+93*k) (some false) (some false) .right (by decide) (by
        change some (8195+837*k)=some (9*(910+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (910+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 20 (910+93*k) (some true) (some true) .right (by decide) (by
        change some (8198+837*k)=some (9*(910+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (910+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean21 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+21)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 21 (911+93*k) (none) (none) .left (by decide) (by
      change some (8199+837*k)=some (9*(911+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (911+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 21 (910+93*k) (some false) (some false) .right (by decide) (by
        change some (8195+837*k)=some (9*(910+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (910+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 21 (910+93*k) (some true) (some false) .right (by decide) (by
        change some (8195+837*k)=some (9*(910+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (910+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean22 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+22)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 22 (912+93*k) (none) (none) .stay (by decide) (by
      change some (8209+837*k)=some (9*(912+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (912+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 22 (911+93*k) (some false) (some false) .left (by decide) (by
        change some (8202+837*k)=some (9*(911+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (911+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 22 (911+93*k) (some true) (some true) .left (by decide) (by
        change some (8205+837*k)=some (9*(911+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (911+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean23 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+23)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 23 (913+93*k) (none) (none) .right (by decide) (by
      change some (8219+837*k)=some (9*(913+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (913+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 23 (913+93*k) (some false) (some false) .right (by decide) (by
        change some (8222+837*k)=some (9*(913+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (913+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 23 (913+93*k) (some true) (some true) .right (by decide) (by
        change some (8225+837*k)=some (9*(913+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (913+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean24 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+24)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 24 (914+93*k) (none) (none) .stay (by decide) (by
      change some (8227+837*k)=some (9*(914+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (914+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 24 (913+93*k) (some false) (some false) .right (by decide) (by
        change some (8222+837*k)=some (9*(913+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (913+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 24 (913+93*k) (some true) (some true) .right (by decide) (by
        change some (8225+837*k)=some (9*(913+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (913+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean25 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+25)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 25 (915+93*k) (none) (none) .right (by decide) (by
      change some (8237+837*k)=some (9*(915+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (915+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 25 (915+93*k) (some false) (some false) .right (by decide) (by
        change some (8240+837*k)=some (9*(915+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (915+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 25 (915+93*k) (some true) (some true) .right (by decide) (by
        change some (8243+837*k)=some (9*(915+93*k)+3*2+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (915+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean26 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+26)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 26 (916+93*k) (none) (none) .left (by decide) (by
      change some (8244+837*k)=some (9*(916+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (916+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 26 (915+93*k) (some false) (some false) .right (by decide) (by
        change some (8240+837*k)=some (9*(915+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (915+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 26 (915+93*k) (some true) (some false) .right (by decide) (by
        change some (8240+837*k)=some (9*(915+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (915+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean27 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+27)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 27 (917+93*k) (none) (none) .stay (by decide) (by
      change some (8254+837*k)=some (9*(917+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (917+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 27 (916+93*k) (some false) (some false) .left (by decide) (by
        change some (8247+837*k)=some (9*(916+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (916+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 27 (916+93*k) (some true) (some true) .left (by decide) (by
        change some (8250+837*k)=some (9*(916+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (916+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean28 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+28)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 28 (918+93*k) (none) (none) .left (by decide) (by
      change some (8262+837*k)=some (9*(918+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (918+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 28 (918+93*k) (some false) (some false) .left (by decide) (by
        change some (8265+837*k)=some (9*(918+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (918+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 28 (918+93*k) (some true) (some true) .left (by decide) (by
        change some (8268+837*k)=some (9*(918+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (918+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean29 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+29)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 29 (919+93*k) (none) (none) .stay (by decide) (by
      change some (8272+837*k)=some (9*(919+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (919+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 29 (918+93*k) (some false) (some false) .left (by decide) (by
        change some (8265+837*k)=some (9*(918+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (918+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 29 (918+93*k) (some true) (some true) .left (by decide) (by
        change some (8268+837*k)=some (9*(918+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (918+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean30 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+30)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 30 (920+93*k) (none) (none) .left (by decide) (by
      change some (8280+837*k)=some (9*(920+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (920+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 30 (920+93*k) (some false) (some false) .left (by decide) (by
        change some (8283+837*k)=some (9*(920+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (920+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 30 (920+93*k) (some true) (some true) .left (by decide) (by
        change some (8286+837*k)=some (9*(920+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (920+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean31 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+31)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 31 (921+93*k) (none) (none) .stay (by decide) (by
      change some (8290+837*k)=some (9*(921+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (921+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 31 (920+93*k) (some false) (some false) .left (by decide) (by
        change some (8283+837*k)=some (9*(920+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (920+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 31 (920+93*k) (some true) (some true) .left (by decide) (by
        change some (8286+837*k)=some (9*(920+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (920+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean32 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+32)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 32 (922+93*k) (none) (none) .left (by decide) (by
      change some (8298+837*k)=some (9*(922+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (922+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 32 (922+93*k) (some false) (some false) .left (by decide) (by
        change some (8301+837*k)=some (9*(922+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (922+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 32 (922+93*k) (some true) (some true) .left (by decide) (by
        change some (8304+837*k)=some (9*(922+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (922+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean33 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+33)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 33 (923+93*k) (none) (none) .stay (by decide) (by
      change some (8308+837*k)=some (9*(923+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (923+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 33 (922+93*k) (some false) (some false) .left (by decide) (by
        change some (8301+837*k)=some (9*(922+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (922+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 33 (922+93*k) (some true) (some true) .left (by decide) (by
        change some (8304+837*k)=some (9*(922+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (922+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean34 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+34)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 34 (924+93*k) (none) (none) .left (by decide) (by
      change some (8316+837*k)=some (9*(924+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (924+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 34 (924+93*k) (some false) (some false) .left (by decide) (by
        change some (8319+837*k)=some (9*(924+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (924+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 34 (924+93*k) (some true) (some true) .left (by decide) (by
        change some (8322+837*k)=some (9*(924+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (924+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean35 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+35)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 35 (925+93*k) (none) (none) .stay (by decide) (by
      change some (8326+837*k)=some (9*(925+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (925+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 35 (924+93*k) (some false) (some false) .left (by decide) (by
        change some (8319+837*k)=some (9*(924+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (924+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 35 (924+93*k) (some true) (some true) .left (by decide) (by
        change some (8322+837*k)=some (9*(924+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (924+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean36 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+36)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 36 (926+93*k) (none) (none) .left (by decide) (by
      change some (8334+837*k)=some (9*(926+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (926+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 36 (926+93*k) (some false) (some false) .left (by decide) (by
        change some (8337+837*k)=some (9*(926+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (926+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 36 (926+93*k) (some true) (some true) .left (by decide) (by
        change some (8340+837*k)=some (9*(926+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (926+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean37 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+37)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 37 (927+93*k) (none) (none) .stay (by decide) (by
      change some (8344+837*k)=some (9*(927+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (927+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 37 (926+93*k) (some false) (some false) .left (by decide) (by
        change some (8337+837*k)=some (9*(926+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (926+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 37 (926+93*k) (some true) (some true) .left (by decide) (by
        change some (8340+837*k)=some (9*(926+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (926+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean38 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+38)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 38 (928+93*k) (none) (none) .left (by decide) (by
      change some (8352+837*k)=some (9*(928+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (928+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 38 (928+93*k) (some false) (some false) .left (by decide) (by
        change some (8355+837*k)=some (9*(928+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (928+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 38 (928+93*k) (some true) (some true) .left (by decide) (by
        change some (8358+837*k)=some (9*(928+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (928+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean39 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+39)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 39 (40) (none) (none) .stay (by decide) (by
      change some (361)=some (9*(40)+3*0+1)
      rfl)
    rw [row]
    exact Or.inr (Or.inr (Or.inr rfl))
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 39 (929+93*k) (some false) (some false) .left (by decide) (by
        change some (8364+837*k)=some (9*(929+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (929+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 39 (40) (some true) (some true) .stay (by decide) (by
        change some (367)=some (9*(40)+3*2+1)
        rfl)
      rw [row]
      exact Or.inr (Or.inr (Or.inr rfl))
private theorem clean40 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+40)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 40 (929+93*k) (none) (none) .left (by decide) (by
      change some (8361+837*k)=some (9*(929+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (929+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 40 (40) (some false) (some false) .stay (by decide) (by
        change some (364)=some (9*(40)+3*1+1)
        rfl)
      rw [row]
      exact Or.inr (Or.inr (Or.inr rfl))
    | true=>
      have row:=cleanRow k 40 (930+93*k) (some true) (some true) .left (by decide) (by
        change some (8376+837*k)=some (9*(930+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (930+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean41 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+41)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 41 (931+93*k) (none) (none) .stay (by decide) (by
      change some (8380+837*k)=some (9*(931+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (931+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 41 (40) (some false) (some false) .stay (by decide) (by
        change some (364)=some (9*(40)+3*1+1)
        rfl)
      rw [row]
      exact Or.inr (Or.inr (Or.inr rfl))
    | true=>
      have row:=cleanRow k 41 (930+93*k) (some true) (some true) .left (by decide) (by
        change some (8376+837*k)=some (9*(930+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (930+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean42 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+42)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 42 (932+93*k) (none) (none) .left (by decide) (by
      change some (8388+837*k)=some (9*(932+93*k)+3*0+0)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (932+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 42 (932+93*k) (some false) (some false) .left (by decide) (by
        change some (8391+837*k)=some (9*(932+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (932+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 42 (932+93*k) (some true) (some true) .left (by decide) (by
        change some (8394+837*k)=some (9*(932+93*k)+3*2+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (932+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean43 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+43)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 43 (933+93*k) (none) (none) .right (by decide) (by
      change some (8399+837*k)=some (9*(933+93*k)+3*0+2)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (933+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 43 (932+93*k) (some false) (some false) .left (by decide) (by
        change some (8391+837*k)=some (9*(932+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (932+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 43 (932+93*k) (some true) (some false) .left (by decide) (by
        change some (8391+837*k)=some (9*(932+93*k)+3*1+0)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (932+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
private theorem clean44 (k : Nat) (b : Option Bool) : region k (((Cursor.machine k).step (Cursor.q k (889+93*k+44)) b).1) := by
  cases b with
  | none=>
    have row:=cleanRow k 44 (936+93*k) (none) (none) .stay (by decide) (by
      change some (8425+837*k)=some (9*(936+93*k)+3*0+1)
      congr 1
      omega)
    rw [row]
    dsimp only [region]
    rw [q_value k (936+93*k) (by unfold Cursor.stateCount;omega)]
    exact Or.inr (Or.inr (Or.inl rfl))
  | some v=>cases v with
    | false=>
      have row:=cleanRow k 44 (933+93*k) (some false) (some false) .right (by decide) (by
        change some (8402+837*k)=some (9*(933+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (933+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    | true=>
      have row:=cleanRow k 44 (933+93*k) (some true) (some false) .right (by decide) (by
        change some (8402+837*k)=some (9*(933+93*k)+3*1+2)
        congr 1
        omega)
      rw [row]
      dsimp only [region]
      rw [q_value k (933+93*k) (by unfold Cursor.stateCount;omega)]
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
/-- Exhaustive literal cleanup control closure, including malformed-cell
reject transitions. Endpoint equalities alone are not used as prefix bounds. -/
private theorem row_closed (k : Nat) (s : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (inside : region k s) : region k (((Cursor.machine k).step s b).1) := by
  rcases inside with gate|middle|ready|rejected
  · have eq : s=Cursor.q k (798+93*k):=Fin.ext (by rw [q_value k _ (by unfold Cursor.stateCount;omega)];exact gate)
    rw [eq,gateRow]
    exact Or.inr (Or.inl ⟨by rw [q_value k _ (by unfold Cursor.stateCount;omega)],by rw [q_value k _ (by unfold Cursor.stateCount;omega)];omega⟩)
  · let j : Fin 45:=⟨s.val-(889+93*k),by omega⟩
    have eq : s=Cursor.q k (889+93*k+j.val):=Fin.ext (by
      rw [q_value k _ (by unfold Cursor.stateCount;have bound:=j.isLt;omega)]
      dsimp only [j];omega)
    rw [eq]
    have jb:=j.isLt
    generalize hj : j.val=i at jb ⊢
    interval_cases i
    · exact clean0 k b
    · exact clean1 k b
    · exact clean2 k b
    · exact clean3 k b
    · exact clean4 k b
    · exact clean5 k b
    · exact clean6 k b
    · exact clean7 k b
    · exact clean8 k b
    · exact clean9 k b
    · exact clean10 k b
    · exact clean11 k b
    · exact clean12 k b
    · exact clean13 k b
    · exact clean14 k b
    · exact clean15 k b
    · exact clean16 k b
    · exact clean17 k b
    · exact clean18 k b
    · exact clean19 k b
    · exact clean20 k b
    · exact clean21 k b
    · exact clean22 k b
    · exact clean23 k b
    · exact clean24 k b
    · exact clean25 k b
    · exact clean26 k b
    · exact clean27 k b
    · exact clean28 k b
    · exact clean29 k b
    · exact clean30 k b
    · exact clean31 k b
    · exact clean32 k b
    · exact clean33 k b
    · exact clean34 k b
    · exact clean35 k b
    · exact clean36 k b
    · exact clean37 k b
    · exact clean38 k b
    · exact clean39 k b
    · exact clean40 k b
    · exact clean41 k b
    · exact clean42 k b
    · exact clean43 k b
    · exact clean44 k b
  · have eq : s=Cursor.mReady k ⟨2,by decide⟩:=by
      rw [readyIndex]
      exact Fin.ext (by rw [q_value k _ (by unfold Cursor.stateCount;omega)];exact ready)
    rw [eq,readyRow]
    exact Or.inr (Or.inr (Or.inl (by rw [readyIndex,q_value k _ (by unfold Cursor.stateCount;omega)])))
  · rw [rejected,UniformTM.step_reject]
    exact Or.inr (Or.inr (Or.inr rfl))
private theorem run_closed (k : Nat) {N B : Nat} (c : Config (Cursor.machine k).stateCount N B)
    (inside : region k c.state) (t : Nat) : region k (((Cursor.machine k).run t c).state) := by
  induction t with
  | zero=>exact inside
  | succ t ih=>exact row_closed k _ _ ih
#print axioms region_type
#print axioms q_value
#print axioms clean0
#print axioms clean1
#print axioms clean2
#print axioms clean3
#print axioms clean4
#print axioms clean5
#print axioms clean6
#print axioms clean7
#print axioms clean8
#print axioms clean9
#print axioms clean10
#print axioms clean11
#print axioms clean12
#print axioms clean13
#print axioms clean14
#print axioms clean15
#print axioms clean16
#print axioms clean17
#print axioms clean18
#print axioms clean19
#print axioms clean20
#print axioms clean21
#print axioms clean22
#print axioms clean23
#print axioms clean24
#print axioms clean25
#print axioms clean26
#print axioms clean27
#print axioms clean28
#print axioms clean29
#print axioms clean30
#print axioms clean31
#print axioms clean32
#print axioms clean33
#print axioms clean34
#print axioms clean35
#print axioms clean36
#print axioms clean37
#print axioms clean38
#print axioms clean39
#print axioms clean40
#print axioms clean41
#print axioms clean42
#print axioms clean43
#print axioms clean44
#print axioms row_closed
#print axioms run_closed
end VirtualFinalClosure.CleanupState
