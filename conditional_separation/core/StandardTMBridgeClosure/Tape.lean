import StandardTMBridgeClosure.Target
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing Lean Elab Command
run_cmd do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num (Name.append `_private `StandardTMBridgeClosure.Machine) 0) "StandardTMBridgeClosure") "phase"
  let some (.defnInfo ci):=e.find? n | throwError "Missing exact phase definition"
  liftTermElabM do
    let expected←Elab.Term.elabTerm (←`(Move → Fin 4)) none
    unless ←Meta.isDefEq ci.type expected do throwError "Wrong complete phase type"
  let some i:=e.getModuleIdxFor? n | throwError "Unowned phase"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `StandardTMBridgeClosure.Machine do throwError "Wrong phase owner"
  logInfo m!"typed-private-interface|StandardTMBridgeClosure.Machine|{n}|kind=definition|{(repr ci.type).pretty 1000000000}"
  modifyScope fun s=>{s with openDecls:=.explicit `phase n::s.openDecls}
private def cell {L : Nat} (tape : Fin L → Option Bool) (i : Int) : Bool × Option Bool :=
  if h:0 ≤ i ∧ i < (L : Int) then
    (decide (i=0),tape ⟨i.toNat,by omega⟩) else (false,none)
private def At {L : Nat} (p : Fin L) (tape : Fin L → Option Bool) (T : Tape (Bool × Option Bool)) : Prop :=
  ∀ i : Int,T.nth i=cell tape ((p.val : Int)+i)
private theorem cell_at {L : Nat} (tape : Fin L → Option Bool) (p : Fin L) :
    cell tape (p.val : Int)=(decide (p.val=0),tape p) := by
  have range:0 ≤ (p.val : Int) ∧ (p.val : Int) < (L : Int):=by constructor <;> omega
  simp only [cell,dif_pos range,Int.toNat_natCast]
  congr 1
  simp
private theorem cell_write {L : Nat} (tape : Fin L → Option Bool) (p : Fin L) (b : Option Bool) (i : Int) :
    cell (fun j=>if j=p then b else tape j) i=
      if i=(p.val : Int) then (decide (p.val=0),b) else cell tape i := by
  by_cases same:i=(p.val : Int)
  · subst i
    simp [cell_at]
  · rw [if_neg same]
    by_cases range:0 ≤ i ∧ i < (L : Int)
    · have ne:(⟨i.toNat,by omega⟩ : Fin L)≠p:=by
        intro eq
        have v:=congrArg Fin.val eq
        change i.toNat=p.val at v
        omega
      simp only [cell,dif_pos range,if_neg ne]
    · simp only [cell,range,↓reduceDIte]
private theorem at_write {L : Nat} (p : Fin L) (tape : Fin L → Option Bool) (T : Tape (Bool × Option Bool))
    (h:At p tape T) (b : Option Bool) :
    At p (fun j=>if j=p then b else tape j) (T.write (decide (p.val=0),b)) := by
  intro i
  rw [Tape.write_nth,cell_write]
  by_cases zero:i=0
  · subst i;simp
  · rw [if_neg zero,h i,if_neg (by omega)]
private def shifted {L : Nat} (p : Fin L) (a : Move) (T : Tape (Bool × Option Bool)) : Tape (Bool × Option Bool) :=
  match a with
  | .left=>if p.val=0 then T else T.move .left
  | .stay=>T
  | .right=>T.move .right
private theorem at_move {L : Nat} (p : Fin L) (tape : Fin L → Option Bool) (T : Tape (Bool × Option Bool))
    (h:At p tape T) (a : Move) (room:a=Move.right → p.val+1 < L) :
    At (moveHead p a) tape (shifted p a T) := by
  intro i
  cases a with
  | left=>
    change (if p.val=0 then T else T.move .left).nth i=cell tape (((moveHead p Move.left).val : Int)+i)
    by_cases zero:p.val=0
    · simp only [zero,↓reduceIte]
      have eq:moveHead p Move.left=p:=by apply Fin.ext;simp [moveHead,zero]
      simpa only [eq] using h i
    · rw [if_neg zero,Tape.move_left_nth,h]
      congr 1
      simp only [moveHead]
      omega
  | stay=>exact h i
  | right=>
    change (T.move .right).nth i=cell tape (((moveHead p Move.right).val : Int)+i)
    rw [Tape.move_right_nth,h]
    congr 1
    simp only [moveHead,dif_pos (room rfl)]
    omega
private theorem represents_at (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (d : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))) :
    Represents M c d ↔ d.q=some (c.state,0) ∧ At c.head c.tape d.Tape := by rfl
private theorem steps_add (M : UniformTM) (a b : Nat)
    (c : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))) :
    steps M (a+b) c=(steps M a c).bind (steps M b) := by
  induction a generalizing c with
  | zero=>simp only [Nat.zero_add,steps,Option.bind_some]
  | succ a ih=>
    simp only [Nat.succ_add,steps]
    cases h:TM0.step (compile M) c with
    | none=>rfl
    | some v=>simpa only [Option.bind_some] using ih v
private theorem input_nat (N : Nat) (y : Bitstring N) (j : Nat) :
    (Tape.mk₁ (encode (List.ofFn y))).nth (j : Int)=
      if h:j < N then (false,some (y ⟨j,h⟩)) else (false,none) := by
  rw [Tape.mk₁,Tape.mk₂,Tape.mk'_nth_nat,ListBlank.nth_mk]
  by_cases small:j < N
  · rw [dif_pos small,List.getI_eq_getElem _ (by simpa [encode] using small)]
    simp [encode]
  · rw [dif_neg small,List.getI_eq_default _ (by simpa [encode] using Nat.le_of_not_gt small)]
    rfl
private theorem input_negative (N : Nat) (y : Bitstring N) (j : Nat) :
    (Tape.mk₁ (encode (List.ofFn y))).nth (Int.negSucc j)=(false,none) := by
  change (ListBlank.mk ([] : List (Bool × Option Bool))).nth j=(false,none)
  simp
  rfl
private theorem boot (M : UniformTM) (N B : Nat) (y : Bitstring N) :
    ∃ d,steps M 1 (TM0.init (encode (List.ofFn y)))=some d ∧ Represents M (initialConfig M B y) d := by
  let T:=Tape.mk₁ (encode (List.ofFn y))
  let d : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)):=
    ⟨some (M.start,0),T.write (true,T.head.2)⟩
  refine ⟨d,rfl,?_,?_⟩
  · rfl
  · change At (⟨0,by simp [tapeLength]⟩ : Fin (tapeLength N B)) (initialConfig M B y).tape d.Tape
    intro i
    change (T.write (true,T.head.2)).nth i=cell (initialConfig M B y).tape (0+i)
    rw [Int.zero_add]
    cases i with
    | ofNat j=>
      change (T.write (true,T.head.2)).nth (j : Int)=cell (initialConfig M B y).tape (j : Int)
      rw [Tape.write_nth]
      by_cases zero:j=0
      · subst j
        have hd:T.head=if h:0 < N then (false,some (y ⟨0,h⟩)) else (false,none):=input_nat N y 0
        by_cases pos:0 < N
        · simp [cell,initialConfig,hd,tapeLength,pos]
          omega
        · simp [cell,initialConfig,hd,tapeLength,pos]
          omega
      · have iz:(j : Int)≠0:=by omega
        rw [if_neg iz]
        change (Tape.mk₁ (encode (List.ofFn y))).nth (j : Int)=_
        rw [input_nat]
        by_cases bound:j < tapeLength N B
        · have range:0 ≤ (j : Int) ∧ (j : Int) < (tapeLength N B : Int):=by constructor <;> omega
          simp only [cell,dif_pos range,Int.toNat_natCast]
          by_cases input:j < N
          · simp [initialConfig,input,zero]
          · simp [initialConfig,input,zero]
        · have outside:¬j < N:=by unfold tapeLength at bound;omega
          have range:¬(0 ≤ (j : Int) ∧ (j : Int) < (tapeLength N B : Int)):=by omega
          simp only [dif_neg outside,cell,dif_neg range]
    | negSucc j=>
      rw [Tape.write_nth]
      have iz:Int.negSucc j≠0:=by omega
      rw [if_neg iz]
      change (Tape.mk₁ (encode (List.ofFn y))).nth (Int.negSucc j)=_
      rw [input_negative]
      simp [cell]
end StandardTMBridgeClosure
