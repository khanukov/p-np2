import CarryWindow.Target
namespace CarryWindow
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  for s in ["oldq","rows","native","extend","liftAction"] do
    let ns:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith "_private.CarryWindow.Machine." && n.toString.endsWith (".CarryWindow."++s)
    unless ns.length=1 do throwError "Ambiguous own private term {s}: {ns}"
    logInfo m!"private-term|{ns.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous s) ns.head! :: st.openDecls}
private theorem inject (k : Nat) {s t : Fin (CanonicalLeaf.machine k).stateCount}
    (h : embed k s=embed k t) : s=t := Fin.ext (congrArg (fun x => x.val) h)
private theorem disjoint (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) (j : Fin 25) :
    embed k s ≠ extra k j := by
  intro h; have e:=congrArg Fin.val h
  dsimp only [embed,extra] at e; have small:=s.isLt; omega
private theorem oldq_val (k i : Nat) (hi : i < Cursor.stateCount k) :
    (oldq k i).val=288+i := by
  change 288+i%Cursor.stateCount k=288+i
  rw [Nat.mod_eq_of_lt hi]
private theorem oldq_ne (k i : Nat) (hi : i < Cursor.stateCount k) (a : i ≠ 39) (r : i ≠ 40) :
    oldq k i ≠ (CanonicalLeaf.machine k).accept ∧ oldq k i ≠ (CanonicalLeaf.machine k).reject := by
  constructor
  all_goals intro h; have e:=congrArg Fin.val h; rw [oldq_val k i hi] at e
  · change 288+i=327 at e; omega
  · change 288+i=328 at e; omega
/-- Exact effective old-row delta: two read-none intercepts, no other changed old row. -/
theorem table_delta (k : Nat) : ∀ (s : Fin (CanonicalLeaf.machine k).stateCount) b,
    (machine k).step (embed k s) b=
      if s=VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))) ∧ b=none
      then (extra k 0,none,.left)
      else if s=VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (613+93*k))) ∧ b=none
      then (ready k,none,.stay)
      else (embed k ((CanonicalLeaf.machine k).step s b).1,((CanonicalLeaf.machine k).step s b).2) := by
  intro s b
  have ne1:=oldq_ne k (430+93*k) (by unfold Cursor.stateCount; omega) (by omega) (by omega)
  have ne2:=oldq_ne k (613+93*k) (by unfold Cursor.stateCount; omega) (by omega) (by omega)
  change (machine k).step (embed k s) b=if s=oldq k (430+93*k) ∧ b=none then _ else if s=oldq k (613+93*k) ∧ b=none then _ else _
  by_cases a : s=(CanonicalLeaf.machine k).accept
  · subst s
    rw [if_neg (by tauto),if_neg (by tauto),UniformTM.step_accept]
    exact (machine k).step_accept b
  by_cases r : s=(CanonicalLeaf.machine k).reject
  · subst s
    rw [if_neg (by tauto),if_neg (by tauto),UniformTM.step_reject]
    exact (machine k).step_reject b
  have na : embed k s ≠ (machine k).accept := fun h => a (inject k h)
  have nr : embed k s ≠ (machine k).reject := fun h => r (inject k h)
  rw [UniformTM.step_of_ne (machine k) na nr]
  change rows k (embed k s) b=_
  dsimp only [rows,embed]
  rw [dif_pos s.isLt]
  rfl
private theorem native_row (k : Nat) (j : Fin 25) (b : Option Bool) :
    (machine k).step (extra k j) b=native k j b := by
  have a : extra k j ≠ (machine k).accept := (disjoint k _ j).symm
  have r : extra k j ≠ (machine k).reject := (disjoint k _ j).symm
  rw [UniformTM.step_of_ne (machine k) a r]
  change rows k (extra k j) b=_
  dsimp only [rows,extra]
  rw [dif_neg (by omega)]
  congr 1
  apply Fin.ext
  change (CanonicalLeaf.machine k).stateCount+j.val-(CanonicalLeaf.machine k).stateCount=j.val
  omega
/-- Original verdicts and state injection are retained literally. -/
theorem controls (k : Nat) :
    (machine k).stateCount=(CanonicalLeaf.machine k).stateCount+25 ∧
    (machine k).start=embed k (CanonicalLeaf.machine k).start ∧
    (machine k).accept=embed k (CanonicalLeaf.machine k).accept ∧
    (machine k).reject=embed k (CanonicalLeaf.machine k).reject ∧
    Function.Injective (embed k) := ⟨rfl,rfl,rfl,rfl,fun _ _ h => inject k h⟩
/-- The existing producer138/read-none repair is preserved, for every k. -/
theorem repair138 (k : Nat) :
    (machine k).step (embed k (VirtualLeaf.embed k
      (IngressRepair.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138)))) none=
        ((machine k).reject,none,.stay) := by
  rw [table_delta]
  have low (i : Nat) (hi : i < Cursor.stateCount k) :
      VirtualLeaf.embed k (IngressRepair.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138)) ≠ oldq k i := by
    intro h; have e:=congrArg Fin.val h; rw [oldq_val k i hi] at e
    change 138=288+i at e; omega
  rw [if_neg (by exact fun h => low _ (by unfold Cursor.stateCount; omega) h.1),
      if_neg (by exact fun h => low _ (by unfold Cursor.stateCount; omega) h.1),CanonicalLeaf.repair138]
  rfl
end CarryWindow
