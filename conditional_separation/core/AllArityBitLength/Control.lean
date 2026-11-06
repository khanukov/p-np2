import AllArityBitLength.Rows
import Complexity.PrivateInterfaceLookupResolvedControl
import CappedWorkspace.Rows
namespace AllArityBitLength
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
elab "fromDonor " mod:str ns:str key:str " => " tac:tacticSeq : tactic => do
  let names := [← PartAPrivateControl.selectText mod.getString ns.getString key.getString]
  unless names.length=1 do throwError "Ambiguous immutable ordinary term: {names}"
  logInfo m!"private-term|{names.head!}"
  evalTactic (tac.raw.rewriteBottomUp fun stx =>
    if stx.isIdent && stx.getId.toString=="OLD" then mkIdent names.head! else stx)
private theorem decoded_bound (xs : List Nat) (lo hi i : Nat) (b : Option Bool)
    (len : xs.length=3*(hi-lo)) (hl : lo ≤ i) (hu : i < hi)
    (checked : (xs.zipIdx.all fun z =>
      if (250 ≤ z.2/3+lo ∧ z.2/3+lo < 254) ∨ (304 ≤ z.2/3+lo ∧ z.2/3+lo < 308) then true else decide (z.1/9=40 ∨ (lo ≤ z.1/9 ∧ z.1/9 ≤ hi ∧ (z.1/9 ≤ 250 ∨ 254 ≤ z.1/9) ∧ (z.1/9 ≤ 304 ∨ 308 ≤ z.1/9))))=true)
    (h250 : i < 250 ∨ 254 ≤ i) (h304 : i < 304 ∨ 308 ≤ i) :
    let code := xs[3*(i-lo)+(match (generalizing := false) b with | none => 0 | some false => 1 | some true => 2)]!
    code/9=40 ∨ (lo ≤ code/9 ∧ code/9 ≤ hi ∧ (code/9 ≤ 250 ∨ 254 ≤ code/9) ∧ (code/9 ≤ 304 ∨ 308 ≤ code/9)) := by
  let sym := match (generalizing := false) b with | none => 0 | some false => 1 | some true => 2
  let j := 3*(i-lo)+sym
  have hs : sym < 3 := by cases b with | none => decide | some b => cases b <;> decide
  have hj : j < xs.length := by dsimp only [j]; omega
  have div : j/3+lo=i := by dsimp only [j]; omega
  have got : xs[j]?=some xs[j]! := by simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
  have mem : (xs[j]!,j) ∈ xs.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr got
  have v := (List.all_eq_true.mp checked) _ mem
  have excluded : ¬((250 ≤ j/3+lo ∧ j/3+lo < 254) ∨ (304 ≤ j/3+lo ∧ j/3+lo < 308)) := by omega
  rw [if_neg excluded] at v
  exact of_decide_eq_true v
private theorem next_bound (k lo hi : Nat) (band : (lo=98 ∧ hi=201) ∨ (lo=201 ∧ hi=308))
    (s : Fin (Cursor.stateCount k)) (b : Option Bool)
    (hs : s.val=40 ∨ (lo ≤ s.val ∧ s.val < hi)) (h250 : s.val < 250 ∨ 254 ≤ s.val) (h304 : s.val < 304 ∨ 308 ≤ s.val) :
    ((Cursor.machine k).step s b).1.val=40 ∨
      (lo ≤ ((Cursor.machine k).step s b).1.val ∧ ((Cursor.machine k).step s b).1.val ≤ hi ∧
       (((Cursor.machine k).step s b).1.val ≤ 250 ∨ 254 ≤ ((Cursor.machine k).step s b).1.val) ∧
       (((Cursor.machine k).step s b).1.val ≤ 304 ∨ 308 ≤ ((Cursor.machine k).step s b).1.val)) := by
  rcases hs with stop|hs
  · have eq : s=(Cursor.machine k).reject := by apply Fin.ext; change s.val=40%Cursor.stateCount k; rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]; exact stop
    rw [eq,UniformTM.step_reject]; exact Or.inl (by change 40 % Cursor.stateCount k=40; exact Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega))
  · have state : s=Cursor.q k s.val := by apply Fin.ext; exact (Nat.mod_eq_of_lt s.isLt).symm
    rw [state]
    rcases band with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have raw : (CappedWorkspace.instructions.zipIdx.all fun z =>
          if (250 ≤ z.2/3+98 ∧ z.2/3+98 < 254) ∨ (304 ≤ z.2/3+98 ∧ z.2/3+98 < 308) then true else decide (z.1/9=40 ∨ (98 ≤ z.1/9 ∧ z.1/9 ≤ 201 ∧ (z.1/9 ≤ 250 ∨ 254 ≤ z.1/9) ∧ (z.1/9 ≤ 304 ∨ 308 ≤ z.1/9))))=true := by rfl
      have h := decoded_bound CappedWorkspace.instructions 98 201 s.val b rfl hs.1 hs.2 raw h250 h304
      fromDonor "CappedWorkspace.Kernel" "CappedWorkspace" "row_value" =>
        have row := OLD k s.val b hs.1 hs.2
      rw [row]
      have hmod : ∀ d, d=40 ∨ (98 ≤ d ∧ d ≤ 201 ∧ (d ≤ 250 ∨ 254 ≤ d) ∧ (d ≤ 304 ∨ 308 ≤ d)) → (Cursor.q k d).val=d := by
        intro d hd; exact Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
      let code : Nat := CappedWorkspace.instructions[3*(s.val-98)+(match (generalizing := false) b with | none => 0 | some false => 1 | some true => 2)]!
      have bound : code/9=40 ∨ (98 ≤ code/9 ∧ code/9 ≤ 201 ∧ (code/9 ≤ 250 ∨ 254 ≤ code/9) ∧ (code/9 ≤ 304 ∨ 308 ≤ code/9)) := h
      have hm : (Cursor.q k (code/9)).val=code/9 := hmod (code/9) bound
      exact hm.symm ▸ bound
    · have raw : ((BitLengthDriver.instructions k).zipIdx.all fun z =>
          if (250 ≤ z.2/3+201 ∧ z.2/3+201 < 254) ∨ (304 ≤ z.2/3+201 ∧ z.2/3+201 < 308) then true else decide (z.1/9=40 ∨ (201 ≤ z.1/9 ∧ z.1/9 ≤ 308 ∧ (z.1/9 ≤ 250 ∨ 254 ≤ z.1/9) ∧ (z.1/9 ≤ 304 ∨ 308 ≤ z.1/9))))=true := by
        run_tac withMainContext do
          let g ← getMainGoal
          Lean.Meta.withTransparency .all g.applyRfl
      have h := decoded_bound (BitLengthDriver.instructions k) 201 308 s.val b rfl hs.1 hs.2 raw h250 h304
      fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "row_value" =>
        have row := OLD k s.val b hs.1 hs.2
      rw [row]
      have hmod : ∀ d, d=40 ∨ (201 ≤ d ∧ d ≤ 308 ∧ (d ≤ 250 ∨ 254 ≤ d) ∧ (d ≤ 304 ∨ 308 ≤ d)) → (Cursor.q k d).val=d := by
        intro d hd; exact Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
      let code : Nat := (BitLengthDriver.instructions k)[3*(s.val-201)+(match (generalizing := false) b with | none => 0 | some false => 1 | some true => 2)]!
      have bound : code/9=40 ∨ (201 ≤ code/9 ∧ code/9 ≤ 308 ∧ (code/9 ≤ 250 ∨ 254 ≤ code/9) ∧ (code/9 ≤ 304 ∨ 308 ≤ code/9)) := h
      have hm : (Cursor.q k (code/9)).val=code/9 := hmod (code/9) bound
      exact hm.symm ▸ bound
/-- Finite-row control ceiling, independent of any semantic tape assumptions. -/
theorem control_before {k N B lo hi t : Nat} (c : Config (Cursor.machine k).stateCount N B)
    (band : (lo=98 ∧ hi=201) ∨ (lo=201 ∧ hi=308))
    (start : c.state.val=40 ∨ (lo ≤ c.state.val ∧ c.state.val ≤ hi ∧ (c.state.val ≤ 250 ∨ 254 ≤ c.state.val) ∧ (c.state.val ≤ 304 ∨ 308 ≤ c.state.val)))
    (guard : ∀ u, u < t → ((Cursor.machine k).run u c).state.val ≠ hi ∧
      (hi=308 → ((Cursor.machine k).run u c).state.val ≠ 250 ∧ ((Cursor.machine k).run u c).state.val ≠ 304)) :
    ∀ u, u < t → ((Cursor.machine k).run u c).state.val < 329 := by
  have inv : ∀ u, u ≤ t → ((Cursor.machine k).run u c).state.val=40 ∨
      (lo ≤ ((Cursor.machine k).run u c).state.val ∧ ((Cursor.machine k).run u c).state.val ≤ hi ∧
       (((Cursor.machine k).run u c).state.val ≤ 250 ∨ 254 ≤ ((Cursor.machine k).run u c).state.val) ∧
       (((Cursor.machine k).run u c).state.val ≤ 304 ∨ 308 ≤ ((Cursor.machine k).run u c).state.val)) := by
    intro u
    induction u with
    | zero => intro _; exact start
    | succ u ih =>
      intro hu
      have old := ih (by omega)
      have g := guard u (by omega)
      have next := next_bound k lo hi band ((Cursor.machine k).run u c).state
        (((Cursor.machine k).run u c).tape ((Cursor.machine k).run u c).head)
        (by rcases old with h|h; exact Or.inl h; exact Or.inr ⟨h.1,by omega⟩)
        (by
          rcases old with h|h
          · omega
          · rcases band with hband|hband
            · rcases hband with ⟨rfl,rfl⟩; omega
            · have no := (g.2 hband.2).1; omega)
        (by
          rcases old with h|h
          · omega
          · rcases band with hband|hband
            · rcases hband with ⟨rfl,rfl⟩; omega
            · have no := (g.2 hband.2).2; omega)
      rw [show u+1=u+1 from rfl,UniformTM.run_add]
      exact next
  intro u hu
  have v := inv u (by omega)
  rcases band with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
end AllArityBitLength
