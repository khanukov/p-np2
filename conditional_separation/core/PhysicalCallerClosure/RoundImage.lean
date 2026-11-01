import PhysicalCallerClosure.RoundFrame
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | .inductInfo _=>"inductive" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.RoundFrame,["Exterior"]),
      (`PhysicalCallerClosure.CallerMemory,["image_inside","update","frameBase"]),
      (`PhysicalCallerClosure.Compare,["flags"]),(`PhysicalCallerClosure.WriteBits,["written","written_outside"]),
      (`PhysicalCallerClosure.RowTape,["rowExternal","d12_lower","external_low","external_table_hole","external_anchor_hole",
        "external_beta","external_meta","external_high","base_outside","external_delimiters","external_marks"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev frameMk : {T E : Nat → Option Bool} → {S z n F r M p q : Nat} →
    {beta : Fin n → Bool} → {bits : Fin 5 → Bool} → {th ah : Bool} →
    (∀ i,i < S → E i=if (th=true ∧ i=p) ∨ (ah=true ∧ i=M-1) then none else T i) →
    E S=T S → (∀ i,S < i → i < S+z+2 → E i=T i) → E (S+z+2)=T (S+z+2) →
    E (S+z+n+3)=T (S+z+n+3) → (∀ j:Fin n,E (S+z+n+2-j.val)=some (beta j)) →
    (∀ i,S+z+n+3 < i → i < F → E i=if i ≤ S+z+n+3+q then some true else none) → E F=T F →
    (∀ j:Fin 5,E (SerializedBody.delimiter F r n 12+1+j.val)=some (bits j)) →
    (∀ i,SerializedBody.delimiter F r n 12+6 ≤ i → E i=T i) →
    Exterior T E S z n F r M p q beta bits th ah := by
  run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.mk" "constructor"
private theorem frame_image_eq (T E U : Nat → Option Bool) (S z n F r g W M p q nodes used rem quota : Nat)
    (beta : Fin n → Bool) (bits : Fin 5 → Bool) (th ah : Bool) (arena:S+z+n+3 < F)
    (ef:Exterior T E S z n F r M p q beta bits th ah) (uf:Exterior T U S z n F r M p q beta bits th ah) :
    SerializedBody.image E F r n g W (S-min M S) nodes used rem quota=
      SerializedBody.image U F r n g W (S-min M S) nodes used rem quota := by
  rcases ef with ⟨es,ee,er,el,eh,eb,em,ef,ed,et⟩
  rcases uf with ⟨us,ue,ur,ul,uh,ub,um,uf,ud,ut⟩
  have dl:=d12_lower F r n
  funext i
  by_cases out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i
  · unfold SerializedBody.image
    rw [if_pos out,if_pos out]
    rcases out with lo|hi
    · have leF:i ≤ F:=by change i < F+1 at lo;omega
      by_cases src:i < S
      · rw [es i src,us i src]
      · by_cases eof:i=S
        · subst i;exact ee.trans ue.symm
        · by_cases reg:i < S+z+2
          · exact (er i (by omega) reg).trans (ur i (by omega) reg).symm
          · by_cases left:i=S+z+2
            · subst i;exact el.trans ul.symm
            · by_cases betaCell:i < S+z+n+3
              · let j:=S+z+n+2-i
                have hj:j < n:=by dsimp only [j];omega
                have pos:S+z+n+2-j=i:=by dsimp only [j];omega
                have e:=eb ⟨j,hj⟩
                have u:=ub ⟨j,hj⟩
                rw [pos] at e u
                exact e.trans u.symm
              · by_cases right:i=S+z+n+3
                · subst i;exact eh.trans uh.symm
                · by_cases fence:i=F
                  · subst i;exact ef.trans uf.symm
                  · rw [em i (by omega) (by omega),um i (by omega) (by omega)]
    · by_cases metaCell:i < SerializedBody.delimiter F r n 12+6
      · let j:=i-SerializedBody.delimiter F r n 12-1
        have hj:j < 5:=by dsimp only [j];omega
        have pos:SerializedBody.delimiter F r n 12+1+j=i:=by dsimp only [j];omega
        have e:=ed ⟨j,hj⟩
        have u:=ud ⟨j,hj⟩
        rw [pos] at e u
        exact e.trans u.symm
      · exact (et i (by omega)).trans (ut i (by omega)).symm
  · exact image_inside E U F r n g W (S-min M S) nodes used rem quota i out
private theorem canonical_frame (T : Nat → Option Bool) (S z n F r M p q : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F) :
    Exterior T (rowExternal T S z n F r M p q beta a t last)
      S z n F r M p q beta (flags a t last) (decide (p < S)) (decide (M < S)) := by
  have dl:=d12_lower F r n
  have delimiters:=external_delimiters T S z n F r M p q beta a t last arena
  have same (i) (hi:S ≤ i) (nb:¬(S+z+2 < i ∧ i < S+z+n+3))
      (nm:¬(S+z+n+3 < i ∧ i < F))
      (nd:¬(SerializedBody.delimiter F r n 12 < i ∧ i < SerializedBody.delimiter F r n 12+6)) :
      rowExternal T S z n F r M p q beta a t last i=T i:=by
    rw [external_high T S z n F r M p q beta a t last i hi,written_outside (by omega)]
    exact base_outside T S z n F r q beta i nb nm nd
  refine frameMk ?_ ?_ ?_ delimiters.1 delimiters.2.1
    (external_beta T S z n F r M p q beta a t last arena)
    (external_marks T S z n F r M p q beta a t last arena) delimiters.2.2.1
    (external_meta T S z n F r M p q beta a t last arena) ?_
  · intro i hi
    by_cases table:i=p ∧ p < S
    · rcases table with ⟨eq,hp⟩
      subst i
      rw [external_table_hole T S z n F r M p q beta a t last hp]
      simp [hp]
    · by_cases anchor:i=M-1 ∧ M < S
      · rcases anchor with ⟨eq,hm⟩
        subst i
        have ne:p≠M-1:=by omega
        rw [external_anchor_hole T S z n F r M p q beta a t last hm ne]
        simp [hm]
      · rw [external_low T S z n F r M p q beta a t last arena i (by omega) (by omega) (by omega)]
        simp only [decide_eq_true_eq]
        rw [if_neg (by omega)]
  · exact same S le_rfl (by omega) (by omega) (by omega)
  · intro i lo hi;exact same i (by omega) (by omega) (by omega) (by omega)
  · intro i hi;exact same i (by omega) (by omega) (by omega) (by omega)
end PhysicalCallerClosure
