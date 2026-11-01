import PhysicalCallerClosure.RoundImage
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
      (`PhysicalCallerClosure.RoundImage,["frame_image_eq","canonical_frame"]),
      (`PhysicalCallerClosure.CallerMemory,["update","caller_image","image_update","written_image"]),
      (`PhysicalCallerClosure.Compare,["flags"]),
      (`PhysicalCallerClosure.WriteBits,["written","written_outside","written_value"]),
      (`PhysicalCallerClosure.RowTape,["rowExternal","d12_lower","external_meta"]),
      (`PhysicalCallerClosure.CallerTarget,["rowImage"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem canonical_image (T : Nat → Option Bool) (S z n F r g W M p q nodes used rem quota : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F) :
    SerializedBody.image (rowExternal T S z n F r M p q beta a t last) F r n g W (S-min M S) nodes used rem quota=
      let V:=written (callerImage T S z n F r g W M q beta nodes used rem quota)
        (SerializedBody.delimiter F r n 12) (flags a t last) 5
      let U:=if M < S then update V (M-1) none else V
      if p < S then update U p none else U := by
  dsimp only
  have pull (E : Nat → Option Bool) (i) (hi:i < S) :
      SerializedBody.image (update E i none) F r n g W (S-min M S) nodes used rem quota=
        update (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota) i none:=by
    symm;exact image_update E F r n g W (S-min M S) nodes used rem quota i none (Or.inl (by change i < F+1;omega))
  unfold rowExternal
  by_cases hp:p < S
  · rw [if_pos hp,pull _ _ hp]
    by_cases hm:M < S
    · rw [if_pos hm,pull _ _ (by omega),←written_image,←caller_image T S z n F r g W M q nodes used rem quota beta arena];simp only [hp,hm,if_true]
    · rw [if_neg hm,←written_image,←caller_image T S z n F r g W M q nodes used rem quota beta arena];simp only [hp,hm,if_true,if_false]
  · rw [if_neg hp]
    by_cases hm:M < S
    · rw [if_pos hm,pull _ _ (by omega),←written_image,←caller_image T S z n F r g W M q nodes used rem quota beta arena];simp only [hp,hm,if_true,if_false]
    · rw [if_neg hm,←written_image,←caller_image T S z n F r g W M q nodes used rem quota beta arena];simp only [hp,hm,if_false]
private theorem hole_order (C : Nat → Option Bool) (S M p i : Nat) :
    (if i=M ∧ i < S then none else
      (if p < S then update (if M < S then update C (M-1) none else C) p none
        else if M < S then update C (M-1) none else C) i)=
      if i=p ∧ i < S then none else if M < S ∧ i=M-1 then none else
        if i=M ∧ i < S then none else C i := by
  have mi:(i=M ∧ i < S) ↔ (i=M ∧ M < S):=by omega
  have pi:(i=p ∧ i < S) ↔ (i=p ∧ p < S):=by omega
  simp only [mi,pi]
  by_cases hm:M < S <;> by_cases hp:p < S
  all_goals simp only [hm,hp,if_true,if_false,true_and,and_true,and_false]
  all_goals try dsimp only [update]
  all_goals split_ifs <;> first | rfl | aesop
private theorem entry_image (T E : Nat → Option Bool) (S z n F r g W M A Q row : Nat)
    (source : Fin S → Bool) (a t : Fin 3) (arena:S+z+n+3 < F)
    (frame:Exterior T E S z n F r M (A+row) (max 1 (Q-row)) (Pnp3.Core.vecOfNat n row) (flags a t false)
      (decide (A+row < S)) (decide (M < S)))
    (alphaTag:a.val=2 ↔ S ≤ M) (tableTag:t.val=2 ↔ S ≤ A+row)
    (anchorBit:decide (a.val=1)=(if M < S then padRead source (M-1) else false))
    (tableBit:decide (t.val=1)=padRead source (A+row)) :
    SerializedBody.prepared E S M F r n g W=rowImage T S z n F r g W M A Q row source := by
  have dl:=d12_lower F r n
  have im:=frame_image_eq T E (rowExternal T S z n F r M (A+row) (max 1 (Q-row)) (Pnp3.Core.vecOfNat n row) a t false)
    S z n F r g W M (A+row) (max 1 (Q-row)) 0 0 W g _ _ _ _ arena frame
    (canonical_frame T S z n F r M (A+row) (max 1 (Q-row)) _ a t false arena)
  rw [canonical_image T S z n F r g W M (A+row) (max 1 (Q-row)) 0 0 W g _ a t false arena] at im
  let d:=SerializedBody.delimiter F r n 12
  let C:=callerImage T S z n F r g W M (max 1 (Q-row)) (Pnp3.Core.vecOfNat n row) 0 0 W g
  have flag0:flags a t false ⟨0,by decide⟩=decide (S ≤ A+row):=by
    change decide (t.val=2)=decide (S ≤ A+row)
    by_cases ht:t.val=2
    · simp only [decide_eq_true ht,decide_eq_true (tableTag.mp ht)]
    · have hn:¬S ≤ A+row:=by intro h;exact ht (tableTag.mpr h)
      simp only [decide_eq_false ht,decide_eq_false hn]
  have flag1:flags a t false ⟨1,by decide⟩=padRead source (A+row):=tableBit
  have flag2:flags a t false ⟨2,by decide⟩=decide (S ≤ M):=by
    change decide (a.val=2)=decide (S ≤ M)
    by_cases ht:a.val=2
    · simp only [decide_eq_true ht,decide_eq_true (alphaTag.mp ht)]
    · have hn:¬S ≤ M:=by intro h;exact ht (alphaTag.mpr h)
      simp only [decide_eq_false ht,decide_eq_false hn]
  have flag3:flags a t false ⟨3,by decide⟩=(if M < S then padRead source (M-1) else false):=anchorBit
  have flag4:flags a t false ⟨4,by decide⟩=false:=rfl
  have atMeta (j:Fin 5) : SerializedBody.prepared E S M F r n g W (d+1+j.val)=some (flags a t false j):=by
    unfold SerializedBody.prepared
    rw [if_neg (by dsimp only [d] at *;have hj:=j.isLt;omega)]
    rw [congrFun im (d+1+j.val)]
    change (if A+row < S then update _ (A+row) none else _) (d+1+j.val)=_
    by_cases hp:A+row < S
    · rw [if_pos hp,update,if_neg (by dsimp only [d] at *;omega)]
      by_cases hm:M < S
      · rw [if_pos hm,update,if_neg (by dsimp only [d] at *;omega)]
        exact written_value C d (flags a t false) j
      · rw [if_neg hm];exact written_value C d (flags a t false) j
    · rw [if_neg hp]
      by_cases hm:M < S
      · rw [if_pos hm,update,if_neg (by dsimp only [d] at *;omega)]
        exact written_value C d (flags a t false) j
      · rw [if_neg hm];exact written_value C d (flags a t false) j
  funext i
  by_cases m0:i=d+1
  · subst i
    have e:=atMeta ⟨0,by decide⟩
    change SerializedBody.prepared E S M F r n g W (d+1)=some (flags a t false ⟨0,by decide⟩) at e
    rw [e,flag0]
    unfold rowImage
    rw [if_pos (show d+1=SerializedBody.delimiter F r n 12+1 by rfl)]
  · by_cases m1:i=d+2
    · subst i
      have e:=atMeta ⟨1,by decide⟩
      change SerializedBody.prepared E S M F r n g W (d+2)=some (flags a t false ⟨1,by decide⟩) at e
      rw [e,flag1]
      unfold rowImage
      rw [if_neg m0,if_pos (show d+2=SerializedBody.delimiter F r n 12+2 by rfl)]
    · by_cases m2:i=d+3
      · subst i
        have e:=atMeta ⟨2,by decide⟩
        change SerializedBody.prepared E S M F r n g W (d+3)=some (flags a t false ⟨2,by decide⟩) at e
        rw [e,flag2]
        unfold rowImage
        rw [if_neg m0,if_neg m1,if_pos (show d+3=SerializedBody.delimiter F r n 12+3 by rfl)]
      · by_cases m3:i=d+4
        · subst i
          have e:=atMeta ⟨3,by decide⟩
          change SerializedBody.prepared E S M F r n g W (d+4)=some (flags a t false ⟨3,by decide⟩) at e
          rw [e,flag3]
          unfold rowImage
          rw [if_neg m0,if_neg m1,if_neg m2,if_pos (show d+4=SerializedBody.delimiter F r n 12+4 by rfl)]
        · by_cases m4:i=d+5
          · subst i
            have e:=atMeta ⟨4,by decide⟩
            change SerializedBody.prepared E S M F r n g W (d+5)=some (flags a t false ⟨4,by decide⟩) at e
            rw [e,flag4]
            unfold rowImage
            rw [if_neg m0,if_neg m1,if_neg m2,if_neg m3,if_pos (show d+5=SerializedBody.delimiter F r n 12+5 by rfl)]
          · have nw:i ≤ d ∨ d+6 ≤ i:=by omega
            unfold SerializedBody.prepared
            rw [congrFun im i]
            unfold rowImage
            rw [if_neg m0,if_neg m1,if_neg m2,if_neg m3,if_neg m4]
            change (if i=M ∧ i < S then none else
              (if A+row < S then update (if M < S then update (written C d (flags a t false) 5) (M-1) none else written C d (flags a t false) 5) (A+row) none
                else if M < S then update (written C d (flags a t false) 5) (M-1) none else written C d (flags a t false) 5) i)=_
            have order:=hole_order (written C d (flags a t false) 5) S M (A+row) i
            simpa only [written_outside nw] using order
end PhysicalCallerClosure
