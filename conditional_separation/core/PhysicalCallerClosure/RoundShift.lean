import PhysicalCallerClosure.RoundGrid
import PhysicalCallerClosure.ShiftRows
import PhysicalCallerClosure.SourceInitialize
import PhysicalCallerClosure.PaymentIncrement
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","NativeSafe","put","ns"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior","shiftSource"]),
      (`PhysicalCallerClosure.CallerMemory,["update","image_update"]),
      (`PhysicalCallerClosure.RoundGrid,["image_facts"]),
      (`PhysicalCallerClosure.Compare,["flags"]),(`PhysicalCallerClosure.PaymentIncrement,["nextRow"]),
      (`PhysicalCallerClosure.WriteReset,["writerEntry"]),(`PhysicalCallerClosure.ShiftSource,["ShiftRows","shift_table"]),
      (`PhysicalCallerClosure.SourceInitialize,["tag_from_source"]),(`PhysicalCallerClosure.RowTape,["d12_lower"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private abbrev code_1527 : ∀ k : Nat,ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true false
    (ns k 1527) (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.ShiftRows "code_1527" "definition"
private abbrev code_2758 : ∀ k : Nat,ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true true
    (ns k 2758) (fun j:Fin 3=>ns k (#[399,440,481][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.ShiftRows "code_2758" "definition"
private abbrev code_1764 : ∀ k : Nat,ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true false
    (ns k 1764) (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.ShiftRows "code_1764" "definition"
private abbrev code_2890 : ∀ k : Nat,ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) true true
    (ns k 2890) (fun j:Fin 3=>ns k (#[868,909,950][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.ShiftRows "code_2890" "definition"
private abbrev code_1929 : ∀ k : Nat,ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) false false
    (ns k 1929) (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.ShiftRows "code_1929" "definition"
private abbrev code_3020 : ∀ k : Nat,ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) false true
    (ns k 3020) (fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!)) := by
  run_tac select `PhysicalCallerClosure.ShiftRows "code_3020" "definition"
private theorem shift_code (k : Nat) (a t : Fin 3) (physical:t.val≠2) :
    Nonempty (ShiftRows (M:=callerMachine k) (Safe:=NativeSafe k) (decide (a.val≠2)) (decide (t.val=1))
      (nextRow k a t) (writerEntry k a)) := by
  fin_cases a <;> fin_cases t
  · have outs:(fun j:Fin 3=>ns k (#[399,440,481][j.val]!))=writerEntry k ⟨0,by decide⟩:=by
      funext j;fin_cases j <;> rfl
    rw [←outs]
    exact ⟨code_1527 k⟩
  · have outs:(fun j:Fin 3=>ns k (#[399,440,481][j.val]!))=writerEntry k ⟨0,by decide⟩:=by
      funext j;fin_cases j <;> rfl
    rw [←outs]
    exact ⟨code_2758 k⟩
  · dsimp only at physical;omega
  · have outs:(fun j:Fin 3=>ns k (#[868,909,950][j.val]!))=writerEntry k ⟨1,by decide⟩:=by
      funext j;fin_cases j <;> rfl
    rw [←outs]
    exact ⟨code_1764 k⟩
  · have outs:(fun j:Fin 3=>ns k (#[868,909,950][j.val]!))=writerEntry k ⟨1,by decide⟩:=by
      funext j;fin_cases j <;> rfl
    rw [←outs]
    exact ⟨code_2890 k⟩
  · dsimp only at physical;omega
  · have outs:(fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!))=writerEntry k ⟨2,by decide⟩:=by
      funext j;fin_cases j <;> rfl
    rw [←outs]
    exact ⟨code_1929 k⟩
  · have outs:(fun j:Fin 3=>ns k (#[1345,1385,1425][j.val]!))=writerEntry k ⟨2,by decide⟩:=by
      funext j;fin_cases j <;> rfl
    rw [←outs]
    exact ⟨code_3020 k⟩
  · dsimp only at physical;omega
private theorem shift_image (T E : Nat → Option Bool) (S z n F r g W M p nodes used rem quota : Nat)
    (bit : Bool) (arena:S+z+n+3 < F) (physical:p < S)
    (value:T p=some bit) (eof:E S=none) :
    put (put (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota) p (some bit)) (p+1) none=
      SerializedBody.image (shiftSource T E S p) F r n g W (S-min M S) nodes used rem quota := by
  have first:=image_update E F r n g W (S-min M S) nodes used rem quota p (some bit)
    (Or.inl (by change p < F+1;omega))
  change update (update (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota) p (some bit)) (p+1) none=_
  rw [first]
  unfold shiftSource
  rw [if_pos physical,value]
  by_cases next:p+1 < S
  · rw [if_pos next]
    exact image_update _ F r n g W (S-min M S) nodes used rem quota (p+1) none
      (Or.inl (by change p+1 < F+1;omega))
  · rw [if_neg next]
    have eq:p+1=S:=by omega
    rw [eq]
    have es:update E p (some bit) S=none:=by rw [update,if_neg (by omega)];exact eof
    have isrc:SerializedBody.image (update E p (some bit)) F r n g W (S-min M S) nodes used rem quota S=none:=by
      unfold SerializedBody.image
      rw [if_pos (Or.inl (show S < SerializedBody.delimiter F r n 0 by change S < F+1;omega))]
      exact es
    funext i
    simp only [update]
    by_cases h:i=S
    · subst i;rw [if_pos rfl,isrc]
    · rw [if_neg h]
private theorem shift_frame (k : Nat) (a t : Fin 3) (T E : Nat → Option Bool)
    (S z n F r g W M p q nodes used rem quota : Nat) (beta : Fin n → Bool) (bits : Fin 5 → Bool)
    (frame:Exterior T E S z n F r M p q beta bits (decide (p < S)) (decide (M < S)))
    (_positive:0 < q) (arena:S+z+n+3+q < F) (before:M < S → p+1 < M-1)
    (source : Fin S → Bool) (src:∀ i,p < i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T F=some false)
    (endBlank:T (SerializedBody.delimiter F r n 12+6)=none)
    (alphaTag:a.val=2 ↔ S ≤ M) (tableTag:t.val=2 ↔ S ≤ p)
    (tv:p < S → T p=some (decide (t.val=1))) :
    ∃ price,price ≤ 2*(S+z+n+3)+7 ∧
      Path (callerMachine k) (NativeSafe k) (SerializedBody.delimiter F r n 12+6) price
        (node (nextRow k a t) (S+z+n+3)
          (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota))
        (node (writerEntry k a (SerializedBody.sourceMode source (p+1))) (S+z+n+3)
          (SerializedBody.image (shiftSource T E S p) F r n g W (S-min M S) nodes used rem quota)) := by
  let H:=S+z+n+3
  let I:=SerializedBody.image E F r n g W (S-min M S) nodes used rem quota
  obtain ⟨_grid,ts,registers,tl,th,betaCells,_marks,_gap,_tf,_metadata,_end⟩:=image_facts T E S z n F r g W M p q nodes used rem quota
    beta bits _ _ frame arena eof reg left right fence endBlank
  have dl:=d12_lower F r n
  rcases frame with ⟨es,ee,_er,_el,_eh,_eb,_em,_ef,_metadataE,_high⟩
  have low (i) (hi:i < S) : I i=E i:=by
    unfold I SerializedBody.image
    rw [if_pos (Or.inl (show i < SerializedBody.delimiter F r n 0 by change i < F+1;omega))]
  by_cases hp:p < S
  · have nt:t.val≠2:=by omega
    have tp:I p=none:=by rw [low p hp,es p hp];simp [hp]
    have sourceI:∀ i,p < i → i < S → (decide (a.val≠2)=false ∨ i≠M-1) → ∃ b,I i=some b:=by
      intro i lo hi skip
      rw [low i hi,es i hi]
      have no:¬((decide (p < S)=true ∧ i=p) ∨ (decide (M < S)=true ∧ i=M-1)):=by
        simp only [decide_eq_true_eq]
        rcases skip with h|h
        · have ha:a.val=2:=by
            by_contra ne
            have hh:decide (a.val≠2)=true:=decide_eq_true ne
            rw [hh] at h
            contradiction
          have hm:=alphaTag.mp ha;omega
        · omega
      rw [if_neg no]
      exact ⟨_,src i lo hi⟩
    have anchor:decide (a.val≠2)=true → p+1 < M-1 ∧ M-1 < S ∧ I (M-1)=none:=by
      intro ha
      have ha':a.val≠2:=of_decide_eq_true ha
      have hm:M < S:=by omega
      have be:=before hm
      refine ⟨be,by omega,?_⟩
      rw [low _ (by omega),es _ (by omega)]
      simp [hm]
    have occupiedBeta:∀ i,S+z+2 < i → i < H → ∃ b,I i=some b:=by
      intro i lo hi
      let j:=S+z+n+2-i
      have hj:j < n:=by dsimp only [H,j] at *;omega
      have pos:S+z+n+2-j=i:=by dsimp only [H,j] at *;omega
      have be:=betaCells ⟨j,hj⟩
      rw [pos] at be
      exact ⟨_,be⟩
    obtain ⟨code⟩:=shift_code k a t nt
    obtain ⟨tag,virtual,bit,path⟩:=shift_table (P:=SerializedBody.delimiter F r n 12+6)
      (anchor:=M-1) hp (by omega) (show S+z+2 < H by dsimp only [H];omega)
      (by dsimp only [H];omega) tp ts tl th sourceI anchor
      (by intro i lo hi;exact ⟨false,registers i lo hi⟩) occupiedBeta code
    have cell:∀ hn:p+1 < S,I (p+1)=some (source ⟨p+1,hn⟩):=by
      intro hn
      rw [low _ hn,es _ hn]
      have no:¬((decide (p < S)=true ∧ p+1=p) ∨ (decide (M < S)=true ∧ p+1=M-1)):=by
        simp only [decide_eq_true_eq]
        by_cases hm:M < S
        · have be:=before hm;omega
        · omega
      rw [if_neg no];exact src _ (by omega) hn
    have tagEq:=tag_from_source source I tag (by omega) ts cell virtual bit
    rw [tagEq] at path
    have restored:=shift_image T E S z n F r g W M p nodes used rem quota _ (by omega) hp (tv hp) (ee.trans eof)
    rw [restored] at path
    exact ⟨2*(H-p)+(if decide (a.val≠2) then 7 else 6),by split_ifs <;> omega,path⟩
  · have ht:t=⟨2,by decide⟩:=by apply Fin.ext;change t.val=2;exact tableTag.mpr (by omega)
    have virtual:SerializedBody.sourceMode source (p+1)=⟨2,by decide⟩:=by
      unfold SerializedBody.sourceMode
      rw [dif_neg (show ¬p+1 < S by omega)]
    have shiftEq:shiftSource T E S p=E:=by unfold shiftSource;rw [if_neg hp,if_neg (show ¬p+1 < S by omega)]
    rw [ht,virtual,shiftEq]
    have eq:nextRow k a ⟨2,by decide⟩=writerEntry k a ⟨2,by decide⟩:=by fin_cases a <;> rfl
    rw [eq]
    exact ⟨0,by omega,Path.nil _ (by dsimp only [H];omega)⟩
end PhysicalCallerClosure
