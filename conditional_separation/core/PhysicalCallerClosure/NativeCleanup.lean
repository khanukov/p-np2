import PhysicalCallerClosure.RoundFrame
import PhysicalCallerClosure.Cleanup
import PhysicalCallerClosure.ResetFrame
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","NativeSafe"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior","clearSource","final_image"]),
      (`PhysicalCallerClosure.CallerMemory,["update","image_update","written_image"]),
      (`PhysicalCallerClosure.Engine,["put"]),
      (`PhysicalCallerClosure.WriteMeta,["FrontGrid"]),(`PhysicalCallerClosure.WriteBits,["written"]),
      (`PhysicalCallerClosure.Cleanup,["restored","cleanupEntry","finishState"]),
      (`PhysicalCallerClosure.ResetImage,["extD"]),(`PhysicalCallerClosure.RowTape,["d12_lower"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private abbrev frontMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 12 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) →
    (∀ j,j ≤ 12 → T (D j)=none) → (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) → FrontGrid D T := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.mk" "constructor"
private theorem cleanup_path : ∀ (k : Nat) (done : Bool) (a t : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (p anchor S L H Q F P : Nat) (_grid:FrontGrid D T) (_d0:D 0=F+1) (_width:D 13=D 12+6)
    (_endBlank:T (D 13)=none) (_room:D 13 ≤ P) (_positive:0 < Q) (_arena:H+Q < F)
    (_sl:S < L) (_lh:L < H) (_ts:T S=none) (_tl:T L=none) (_th:T H=none)
    (_anchorFacts:a.val≠2 → anchor < S ∧ T anchor=none ∧ ∀ i,anchor < i → i < S → ∃ b,T i=some b)
    (_tableFacts:t.val≠2 → p < S ∧ T p=none ∧ ∀ i,p < i → i < S → (a.val=2 ∨ i≠anchor) → ∃ b,T i=some b)
    (_order:a.val≠2 → t.val≠2 → p < anchor)
    (_reg:∀ i,S < i → i < L → ∃ b,T i=some b) (_beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (_tf:T F=some false) (_marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (_gap:∀ i,H+Q < i → i < F → T i=none),
    ∃ price,price ≤ 64*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P price
      (node (cleanupEntry k done a t) H T)
      (node (finishState k done) H (written (restored T p anchor a t) (D 12) (fun _=>false) 5)) := by run_tac select `PhysicalCallerClosure.Cleanup "cleanup_path" "theorem"
private theorem image_grid : ∀ (T : Nat → Option Bool) (F r n g W anchor nodes used rem quota : Nat)
    (_endBlank:T (SerializedBody.delimiter F r n 12+6)=none)
    (_metadata:∀ i,SerializedBody.delimiter F r n 12 < i → i < SerializedBody.delimiter F r n 12+6 → ∃ b,T i=some b),
    (∀ j,j < 13 → extD F r n j < extD F r n (j+1)) ∧
    (∀ a b,a ≤ b → b ≤ 13 → extD F r n a ≤ extD F r n b) ∧
    (∀ j,j ≤ 13 → SerializedBody.image T F r n g W anchor nodes used rem quota (extD F r n j)=none) ∧
    (∀ j i,j < 13 → extD F r n j < i → i < extD F r n (j+1) →
      ∃ b,SerializedBody.image T F r n g W anchor nodes used rem quota i=some b) := by run_tac select `PhysicalCallerClosure.ResetFrame "image_grid" "theorem"
private theorem frame_restore : ∀ {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {bits : Fin 5 → Bool},
    Exterior T E S z n F r M p q beta bits (decide (p < S)) (decide (M < S)) → S+z+n+3 < F →
    Exterior T (clearSource T E S M p) S z n F r M p q beta bits false false := by
  run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.restore" "theorem"
private theorem frame_write : ∀ {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {old : Fin 5 → Bool} {th ah : Bool},
    Exterior T E S z n F r M p q beta old th ah → S+z+n+3 < F → ∀ bits : Fin 5 → Bool,
    Exterior T (written E (SerializedBody.delimiter F r n 12) bits 5) S z n F r M p q beta bits th ah := by
  run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.write" "theorem"
private theorem image_outside (E : Nat → Option Bool) (F r n g W a nodes used rem quota i : Nat)
    (out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i) :
    SerializedBody.image E F r n g W a nodes used rem quota i=E i := by unfold SerializedBody.image;rw [if_pos out]
private theorem restore_image (T E : Nat → Option Bool) (S z n F r g W M p nodes used rem quota : Nat)
    (a t : Fin 3) (arena:S+z+n+3 < F)
    (alphaTag:a.val=2 ↔ S ≤ M) (tableTag:t.val=2 ↔ S ≤ p)
    (av:M < S → T (M-1)=some (decide (a.val=1))) (tv:p < S → T p=some (decide (t.val=1))) :
    restored (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota) p (M-1) a t=
      SerializedBody.image (clearSource T E S M p) F r n g W (S-min M S) nodes used rem quota := by
  have ta:a.val=2 ↔ ¬M < S:=by omega
  have tb:t.val=2 ↔ ¬p < S:=by omega
  unfold restored clearSource
  by_cases hm:M < S
  · have na:a.val≠2:=by omega
    rw [if_neg na,if_pos hm]
    rw [←av hm]
    change (if t.val=2 then _ else _)=_
    rw [show put
        (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota) (M-1) (T (M-1))=
      SerializedBody.image (update E (M-1) (T (M-1)))
        F r n g W (S-min M S) nodes used rem quota by
          exact image_update _ F r n g W (S-min M S) nodes used rem quota _ _
            (Or.inl (by change M-1 < F+1;omega))]
    by_cases hp:p < S
    · have nt:t.val≠2:=by omega
      rw [if_neg nt,if_pos hp,←tv hp]
      exact image_update _ F r n g W (S-min M S) nodes used rem quota _ _
        (Or.inl (by change p < F+1;omega))
    · have et:t.val=2:=by omega
      rw [if_pos et,if_neg hp]
  · have ea:a.val=2:=by omega
    rw [if_pos ea,if_neg hm]
    by_cases hp:p < S
    · have nt:t.val≠2:=by omega
      rw [if_neg nt,if_pos hp,←tv hp]
      exact image_update _ F r n g W (S-min M S) nodes used rem quota _ _
        (Or.inl (by change p < F+1;omega))
    · have et:t.val=2:=by omega
      rw [if_pos et,if_neg hp]

private theorem native_cleanup (k : Nat) (done : Bool) (a t : Fin 3)
    (T E : Nat → Option Bool) (S z n F r g W M p q nodes used rem quota : Nat)
    (beta : Fin n → Bool) (bits : Fin 5 → Bool)
    (frame:Exterior T E S z n F r M p q beta bits (decide (p < S)) (decide (M < S)))
    (positive:0 < q) (arena:S+z+n+3+q < F) (mp:0 < M)
    (order:M < S → p < M-1)
    (source:∀ i,p < i → i < S → ∃ b,T i=some b)
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T F=some false)
    (endBlank:T (SerializedBody.delimiter F r n 12+6)=none)
    (alphaTag:a.val=2 ↔ S ≤ M) (tableTag:t.val=2 ↔ S ≤ p)
    (av:M < S → T (M-1)=some (decide (a.val=1)))
    (tv:p < S → T p=some (decide (t.val=1))) :
    ∃ price,price ≤ 64*(SerializedBody.delimiter F r n 12+7) ∧
      Path (callerMachine k) (NativeSafe k) (SerializedBody.delimiter F r n 12+6) price
        (node (cleanupEntry k done a t) (S+z+n+3)
          (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota))
        (node (finishState k done) (S+z+n+3)
          (callerImage T S z n F r g W M q beta nodes used rem quota)) := by
  let H:=S+z+n+3
  let I:=SerializedBody.image E F r n g W (S-min M S) nodes used rem quota
  let D:=extD F r n
  have keep:=frame
  rcases frame with ⟨es,ee,er,el,eh,eb,em,ef,metadata,high⟩
  have dl:=d12_lower F r n
  have low (i) (hi:i ≤ F) : I i=E i:=image_outside E F r n g W (S-min M S) nodes used rem quota i (Or.inl (by change i < F+1;omega))
  have metaE:∀ i,SerializedBody.delimiter F r n 12 < i → i < SerializedBody.delimiter F r n 12+6 → ∃ b,E i=some b:=by
    intro i lo hi
    let j:=i-SerializedBody.delimiter F r n 12-1
    have hj:j < 5:=by dsimp only [j];omega
    have pos:SerializedBody.delimiter F r n 12+1+j=i:=by dsimp only [j];omega
    have value:=metadata ⟨j,hj⟩
    rw [pos] at value
    exact ⟨_,value⟩
  obtain ⟨rise,mono,blank,cells⟩:=image_grid E F r n g W (S-min M S) nodes used rem quota
    ((high _ le_rfl).trans endBlank) metaE
  have front:FrontGrid D I:=frontMk
    (by intro j hj;exact rise j (by omega))
    (by intro u v uv hv;exact mono u v uv (by omega))
    (by intro j hj;exact blank j (by omega))
    (by intro j i hj lo hi;exact cells j i (by omega) lo hi)
  have anchorFacts:a.val≠2 → M-1 < S ∧ I (M-1)=none ∧ ∀ i,M-1 < i → i < S → ∃ b,I i=some b:=by
    intro ne
    have hm:M < S:=by omega
    have before:=order hm
    refine ⟨by omega,?_,?_⟩
    · rw [low _ (by omega),es _ (by omega)]
      simp [hm]
    · intro i lo hi
      rw [low i (by omega),es i hi,if_neg (by simp only [decide_eq_true_eq];omega)]
      exact source i (by omega) hi
  have tableFacts:t.val≠2 → p < S ∧ I p=none ∧ ∀ i,p < i → i < S → (a.val=2 ∨ i≠M-1) → ∃ b,I i=some b:=by
    intro ne
    have hp:p < S:=by omega
    refine ⟨hp,?_,?_⟩
    · rw [low _ (by omega),es _ hp];simp [hp]
    · intro i lo hi skip
      rw [low i (by omega),es i hi]
      have no:¬((decide (p < S)=true ∧ i=p) ∨ (decide (M < S)=true ∧ i=M-1)):=by
        simp only [decide_eq_true_eq]
        rcases skip with ha|hia
        · have hm:S ≤ M:=alphaTag.mp ha;omega
        · omega
      rw [if_neg no];exact source i lo hi
  have betaCells:∀ i,S+z+2 < i → i < H → ∃ b,I i=some b:=by
    intro i lo hi
    let j:=S+z+n+2-i
    have hj:j < n:=by dsimp only [H,j] at *;omega
    have pos:S+z+n+2-j=i:=by dsimp only [H,j] at *;omega
    have e:=eb ⟨j,hj⟩
    rw [pos] at e
    rw [low i (by dsimp only [H] at hi;omega)]
    exact ⟨_,e⟩
  obtain ⟨price,bound,path⟩:=cleanup_path k done a t D I p (M-1) S (S+z+2) H q F
    (SerializedBody.delimiter F r n 12+6) front rfl rfl
    (by change SerializedBody.image E F r n g W (S-min M S) nodes used rem quota (SerializedBody.delimiter F r n 12+6)=none
        rw [image_outside _ F r n g W (S-min M S) nodes used rem quota _ (Or.inr (by omega)),high _ le_rfl,endBlank])
    le_rfl positive arena (by omega) (by dsimp only [H];omega)
    (by rw [low S (by omega),ee,eof])
    (by rw [low _ (by omega),el,left])
    (by rw [low H (by dsimp only [H];omega),eh,right])
    anchorFacts tableFacts (by intro ha _;exact order (by omega))
    (by intro i lo hi;rw [low i (by omega),er i lo hi];exact ⟨false,reg i lo hi⟩)
    betaCells (by rw [low F le_rfl,ef,fence])
    (by intro i lo hi;rw [low i (by omega),em i lo (by omega),if_pos hi])
    (by intro i lo hi;rw [low i (by omega),em i (by omega) hi,if_neg (by omega)])
  have restoredEq:=restore_image T E S z n F r g W M p nodes used rem quota a t (by omega) alphaTag tableTag av tv
  have finalEq:written (restored I p (M-1) a t) (D 12) (fun _=>false) 5=
      callerImage T S z n F r g W M q beta nodes used rem quota:=by
    change written (restored (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota) p (M-1) a t)
      (SerializedBody.delimiter F r n 12) (fun _=>false) 5=_
    rw [restoredEq,written_image]
    exact final_image T _ S z n F r g W M p q nodes used rem quota beta (by omega)
      (frame_write (frame_restore keep (by omega)) (by omega) (fun _=>false))
  rw [finalEq] at path
  exact ⟨price,by omega,path⟩
end PhysicalCallerClosure
