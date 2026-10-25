import PhysicalCallerClosure.RoundFrame
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","NativeSafe"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior"]),(`PhysicalCallerClosure.ResetImage,["extD"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem image_grid : ∀ (T : Nat → Option Bool) (F r n g W anchor nodes used rem quota : Nat)
    (_endBlank:T (SerializedBody.delimiter F r n 12+6)=none)
    (_metadata:∀ i,SerializedBody.delimiter F r n 12 < i → i < SerializedBody.delimiter F r n 12+6 → ∃ b,T i=some b),
    (∀ j,j < 13 → extD F r n j < extD F r n (j+1)) ∧
    (∀ a b,a ≤ b → b ≤ 13 → extD F r n a ≤ extD F r n b) ∧
    (∀ j,j ≤ 13 → SerializedBody.image T F r n g W anchor nodes used rem quota (extD F r n j)=none) ∧
    (∀ j i,j < 13 → extD F r n j < i → i < extD F r n (j+1) →
      ∃ b,SerializedBody.image T F r n g W anchor nodes used rem quota i=some b) := by run_tac select `PhysicalCallerClosure.ResetFrame "image_grid" "theorem"
private abbrev gridMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 13 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b) →
    (∀ j,j ≤ 13 → T (D j)=none) → (∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b) → Grid D T := by
  run_tac select `PhysicalCallerClosure.Engine "Grid.mk" "constructor"
private theorem image_facts (T E : Nat → Option Bool) (S z n F r g W M p q nodes used rem quota : Nat)
    (beta : Fin n → Bool) (bits : Fin 5 → Bool) (th ah : Bool)
    (frame:Exterior T E S z n F r M p q beta bits th ah)
    (arena:S+z+n+3+q < F) (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T F=some false)
    (endBlank:T (SerializedBody.delimiter F r n 12+6)=none) :
    let I:=SerializedBody.image E F r n g W (S-min M S) nodes used rem quota
    Grid (extD F r n) I ∧ I S=none ∧
    (∀ i,S < i → i < S+z+2 → I i=some false) ∧ I (S+z+2)=none ∧ I (S+z+n+3)=none ∧
    (∀ j:Fin n,I (S+z+n+2-j.val)=some (beta j)) ∧
    (∀ i,S+z+n+3 < i → i ≤ S+z+n+3+q → I i=some true) ∧
    (∀ i,S+z+n+3+q < i → i < F → I i=none) ∧ I F=some false ∧
    (∀ j:Fin 5,I (SerializedBody.delimiter F r n 12+1+j.val)=some (bits j)) ∧
    I (SerializedBody.delimiter F r n 12+6)=none := by
  dsimp only
  rcases frame with ⟨_es,ee,er,el,eh,eb,em,ef,metadata,high⟩
  have low (i) (hi:i ≤ F) : SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i=E i:=by
    unfold SerializedBody.image
    rw [if_pos (Or.inl (show i < SerializedBody.delimiter F r n 0 by change i < F+1;omega))]
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
  refine ⟨gridMk rise mono blank cells,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [low S (by omega),ee,eof]
  · intro i lo hi;rw [low i (by omega),er i lo hi,reg i lo hi]
  · rw [low _ (by omega),el,left]
  · rw [low _ (by omega),eh,right]
  · intro j;have hj:=j.isLt;rw [low _ (by omega)];exact eb j
  · intro i lo hi;rw [low i (by omega),em i lo (by omega),if_pos hi]
  · intro i lo hi;rw [low i (by omega),em i (by omega) hi,if_neg (by omega)]
  · rw [low F le_rfl,ef,fence]
  · intro j
    unfold SerializedBody.image
    rw [if_pos (Or.inr (show SerializedBody.delimiter F r n 12 < SerializedBody.delimiter F r n 12+1+j.val by omega))]
    exact metadata j
  · unfold SerializedBody.image
    rw [if_pos (Or.inr (show SerializedBody.delimiter F r n 12 < SerializedBody.delimiter F r n 12+6 by omega))]
    exact (high _ le_rfl).trans endBlank
end PhysicalCallerClosure
