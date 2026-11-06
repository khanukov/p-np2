import PhysicalCallerClosure.ResetImage
import PhysicalCallerClosure.CopySurface
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic Command
private def checkedCase (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.SerializedBodyCompletion.Case 0) "SerializedBodyCompletion")
  let some ci:=e.find? n | throwError "Missing exact image term {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | _=>"other"
  unless actual==kind do throwError "Wrong image term kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `SerializedBodyCompletion.Case do throwError "Wrong image term owner"
  logInfo m!"caller-image-adapter|{n}|{ci.type}"
  closeMainGoal `checkedCase (mkConst n (ci.levelParams.map Level.param))
private abbrev value : (F r n g W a v u rem quota j i : Nat) → Bool := by
  run_tac checkedCase "cellValue" "definition"
run_cmd do
  let e←getEnv
  for (leaf,aliasName) in [("cellValue",`rawValue),("D",`rawD)] do
    let n:=Name.str (Name.str (Name.num `_private.SerializedBodyCompletion.Case 0) "SerializedBodyCompletion") leaf
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact Case definition"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `SerializedBodyCompletion.Case do throwError "Wrong Case definition owner"
    logInfo m!"image-definition-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit aliasName n::st.openDecls}
private theorem dmono : ∀ F r n a b,a ≤ b → b ≤ 12 →
    SerializedBody.delimiter F r n a ≤ SerializedBody.delimiter F r n b := by
  run_tac checkedCase "d_mono" "theorem"
private theorem ivalue : ∀ T F r n g W a v u rem quota j i,j < 12 →
    SerializedBody.delimiter F r n j < i → i < SerializedBody.delimiter F r n (j+1) →
    SerializedBody.image T F r n g W a v u rem quota i=some (value F r n g W a v u rem quota j i) := by
  run_tac checkedCase "image_value" "theorem"
private theorem iblank : ∀ T F r n g W a v u rem quota j,j ≤ 12 →
    SerializedBody.image T F r n g W a v u rem quota (SerializedBody.delimiter F r n j)=none := by
  run_tac checkedCase "image_blank" "theorem"
private theorem ioutside : ∀ T F r n g W a v u rem quota i,
    i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i →
    SerializedBody.image T F r n g W a v u rem quota i=T i := by
  run_tac checkedCase "image_outside" "theorem"
private theorem locate : ∀ (d : Nat → Nat) (m i : Nat),d 0 < i → i < d m →
    (∀ k,k ≤ m → i≠d k) → ∃ j,j < m ∧ d j < i ∧ i < d (j+1) := by
  run_tac checkedCase "locate" "theorem"
private def checkedImage (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.ResetImage 0) "PhysicalCallerClosure") leaf
  let some ci:=e.find? n | throwError "Missing exact caller image interface {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | _=>"other"
  unless actual==kind do throwError "Wrong caller image term kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.ResetImage do throwError "Wrong image owner"
  logInfo m!"caller-frame-adapter|{n}|{ci.type}"
  closeMainGoal `checkedImage (mkConst n (ci.levelParams.map Level.param))
private abbrev extD : Nat → Nat → Nat → Nat → Nat := by run_tac checkedImage "extD" "definition"
private abbrev resetView : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by
  run_tac checkedImage "resetView" "definition"
private theorem reset_image : ∀ (T : Nat → Option Bool) (F r n g W a nodes used rem quota : Nat),
    resetView (SerializedBody.image T F r n g W a nodes used rem quota) (extD F r n) g W=
      SerializedBody.image T F r n g W a 0 0 W g := by
  run_tac checkedImage "reset_image" "theorem"
private theorem drise : ∀ F r n j,j < 12 → SerializedBody.delimiter F r n j < SerializedBody.delimiter F r n (j+1) := by
  run_tac checkedCase "d_rise" "theorem"
private theorem ext_eq (F r n j : Nat) (hj:j ≤ 12) : extD F r n j=SerializedBody.delimiter F r n j := by
  change (if j ≤ 12 then _ else _)=_
  rw [if_pos hj]
private theorem ext_last (F r n : Nat) : extD F r n 13=SerializedBody.delimiter F r n 12+6 := rfl
private theorem ext_rise (F r n j : Nat) (hj:j < 13) : extD F r n j < extD F r n (j+1) := by
  by_cases before:j < 12
  · rw [ext_eq F r n j (by omega),ext_eq F r n (j+1) (by omega)];exact drise F r n j before
  · have eq:j=12:=by omega
    subst j
    rw [ext_eq F r n 12 (by decide),ext_last]
    omega
private theorem ext_mono (F r n a b : Nat) (ab:a ≤ b) (hb:b ≤ 13) : extD F r n a ≤ extD F r n b := by
  by_cases before:b ≤ 12
  · rw [ext_eq F r n a (by omega),ext_eq F r n b before];exact dmono F r n a b ab before
  · have eq:b=13:=by omega
    subst b
    rw [ext_last]
    by_cases small:a ≤ 12
    · rw [ext_eq F r n a small];have h:=dmono F r n a 12 small le_rfl;omega
    · have eq:a=13:=by omega
      subst a;rw [ext_last]
private theorem image_grid (T : Nat → Option Bool) (F r n g W anchor nodes used rem quota : Nat)
    (endBlank:T (SerializedBody.delimiter F r n 12+6)=none)
    (metadata:∀ i,SerializedBody.delimiter F r n 12 < i → i < SerializedBody.delimiter F r n 12+6 → ∃ b,T i=some b) :
    (∀ j,j < 13 → extD F r n j < extD F r n (j+1)) ∧
    (∀ a b,a ≤ b → b ≤ 13 → extD F r n a ≤ extD F r n b) ∧
    (∀ j,j ≤ 13 → SerializedBody.image T F r n g W anchor nodes used rem quota (extD F r n j)=none) ∧
    (∀ j i,j < 13 → extD F r n j < i → i < extD F r n (j+1) →
      ∃ b,SerializedBody.image T F r n g W anchor nodes used rem quota i=some b) := by
  refine ⟨ext_rise F r n,ext_mono F r n,?_,?_⟩
  · intro j hj
    by_cases before:j ≤ 12
    · rw [ext_eq F r n j before];exact iblank T F r n g W anchor nodes used rem quota j before
    · have eq:j=13:=by omega
      subst j
      rw [ext_last,ioutside T F r n g W anchor nodes used rem quota _ (Or.inr (by omega))]
      exact endBlank
  · intro j i hj lo hi
    by_cases before:j < 12
    · rw [ext_eq F r n j (by omega)] at lo
      rw [ext_eq F r n (j+1) (by omega)] at hi
      exact ⟨_,ivalue T F r n g W anchor nodes used rem quota j i before lo hi⟩
    · have eq:j=12:=by omega
      subst j
      rw [ext_eq F r n 12 (by decide)] at lo
      rw [ext_last] at hi
      rw [ioutside T F r n g W anchor nodes used rem quota i (Or.inr lo)]
      exact metadata i lo hi
private theorem copy_width (F r n j : Nat) (hj:j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6) :
    extD F r n (j+1)=extD F r n j+r+1 := by
  rw [ext_eq F r n (j+1) (by omega),ext_eq F r n j (by omega)]
  rcases hj with rfl|rfl|rfl|rfl|rfl <;> dsimp only [SerializedBody.delimiter] <;> omega
private theorem reset_prepared (k : Nat) (a : Fin 3) (N B S z n r g W M Q F : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool) (T : Nat → Option Bool) (nodes used rem quota : Nat)
    (hg:g ≤ r) (hw:W ≤ r) (positive:0 < Q) (arena:S+z+n+3+Q < F)
    (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false) (left:T (S+z+2)=none)
    (betaCells:∀ j:Fin n,T (S+z+n+2-j.val)=some (beta j)) (right:T (S+z+n+3)=none)
    (marks:∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap:∀ i,S+z+n+3+Q < i → i < F → T i=none) (fence:T F=some false)
    (endBlank:T (SerializedBody.delimiter F r n 12+6)=none)
    (metadata:∀ i,SerializedBody.delimiter F r n 12 < i → i < SerializedBody.delimiter F r n 12+6 → ∃ b,T i=some b)
    (tag:a.val=2 ↔ S ≤ M) (anchor:M < S → 0 < M ∧ T (M-1)=none)
    (fit:SerializedBody.delimiter F r n 12+6 < tapeLength N B) (hH:S+z+n+3 < tapeLength N B) :
    let U:=SerializedBody.image T F r n g W (S-min M S) nodes used rem quota
    let initial : Config (callerMachine k).stateCount N B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,fun i=>U i.val⟩
    ∃ t,t ≤ 1024*(r+1)*(SerializedBody.delimiter F r n 12+7) ∧
      (callerMachine k).run t initial=⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared T S M F r n g W i.val⟩ ∧
      (∀ u,u < t → (BodyIngress.machine k).stateCount+7500 ≤ ((callerMachine k).run u initial).state.val) := by
  let U:=SerializedBody.image T F r n g W (S-min M S) nodes used rem quota
  let D:=extD F r n
  let H:=S+z+n+3
  let L:=S+z+2
  let P:=SerializedBody.delimiter F r n 12+6
  have below:∀ i,i < F+1 → U i=T i:=by
    intro i hi;exact ioutside T F r n g W (S-min M S) nodes used rem quota i (Or.inl hi)
  obtain ⟨rise,mono,blank,cells⟩:=image_grid T F r n g W (S-min M S) nodes used rem quota endBlank metadata
  have gfield:∀ i,D 0 < i → i < D 1 → U i=some (decide (i-D 0 ≤ g)):=by
    intro i lo hi
    change SerializedBody.delimiter F r n 0 < i at lo
    change i < SerializedBody.delimiter F r n 1 at hi
    exact ivalue T F r n g W (S-min M S) nodes used rem quota 0 i (by decide) lo hi
  have wfield:∀ i,D 3 < i → i < D 4 → U i=some (decide (i-D 3 ≤ W)):=by
    intro i lo hi
    change SerializedBody.delimiter F r n 3 < i at lo
    change i < SerializedBody.delimiter F r n 4 at hi
    exact ivalue T F r n g W (S-min M S) nodes used rem quota 3 i (by decide) lo hi
  have bc:∀ i,L < i → i < H → ∃ b,U i=some b:=by
    intro i lo hi
    let j:=H-1-i
    have hj:j < n:=by dsimp only [H,L,j] at *;omega
    have cell:=betaCells ⟨j,hj⟩
    have pos:S+z+n+2-j=i:=by dsimp only [j,H] at *;omega
    rw [pos] at cell
    rw [below i (by dsimp only [H] at hi;omega)]
    exact ⟨_,cell⟩
  obtain ⟨t,price,execution,_foot,_safe,range⟩:=reset_body_entry k a N B S L H M Q F P r g W D U source
    rise mono blank cells rfl (le_of_eq (ext_last F r n)) fit (copy_width F r n) gfield wfield hg hw positive arena
    (by rw [below H (by dsimp only [H];omega)];exact right)
    (by rw [below F (by omega)];exact fence)
    (by intro i lo hi;rw [below i (by dsimp only [H] at hi;omega)];exact marks i lo hi)
    (by intro i lo hi;rw [below i (by omega)];exact gap i lo hi)
    (by dsimp only [L];omega) (by dsimp only [L,H];omega)
    (by rw [below S (by omega)];exact eof)
    (by rw [below L (by dsimp only [L];omega)];exact left)
    (by intro i lo hi;rw [below i (by dsimp only [L] at hi;omega)];exact ⟨false,reg i lo hi⟩) bc
    (by intro i lo hi;rw [below i (by omega)];exact src i lo hi) tag
    (by intro physical;obtain ⟨pos,hole⟩:=anchor physical;exact ⟨pos,by rw [below (M-1) (by omega)];exact hole⟩) hH
  have tape:(fun h:Fin (tapeLength N B)=>if h.val=M ∧ h.val < S then none
      else if D 6 < h.val ∧ h.val < D 7 then some (decide (h.val-D 6 ≤ g))
      else if D 4 < h.val ∧ h.val < D 5 then some (decide (h.val-D 4 ≤ W))
      else if D 11 < h.val ∧ h.val < D 12 then some false
      else if D 5 < h.val ∧ h.val < D 6 then some false else U h.val)=
      (fun h=>SerializedBody.prepared T S M F r n g W h.val):=by
    funext h
    change (if h.val=M ∧ h.val < S then none else resetView U D g W h.val)=_
    rw [congrFun (reset_image T F r n g W (S-min M S) nodes used rem quota) h.val]
    rfl
  rw [tape] at execution
  refine ⟨t,?_,execution,range⟩
  simpa only [P,show SerializedBody.delimiter F r n 12+6+1=SerializedBody.delimiter F r n 12+7 by omega] using price
end PhysicalCallerClosure
