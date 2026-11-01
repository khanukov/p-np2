import PhysicalCallerClosure.WriteBits
import PhysicalCallerClosure.CallerTarget
import PhysicalCallerClosure.ResetReadySurface
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
run_cmd do
  let e←getEnv
  for leaf in ["written","written_outside","written_value"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.WriteBits 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact memory writer interface {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.WriteBits do throwError "Wrong memory writer owner"
    logInfo m!"caller-memory-writer|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def frameBase (T : Nat → Option Bool) (S z n F r marks : Nat) (beta : Fin n → Bool) : Nat → Option Bool:=fun i=>
  let L:=S+z+2
  let H:=L+n+1
  if h:L < i ∧ i < H then some (beta ⟨H-1-i,by dsimp only [H] at h;omega⟩)
  else if H < i ∧ i < F then if i ≤ H+marks then some true else none
  else if SerializedBody.delimiter F r n 12 < i ∧ i < SerializedBody.delimiter F r n 12+6 then some false
  else T i
private theorem image_inside (T U : Nat → Option Bool) (F r n g W a nodes used rem quota i : Nat)
    (inside:¬(i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i)) :
    SerializedBody.image T F r n g W a nodes used rem quota i=
      SerializedBody.image U F r n g W a nodes used rem quota i := by
  unfold SerializedBody.image
  simp only [if_neg inside]
private theorem caller_image (T : Nat → Option Bool) (S z n F r g W M marks nodes used rem quota : Nat)
    (beta : Fin n → Bool) (arena:S+z+n+3 < F) :
    callerImage T S z n F r g W M marks beta nodes used rem quota=
      SerializedBody.image (frameBase T S z n F r marks beta) F r n g W (S-min M S) nodes used rem quota := by
  funext i
  let L:=S+z+2
  let H:=L+n+1
  have d0:SerializedBody.delimiter F r n 0=F+1:=rfl
  by_cases out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i
  · rw [ioutside _ F r n g W (S-min M S) nodes used rem quota i out]
    change (if h:L < i ∧ i < H then some (beta ⟨H-1-i,by dsimp only [H] at h;omega⟩)
      else if H < i ∧ i < F then if i ≤ H+marks then some true else none
      else if SerializedBody.delimiter F r n 12 < i ∧ i < SerializedBody.delimiter F r n 12+6 then some false
      else SerializedBody.image T F r n g W (S-min M S) nodes used rem quota i)=_
    rw [ioutside _ F r n g W (S-min M S) nodes used rem quota i out]
    rfl
  · have low:SerializedBody.delimiter F r n 0 ≤ i:=by omega
    have hi:i ≤ SerializedBody.delimiter F r n 12:=by omega
    have nh:¬(L < i ∧ i < H):=by dsimp only [L,H] at *;omega
    have nm:¬(H < i ∧ i < F):=by rw [d0] at low;omega
    have nd:¬(SerializedBody.delimiter F r n 12 < i ∧ i < SerializedBody.delimiter F r n 12+6):=by omega
    change (if h:L < i ∧ i < H then some (beta ⟨H-1-i,by dsimp only [H] at h;omega⟩)
      else if H < i ∧ i < F then if i ≤ H+marks then some true else none
      else if SerializedBody.delimiter F r n 12 < i ∧ i < SerializedBody.delimiter F r n 12+6 then some false
      else SerializedBody.image T F r n g W (S-min M S) nodes used rem quota i)=_
    rw [dif_neg nh,if_neg nm,if_neg nd]
    exact image_inside _ _ F r n g W (S-min M S) nodes used rem quota i out
private def update (T : Nat → Option Bool) (h : Nat) (v : Option Bool) : Nat → Option Bool:=fun i=>if i=h then v else T i
private theorem image_update (T : Nat → Option Bool) (F r n g W a nodes used rem quota h : Nat) (v : Option Bool)
    (outside:h < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < h) :
    update (SerializedBody.image T F r n g W a nodes used rem quota) h v=
      SerializedBody.image (update T h v) F r n g W a nodes used rem quota := by
  funext i
  by_cases eq:i=h
  · subst i
    rw [ioutside _ F r n g W a nodes used rem quota h outside]
    simp [update]
  · by_cases out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i
    · rw [ioutside _ F r n g W a nodes used rem quota i out]
      simp only [update,if_neg eq,ioutside T F r n g W a nodes used rem quota i out]
    · rw [show update (SerializedBody.image T F r n g W a nodes used rem quota) h v i=
          SerializedBody.image T F r n g W a nodes used rem quota i by simp only [update,if_neg eq]]
      exact image_inside _ _ F r n g W a nodes used rem quota i out
private theorem written_image (T : Nat → Option Bool) (F r n g W a nodes used rem quota : Nat) (bits : Fin 5 → Bool) :
    written (SerializedBody.image T F r n g W a nodes used rem quota) (SerializedBody.delimiter F r n 12) bits 5=
      SerializedBody.image (written T (SerializedBody.delimiter F r n 12) bits 5) F r n g W a nodes used rem quota := by
  funext i
  let d:=SerializedBody.delimiter F r n 12
  by_cases w:d < i ∧ i < d+6
  · have out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i:=Or.inr w.1
    rw [ioutside _ F r n g W a nodes used rem quota i out]
    let j:=i-d-1
    have hj:j < 5:=by dsimp only [j];omega
    have pos:d+1+j=i:=by dsimp only [j];omega
    have left:=written_value (SerializedBody.image T F r n g W a nodes used rem quota) d bits ⟨j,hj⟩
    have right:=written_value T d bits ⟨j,hj⟩
    rw [pos] at left right
    exact left.trans right.symm
  · have nw:i ≤ d ∨ d+6 ≤ i:=by omega
    rw [written_outside nw]
    by_cases out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i
    · rw [ioutside T F r n g W a nodes used rem quota i out,ioutside _ F r n g W a nodes used rem quota i out,
        written_outside nw]
    · exact image_inside _ _ F r n g W a nodes used rem quota i out
end PhysicalCallerClosure
