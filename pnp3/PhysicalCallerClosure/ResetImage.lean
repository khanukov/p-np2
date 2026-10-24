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
private def extD (F r n j : Nat) : Nat :=
  if j ≤ 12 then SerializedBody.delimiter F r n j else SerializedBody.delimiter F r n 12+6
private theorem gate {D : Nat → Nat} (mono:∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    {j i} (hj:j < 12) (lo:D j < i) (hi:i < D (j+1)) (k : Nat) (hk:k < 12) :
    (D k < i ∧ i < D (k+1)) ↔ j=k := by
  constructor
  · intro inside
    by_contra ne
    by_cases order:j < k
    · have h:=mono (j+1) k (by omega) (by omega);omega
    · have h:=mono (k+1) j (by omega) (by omega);omega
  · intro eq;subst k;exact ⟨lo,hi⟩
private def resetView (T : Nat → Option Bool) (D : Nat → Nat) (g W : Nat) : Nat → Option Bool := fun i=>
  if D 6 < i ∧ i < D 7 then some (decide (i-D 6 ≤ g))
  else if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W))
  else if D 11 < i ∧ i < D 12 then some false
  else if D 5 < i ∧ i < D 6 then some false else T i
private theorem reset_image (T : Nat → Option Bool) (F r n g W a nodes used rem quota : Nat) :
    resetView (SerializedBody.image T F r n g W a nodes used rem quota) (extD F r n) g W=
      SerializedBody.image T F r n g W a 0 0 W g := by
  let D:=SerializedBody.delimiter F r n
  have mono:∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b:=dmono F r n
  funext i
  change (if D 6 < i ∧ i < D 7 then some (decide (i-D 6 ≤ g))
    else if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W))
    else if D 11 < i ∧ i < D 12 then some false
    else if D 5 < i ∧ i < D 6 then some false
    else SerializedBody.image T F r n g W a nodes used rem quota i)=_
  by_cases out:i < D 0 ∨ D 12 < i
  · have no (k : Nat) (hk:k < 12) : ¬(D k < i ∧ i < D (k+1)):=by
      have l:=mono 0 k (by omega) (by omega)
      have u:=mono (k+1) 12 (by omega) le_rfl
      omega
    rw [if_neg (no 6 (by decide)),if_neg (no 4 (by decide)),if_neg (no 11 (by decide)),if_neg (no 5 (by decide)),
      ioutside T F r n g W a nodes used rem quota i out,ioutside T F r n g W a 0 0 W g i out]
  · by_cases sep:∃ j,j ≤ 12 ∧ i=D j
    · obtain ⟨j,hj,rfl⟩:=sep
      have no (k : Nat) (hk:k < 12) : ¬(D k < D j ∧ D j < D (k+1)):=by
        by_cases order:j ≤ k
        · have h:=mono j k order (by omega);omega
        · have h:=mono (k+1) j (by omega) hj;omega
      rw [if_neg (no 6 (by decide)),if_neg (no 4 (by decide)),if_neg (no 11 (by decide)),if_neg (no 5 (by decide)),
        iblank T F r n g W a nodes used rem quota j hj,iblank T F r n g W a 0 0 W g j hj]
    · have no:∀ k,k ≤ 12 → i≠D k:=by intro k hk eq;exact sep ⟨k,hk,eq⟩
      have lo:D 0 < i:=by have h:=no 0 (by decide);omega
      have hi:i < D 12:=by have h:=no 12 (by decide);omega
      obtain ⟨j,hj,lo,hi⟩:=locate D 12 i lo hi no
      simp only [gate mono hj lo hi 6 (by decide),gate mono hj lo hi 4 (by decide),
        gate mono hj lo hi 11 (by decide),gate mono hj lo hi 5 (by decide)]
      rw [ivalue T F r n g W a nodes used rem quota j i hj lo hi,ivalue T F r n g W a 0 0 W g j i hj lo hi]
      interval_cases j <;> simp [rawValue]
      all_goals dsimp only [D,rawD] at *
      all_goals first | rfl | omega
end PhysicalCallerClosure
