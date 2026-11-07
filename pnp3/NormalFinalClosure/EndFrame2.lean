import NormalFinalClosure.FrameFacts2
import NormalFinalClosure.RowsDone
import RawCallerClosure.Frame
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
private def caseTerm (leaf kind : String) : TacticM Unit := do
  let owner:=`SerializedBodyCompletion.Case
  let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "SerializedBodyCompletion") leaf
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact original image term"
  let actual:=match ci with|.thmInfo _=>"theorem"|.defnInfo _=>"definition"|_=>"other"
  unless actual==kind do throwError "Wrong original image term kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing image owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong image owner"
  logInfo m!"actual-caller-frame-image|{n}|{kind}|{ci.type}"
  closeMainGoal `caseTerm (mkConst n (ci.levelParams.map Level.param))
private abbrev cellValue : (F r n g W a nodes used rem quota j i : Nat) → Bool := by
  run_tac caseTerm "cellValue" "definition"
private theorem imageOutside : ∀ T F r n g W a nodes used rem quota i,
    i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i →
    SerializedBody.image T F r n g W a nodes used rem quota i=T i := by
  run_tac caseTerm "image_outside" "theorem"
private theorem imageBlank : ∀ T F r n g W a nodes used rem quota j,j ≤ 12 →
    SerializedBody.image T F r n g W a nodes used rem quota (SerializedBody.delimiter F r n j)=none := by
  run_tac caseTerm "image_blank" "theorem"
private theorem imageCell : ∀ T F r n g W a nodes used rem quota j i,j < 12 →
    SerializedBody.delimiter F r n j < i → i < SerializedBody.delimiter F r n (j+1) →
    SerializedBody.image T F r n g W a nodes used rem quota i=some (cellValue F r n g W a nodes used rem quota j i) := by
  run_tac caseTerm "image_value" "theorem"
private theorem low_caller (T : Nat → Option Bool) (S z n F r g W M marks nodes used rem quota : Nat)
    (beta : Fin n → Bool) (i : Nat) (hi:i ≤ F) :
    PhysicalCallerClosure.callerImage T S z n F r g W M marks beta nodes used rem quota i=
      if h:S+z+2 < i ∧ i < S+z+2+n+1 then
        some (beta ⟨S+z+2+n+1-1-i,by omega⟩)
      else if S+z+2+n+1 < i ∧ i < F then
        if i ≤ S+z+2+n+1+marks then some true else none
      else T i := by
  have endAfter:F < SerializedBody.delimiter F r n 12 := by
    change F < F+13*r+2*n+16
    omega
  dsimp only [PhysicalCallerClosure.callerImage]
  split
  · rfl
  · split
    · rfl
    · rw [if_neg (by omega),imageOutside T F r n g W (S-min M S) nodes used rem quota i (Or.inl (show i < F+1 by omega))]
private theorem high_caller (T : Nat → Option Bool) (S z n F r g W M marks nodes used rem quota : Nat)
    (beta : Fin n → Bool) (i : Nat) (room:S+z+2+n+1 < F) (hi:F < i) :
    PhysicalCallerClosure.callerImage T S z n F r g W M marks beta nodes used rem quota i=
      if SerializedBody.delimiter F r n 12 < i ∧ i < SerializedBody.delimiter F r n 12+6 then some false
      else SerializedBody.image T F r n g W (S-min M S) nodes used rem quota i := by
  dsimp only [PhysicalCallerClosure.callerImage]
  rw [dif_neg (by omega),if_neg (by omega)]
private theorem caller_blanks (T : Nat → Option Bool) (S z n F r g W M marks nodes used rem quota : Nat)
    (beta : Fin n → Bool) (room:S+z+2+n+1 < F) (j : Nat) (hj:j ≤ 12) :
    PhysicalCallerClosure.callerImage T S z n F r g W M marks beta nodes used rem quota (SerializedBody.delimiter F r n j)=none := by
  have lower:F < SerializedBody.delimiter F r n j := by
    interval_cases j <;> simp only [SerializedBody.delimiter] <;> omega
  have upper:SerializedBody.delimiter F r n j ≤ SerializedBody.delimiter F r n 12 := by
    interval_cases j <;> simp only [SerializedBody.delimiter] <;> omega
  rw [high_caller T S z n F r g W M marks nodes used rem quota beta _ room lower,if_neg (by omega)]
  exact imageBlank T F r n g W (S-min M S) nodes used rem quota j hj
private theorem caller_cell (T : Nat → Option Bool) (S z n F r g W M marks nodes used rem quota : Nat)
    (beta : Fin n → Bool) (room:S+z+2+n+1 < F) (j i : Nat) (hj:j < 12)
    (lo:SerializedBody.delimiter F r n j < i) (hi:i < SerializedBody.delimiter F r n (j+1)) :
    PhysicalCallerClosure.callerImage T S z n F r g W M marks beta nodes used rem quota i=
      some (cellValue F r n g W (S-min M S) nodes used rem quota j i) := by
  have lower:F < i := by
    have h:F < SerializedBody.delimiter F r n j := by
      interval_cases j <;> simp only [SerializedBody.delimiter] <;> omega
    omega
  have upper:i < SerializedBody.delimiter F r n 12 := by
    have h:SerializedBody.delimiter F r n (j+1) ≤ SerializedBody.delimiter F r n 12 := by
      interval_cases j <;> norm_num only [SerializedBody.delimiter] <;> omega
    omega
  rw [high_caller T S z n F r g W M marks nodes used rem quota beta i room lower,if_neg (by omega)]
  exact imageCell T F r n g W (S-min M S) nodes used rem quota j i hj lo hi
end NormalFinalClosure
