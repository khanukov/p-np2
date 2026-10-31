import FullBodyClosure.Representation
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Lean Elab Tactic in
private def checkedCase (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num `_private.SerializedBodyCompletion.Case 0) "SerializedBodyCompletion")
  let some ci:=env.find? name | throwError "Missing exact immutable declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing owner for {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside imported header"
  unless env.header.moduleNames[mi]! == `SerializedBodyCompletion.Case do throwError "Wrong owner for {name}"
  logInfo m!"frame-adapter|{name}|{ci.type}"
  closeMainGoal `checkedCase (mkConst name (ci.levelParams.map Level.param))
private abbrev D : Nat → Nat → Nat → Nat → Nat := SerializedBody.delimiter
private abbrev value : (F r n g W a v u rem quota j i : Nat) → Bool := by run_tac checkedCase "cellValue"
private theorem rise : ∀ F r n j,j < 12 → D F r n j < D F r n (j+1) := by run_tac checkedCase "d_rise"
private theorem mono : ∀ F r n a b,a ≤ b → b ≤ 12 → D F r n a ≤ D F r n b := by run_tac checkedCase "d_mono"
private theorem image_blank : ∀ T F r n g W a v u rem quota j,j ≤ 12 →
  SerializedBody.image T F r n g W a v u rem quota (D F r n j)=none := by run_tac checkedCase "image_blank"
private theorem image_value : ∀ T F r n g W a v u rem quota j i,j < 12 → D F r n j < i → i < D F r n (j+1) →
  SerializedBody.image T F r n g W a v u rem quota i=some (value F r n g W a v u rem quota j i) := by run_tac checkedCase "image_value"
private theorem image_outside : ∀ T F r n g W a v u rem quota i,i < D F r n 0 ∨ D F r n 12 < i →
  SerializedBody.image T F r n g W a v u rem quota i=T i := by run_tac checkedCase "image_outside"
private theorem locate : ∀ (d : Nat → Nat) (m i : Nat),d 0 < i → i < d m → (∀ k,k ≤ m → i≠d k) →
  ∃ j,j < m ∧ d j < i ∧ i < d (j+1) := by run_tac checkedCase "locate"
/-- Full pointwise image reconstruction, including both exterior regions and every delimiter. -/
private theorem image_ext (base T : Nat → Option Bool) (F r n g W a v u rem quota : Nat)
    (outside : ∀ i,i < D F r n 0 ∨ D F r n 12 < i → T i=base i)
    (blank : ∀ j,j ≤ 12 → T (D F r n j)=none)
    (fields : ∀ j i,j < 12 → D F r n j < i → i < D F r n (j+1) →
      T i=some (value F r n g W a v u rem quota j i)) :
    T=SerializedBody.image base F r n g W a v u rem quota := by
  funext i
  by_cases out : i < D F r n 0 ∨ D F r n 12 < i
  · rw [outside i out,image_outside base F r n g W a v u rem quota i out]
  · by_cases sep : ∃ j,j ≤ 12 ∧ i=D F r n j
    · obtain ⟨j,hj,rfl⟩:=sep
      rw [blank j hj,image_blank base F r n g W a v u rem quota j hj]
    · have no : ∀ j,j ≤ 12 → i≠D F r n j := by intro j hj h;exact sep ⟨j,hj,h⟩
      have lo : D F r n 0 < i := by have :=no 0 (by decide);omega
      have hi : i < D F r n 12 := by have :=no 12 (by decide);omega
      obtain ⟨j,hj,lo,hi⟩:=locate (D F r n) 12 i lo hi no
      rw [fields j i hj lo hi,image_value base F r n g W a v u rem quota j i hj lo hi]
/-- The source, register and assignment lie strictly before the workspace. -/
private theorem image_header (T : Nat → Option Bool) (S F r n g W a v u rem quota i : Nat)
    (_before : S < D F r n 0) (_lo : S ≤ i) (hi : i < D F r n 0) :
    SerializedBody.image T F r n g W a v u rem quota i=T i := by
  exact image_outside T F r n g W a v u rem quota i (Or.inl hi)
private theorem extent_bound (R S z n r Q : Nat) (hr : r ≤ S) (hs : S ≤ R) (hq : 0 < Q)
    (arena : S+z+n+3+Q < FixedRawLengthFence.fencePos R) :
    D (FixedRawLengthFence.fencePos R) r n 12+1 ≤ 22*(R+1) ∧ n+1 ≤ 3*(R+1) := by
  have bound : S+z+n+3+Q < 3*R+2:=arena
  have width : n ≤ 3*R:=by omega
  change 3*R+2+13*r+2*n+16+1 ≤ 22*(R+1) ∧ n+1 ≤ 3*(R+1)
  omega
/-- Plain-Nat absorption for a candidate complete native execution price; execution still must establish this price. -/
private theorem absorb_price (R P n r g t : Nat) (hp : P+1 ≤ 22*(R+1)) (hn : n+1 ≤ 3*(R+1))
    (hr : r ≤ R) (hg : g ≤ r) (price : t ≤ 8192*(P+1)*(n+1)*(r+1)*(g+1)) :
    t ≤ 1073741824*(R+1)^6 := by
  have a:=Nat.mul_le_mul_left 8192 hp
  have b:=Nat.mul_le_mul a hn
  have c:=Nat.mul_le_mul b (show r+1 ≤ R+1 from by omega)
  have d:=Nat.mul_le_mul c (show g+1 ≤ R+1 from by omega)
  have p4 : 8192*(22*(R+1))*(3*(R+1))*(R+1)*(R+1)=540672*(R+1)^4 := by ring
  rw [p4] at d
  have powers : (R+1)^4 ≤ (R+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith
end FullBodyClosure
