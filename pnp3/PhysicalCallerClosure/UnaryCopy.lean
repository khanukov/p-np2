import PhysicalCallerClosure.Engine
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def support (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing Engine term {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong Engine kind: {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
  logInfo m!"copy-support|{actual}|{n}|{ci.type}"
  closeMainGoal `support (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["Node","Path","Grid","Unary","DecRows","IncRows","put","keep","dec_zero","dec_positive","inc_success"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
    logInfo m!"copy-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac support "Node.mk" "constructor"
private abbrev gridMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 13 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b) →
    (∀ j,j ≤ 13 → T (D j)=none) →
    (∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b) → Grid D T := by
  run_tac support "Grid.mk" "constructor"
private theorem mono : ∀ {D T},Grid D T → ∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b := by
  run_tac support "Grid.mono" "theorem"
private theorem rise : ∀ {D T},Grid D T → ∀ j,j < 13 → D j < D (j+1) := by
  run_tac support "Grid.rise" "theorem"
private theorem blanks : ∀ {D T},Grid D T → ∀ j,j ≤ 13 → T (D j)=none := by
  run_tac support "Grid.blank" "theorem"
private theorem occupied : ∀ {D T},Grid D T → ∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b := by
  run_tac support "Grid.cells" "theorem"
private def field (T : Nat → Option Bool) (D : Nat → Nat) (j v : Nat) : Nat → Option Bool :=
  fun i=>if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else T i
private theorem field_self {T D j v} (u : Unary D T j v) : field T D j v=T := by
  funext i; by_cases h:D j < i ∧ i < D (j+1)
  · simp only [field,if_pos h]; exact (u i h.1 h.2).symm
  · simp only [field,if_neg h]
private theorem field_repeat (T D j v w) : field (field T D j v) D j w=field T D j w := by
  funext i; simp only [field]; split <;> rfl
private theorem field_unary (T D j v) : Unary D (field T D j v) j v := by
  intro i lo hi; simp only [field,if_pos (show D j < i ∧ i < D (j+1) from ⟨lo,hi⟩)]
private theorem disjoint {D T} (grid:Grid D T) {j k i} (hj:j < 13) (hk:k < 13) (ne:j≠k)
    (lo:D j < i) (hi:i < D (j+1)) : ¬(D k < i ∧ i < D (k+1)) := by
  by_cases order:j < k
  · have h:=mono grid (j+1) k (by omega) (by omega); omega
  · have h:=mono grid (k+1) j (by omega) (by omega); omega
private theorem field_other {D T j k v w} (grid:Grid D T) (hj:j < 13) (hk:k < 13) (ne:j≠k)
    (u:Unary D T k w) : Unary D (field T D j v) k w := by
  intro i lo hi
  rw [field,if_neg (disjoint grid hk hj ne.symm lo hi)]
  exact u i lo hi
private theorem field_grid {D T} (grid:Grid D T) (j v : Nat) (hj:j < 13) : Grid D (field T D j v) := by
  refine gridMk (rise grid) (mono grid) ?_ ?_
  · intro k hk
    have no:¬(D j < D k ∧ D k < D (j+1)) := by
      by_cases order:k ≤ j
      · have h:=mono grid k j order (by omega); omega
      · have h:=mono grid (j+1) k (by omega) hk; omega
    simp only [field,if_neg no]; exact blanks grid k hk
  · intro k i hk lo hi
    by_cases h:D j < i ∧ i < D (j+1)
    · exact ⟨decide (i-D j ≤ v),by simp only [field,if_pos h]⟩
    · simp only [field,if_neg h]; exact occupied grid k i hk lo hi
private theorem field_comm {T D j k v w} (grid:Grid D T) (hj:j < 13) (hk:k < 13) (ne:j≠k) :
    field (field T D j v) D k w=field (field T D k w) D j v := by
  funext i
  by_cases h:D j < i ∧ i < D (j+1)
  · have no:=disjoint grid hj hk ne h.1 h.2
    simp only [field,if_pos h,if_neg no]
  · simp only [field,if_neg h]
private theorem field_dec {D T j w v} (_grid:Grid D T) (_hj:j < 13)
    (len:D (j+1)=D j+w+1) (u:Unary D T j v) (pos:0 < v) (small:v ≤ w) :
    put T (D j+v) (some false)=field T D j (v-1) := by
  funext i
  by_cases eq:i=D j+v
  · subst i
    have inside:D j < D j+v ∧ D j+v < D (j+1) := by omega
    simp only [put,field,if_pos inside,ite_true,Nat.add_sub_cancel_left]
    have h:¬v ≤ v-1:=by omega
    simp only [decide_eq_false h]
  · by_cases inside:D j < i ∧ i < D (j+1)
    · simp only [put,if_neg eq,field,if_pos inside]
      rw [u i inside.1 inside.2]
      have ar:(i-D j ≤ v) ↔ (i-D j ≤ v-1) := by omega
      simp only [ar]
    · simp only [put,if_neg eq,field,if_neg inside]
private theorem field_inc {D T j w v} (_grid:Grid D T) (_hj:j < 13)
    (len:D (j+1)=D j+w+1) (u:Unary D T j v) (small:v < w) :
    put T (D j+v+1) (some true)=field T D j (v+1) := by
  funext i
  by_cases eq:i=D j+v+1
  · subst i
    have inside:D j < D j+v+1 ∧ D j+v+1 < D (j+1) := by omega
    simp only [put,field,if_pos inside,ite_true]
    have h:D j+v+1-D j ≤ v+1:=by omega
    simp only [decide_eq_true h]
  · by_cases inside:D j < i ∧ i < D (j+1)
    · simp only [put,if_neg eq,field,if_pos inside]
      rw [u i inside.1 inside.2]
      have ar:(i-D j ≤ v) ↔ (i-D j ≤ v+1) := by omega
      simp only [ar]
    · simp only [put,if_neg eq,field,if_neg inside]
end PhysicalCallerClosure
