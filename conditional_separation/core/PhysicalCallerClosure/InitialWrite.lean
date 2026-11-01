import PhysicalCallerClosure.CallerMemory
import PhysicalCallerClosure.SourceInitialize
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","NativeSafe","put"]),
      (`PhysicalCallerClosure.WriteMeta,["FrontGrid","write_metadata"]),
      (`PhysicalCallerClosure.CallerMemory,["update","image_update","written_image"]),
      (`PhysicalCallerClosure.ResetFrame,["extD","ext_rise","ext_mono","ext_eq","iblank","ivalue"]),
      (`PhysicalCallerClosure.SourceInitialize,["sourceHoles"]),
      (`PhysicalCallerClosure.WriteBits,["written"]),(`PhysicalCallerClosure.Compare,["flags"]),
      (`PhysicalCallerClosure.WriteReset,["writerEntry","writer_code"])] do
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
private abbrev frontMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 12 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) →
    (∀ j,j ≤ 12 → T (D j)=none) → (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) → FrontGrid D T := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.mk" "constructor"
private theorem front_image (T : Nat → Option Bool) (F r n g W anchor nodes used rem quota : Nat) :
    FrontGrid (extD F r n) (SerializedBody.image T F r n g W anchor nodes used rem quota) := by
  refine frontMk (by intro j hj;exact ext_rise F r n j (by omega))
    (by intro a b ab hb;exact ext_mono F r n a b ab (by omega)) ?_ ?_
  · intro j hj
    rw [ext_eq F r n j hj]
    exact iblank T F r n g W anchor nodes used rem quota j hj
  · intro j i hj lo hi
    rw [ext_eq F r n j (by omega)] at lo
    rw [ext_eq F r n (j+1) (by omega)] at hi
    exact ⟨_,ivalue T F r n g W anchor nodes used rem quota j i hj lo hi⟩
private theorem holes_image (T : Nat → Option Bool) (S z n F r g W M A : Nat)
    (arena:S+z+n+3 < F) (aS:A ≤ S) :
    sourceHoles (SerializedBody.image T F r n g W (S-min M S) 0 0 W g) S M A=
      SerializedBody.image (sourceHoles T S M A) F r n g W (S-min M S) 0 0 W g := by
  unfold sourceHoles
  by_cases hm:M < S
  · simp only [if_pos hm]
    change update (update (SerializedBody.image T F r n g W (S-min M S) 0 0 W g) (M-1) none) A none=_
    rw [image_update _ F r n g W (S-min M S) 0 0 W g (M-1) none (Or.inl (by change M-1 < F+1;omega)),
      image_update _ F r n g W (S-min M S) 0 0 W g A none (Or.inl (by change A < F+1;omega))]
    rfl
  · simp only [if_neg hm]
    exact image_update _ F r n g W (S-min M S) 0 0 W g A none (Or.inl (by change A < F+1;omega))
end PhysicalCallerClosure
