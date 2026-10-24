import NormalFinalClosure.Frame2
import NormalFinalClosure.Support
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaves) in [
    (`NormalFinalClosure.Frame2,["D","GuardFrame","repImage"]),
    (`PhysicalCallerClosure.Engine,["Grid"])] do
    for leaf in leaves do
      let ns:=if owner==`PhysicalCallerClosure.Engine then `PhysicalCallerClosure else `NormalFinalClosure
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing exact frame component {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing frame component owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong frame component owner"
      let kind:=match ci with|.defnInfo _=>"definition"|.inductInfo _=>"structure"|_=>"other"
      unless kind==(if leaf=="Grid" || leaf=="GuardFrame" then "structure" else "definition") do throwError "Wrong frame component kind"
      logInfo m!"normal-frame-component|{owner}|{kind}|{n}|{ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private def frameSelect (owner : Name) (ns : Name) (leaf kind : String) : Lean.Elab.Tactic.TacticM Unit := do
  let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact frame projection/constructor"
  let actual:=match ci with|.thmInfo _=>"theorem"|.ctorInfo _=>"constructor"|_=>"other"
  unless actual==kind do throwError "Wrong frame API kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing frame API owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong frame API owner"
  logInfo m!"normal-frame-exact-API|{n}|{kind}|{ci.type}"
  Lean.Elab.Tactic.closeMainGoal `frameSelect (mkConst n (ci.levelParams.map Level.param))
private abbrev gridMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 13 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b) →
    (∀ j,j ≤ 13 → T (D j)=none) →
    (∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b) → Grid D T := by
  run_tac frameSelect `PhysicalCallerClosure.Engine `PhysicalCallerClosure "Grid.mk" "constructor"
private theorem fHead : ∀ {S z n F r W source T},GuardFrame S z n F r W source T → S+z+2+n+1 < F := by
  run_tac frameSelect `NormalFinalClosure.Frame2 `NormalFinalClosure "GuardFrame.headBefore" "theorem"
private theorem fDelim : ∀ {S z n F r W source T},GuardFrame S z n F r W source T →
    ∀ j,j ≤ 13 → T (D F r n j)=none := by
  run_tac frameSelect `NormalFinalClosure.Frame2 `NormalFinalClosure "GuardFrame.delimiters" "theorem"
private theorem fCells : ∀ {S z n F r W source T},GuardFrame S z n F r W source T →
    ∀ j i,j < 13 → D F r n j < i → i < D F r n (j+1) → ∃ b,T i=some b := by
  run_tac frameSelect `NormalFinalClosure.Frame2 `NormalFinalClosure "GuardFrame.occupied" "theorem"
private theorem d_rise (F r n j : Nat) (hj:j < 13) : D F r n j < D F r n (j+1) := by
  interval_cases j <;> norm_num only [D,SerializedBody.delimiter,ite_true,ite_false] <;> omega
private theorem d_mono (F r n a b : Nat) (h:a ≤ b) (bound:b ≤ 13) : D F r n a ≤ D F r n b := by
  induction b with
  | zero=>
    have eq:a=0:=by omega
    subst a
    exact le_rfl
  | succ b ih=>
    by_cases eq:a=b+1
    · subst a;exact le_rfl
    · exact (ih (by omega) (by omega)).trans (d_rise F r n b (by omega)).le
private theorem frame_grid {S z n F r W source T} (frame:GuardFrame S z n F r W source T) :
    Grid (D F r n) T :=
  gridMk (d_rise F r n) (fun a b h hb=>d_mono F r n a b h hb) (fDelim frame) (fCells frame)
private theorem frame_before {S z n F r W source T} (frame:GuardFrame S z n F r W source T) :
    S < D F r n 0 := by
  change S < F+1
  have h:=fHead frame
  omega
private theorem rep_grid {S z n F r W source T} (frame:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) :
    Grid (D F r n) (repImage T F r n S cursor a b c index records) := by
  have low:=frame_before frame
  apply gridMk
  · exact d_rise F r n
  · exact fun a b h hb=>d_mono F r n a b h hb
  · intro j hj
    have above:=d_mono F r n 0 j (by omega) hj
    have blanks:=fDelim frame j hj
    have noField (v : Nat) (hv:v < 13) :
        ¬ (D F r n v < D F r n j ∧ D F r n j < D F r n (v+1)) := by
      by_cases lt:j ≤ v
      · have h:=d_mono F r n j v lt (by omega);omega
      · have h:=d_mono F r n (v+1) j (by omega) hj;omega
    simp only [repImage,show ¬(D F r n j=cursor ∧ cursor < S) by omega,if_false,
      noField 4 (by decide),noField 5 (by decide),noField 6 (by decide),noField 11 (by decide),noField 10 (by decide)]
    exact blanks
  · intro j i hj lo hi
    have above:=d_mono F r n 0 j (by omega) (by omega)
    have original:=fCells frame j i hj lo hi
    dsimp only [repImage]
    rw [if_neg (by omega : ¬(i=cursor ∧ cursor < S))]
    split
    · exact ⟨_,rfl⟩
    · split
      · exact ⟨_,rfl⟩
      · split
        · exact ⟨_,rfl⟩
        · split
          · exact ⟨_,rfl⟩
          · split
            · split <;> exact ⟨_,rfl⟩
            · exact original
private theorem clean_image (N B S F r n : Nat) (T : Nat → Option Bool) :
    (fun i:Fin (tapeLength N B)=>repImage T F r n S S 0 0 0 0 [] i.val)=
      Target.cleared (fun i:Fin (tapeLength N B)=>T i.val) F r n := by
  funext i
  have dsmall (j : Nat) (hj:j ≤ 12) : D F r n j=SerializedBody.delimiter F r n j := by
    exact if_pos hj
  simp only [repImage,Nat.lt_irrefl,and_false,if_false,List.length_nil,Nat.not_lt_zero,
    dsmall 4 (by decide),dsmall 5 (by decide),dsmall 6 (by decide),dsmall 7 (by decide),
    dsmall 10 (by decide),dsmall 11 (by decide),dsmall 12 (by decide),Target.cleared]
  by_cases h4:SerializedBody.delimiter F r n 4 < i.val ∧ i.val < SerializedBody.delimiter F r n 5
  · have no:¬i.val-SerializedBody.delimiter F r n 4 ≤ 0:=by omega
    simp only [h4,if_true,decide_eq_false no,and_self,true_or]
  · by_cases h5:SerializedBody.delimiter F r n 5 < i.val ∧ i.val < SerializedBody.delimiter F r n 6
    · have no:¬i.val-SerializedBody.delimiter F r n 5 ≤ 0:=by omega
      simp only [h4,h5,if_false,if_true,decide_eq_false no,and_self,true_or,false_or]
    · by_cases h6:SerializedBody.delimiter F r n 6 < i.val ∧ i.val < SerializedBody.delimiter F r n 7
      · have no:¬i.val-SerializedBody.delimiter F r n 6 ≤ 0:=by omega
        simp only [h4,h5,h6,if_false,if_true,decide_eq_false no,and_self,true_or,false_or]
      · by_cases h11:SerializedBody.delimiter F r n 11 < i.val ∧ i.val < SerializedBody.delimiter F r n 12
        · have no:¬i.val-SerializedBody.delimiter F r n 11 ≤ 0:=by omega
          simp only [h4,h5,h6,h11,if_false,if_true,decide_eq_false no,and_self,false_or]
        · simp only [h4,h5,h6,h11,if_false,false_or]
end NormalFinalClosure
