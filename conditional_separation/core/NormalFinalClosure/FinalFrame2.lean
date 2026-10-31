import NormalFinalClosure.EndFrame2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["GuardFrame","D"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["d_mono"]),
    (`NormalFinalClosure.EndFrame2,`NormalFinalClosure,["low_caller","high_caller","caller_blanks","caller_cell","imageOutside"]),
    (`SerializedBodyCompletion.Case,`SerializedBodyCompletion,["cellValue"]),
    (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,["Layout","Layout.rS","Layout.windowPositive","Layout.windowRoom","Layout.arena","Layout.paid","Layout.sourceCells","Layout.eof","Layout.registers","Layout.left","Layout.right","Layout.fence","Layout.metadataEmpty"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing actual final frame API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing final frame owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong final frame owner"
      let aliasName:=(leaf.splitOn ".").getLast!
      logInfo m!"actual-final-frame-API|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev frameMk : {S z n F r W : Nat} → {source : Fin S → Bool} → {T : Nat → Option Bool} →
    r ≤ S → 0 < W → W ≤ r → S+z+2+n+1 < F →
    (∀ i,S-r ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩)) → T S=none →
    (∀ i,S < i → i < S+z+2 → T i=some false) → T (S+z+2)=none →
    (∀ i,S+z+2 < i → i < S+z+2+n+1 → ∃ b,T i=some b) → T (S+z+2+n+1)=none →
    T (S+z+2+n+2)=some true → (∀ i,S+z+2+n+2 < i → i < F → T i=none) → T F=some false →
    (∀ j,j ≤ 13 → T (D F r n j)=none) →
    (∀ j i,j < 13 → D F r n j < i → i < D F r n (j+1) → ∃ b,T i=some b) →
    (∀ i,D F r n 3 < i → i < D F r n 4 → T i=some (decide (i-D F r n 3 ≤ W))) →
    (∀ i,D F r n 10 < i → i < D F r n 11 → T i=some true) → GuardFrame S z n F r W source T := by
  run_tac do
    let owner:=`NormalFinalClosure.Frame2
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure") "GuardFrame") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing actual GuardFrame constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing constructor owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong constructor owner"
    logInfo m!"full-final-frame-constructor|{name}|{ci.type}"
    closeMainGoal `frameMk (mkConst name (ci.levelParams.map Level.param))
/-- Derives the static guard ABI from the SAME raw layout and entire actual
rowsDone image. The only extra inequality is the raw geometric identity p=S-r. -/
private theorem rows_done_frame {B R S z n r g W M A Q source T}
    (layout:Layout B R S z n r g W M A Q source T) (pSource:A ≤ S-r)
    (nodes used rem quota : Nat) (beta : Fin n → Bool) :
    GuardFrame S z n (FixedRawLengthFence.fencePos R) r W source
      (PhysicalCallerClosure.callerImage T S z n (FixedRawLengthFence.fencePos R) r g W M 1 beta nodes used rem quota) := by
  let F:=FixedRawLengthFence.fencePos R
  let E:=PhysicalCallerClosure.callerImage T S z n F r g W M 1 beta nodes used rem quota
  have arenaH:S+z+2+n+1 < F:=by have h:=arena layout;omega
  have paidH:S+z+2+n+2 < F:=by have h:=arena layout;have q:=paid layout;omega
  have low (i : Nat) (hi:i ≤ F):E i=
      if h:S+z+2 < i ∧ i < S+z+2+n+1 then some (beta ⟨S+z+2+n+1-1-i,by omega⟩)
      else if S+z+2+n+1 < i ∧ i < F then
        if i ≤ S+z+2+n+1+1 then some true else none else T i :=
    low_caller T S z n F r g W M 1 nodes used rem quota beta i hi
  change GuardFrame S z n F r W source E
  refine frameMk (T:=E) (rS layout) (windowPositive layout) (windowRoom layout) arenaH ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i lo hi
    rw [low i (by omega),dif_neg (by omega),if_neg (by omega)]
    exact sourceCells layout i (by omega) hi
  · rw [low S (by omega),dif_neg (by omega),if_neg (by omega)]
    exact eof layout
  · intro i lo hi
    rw [low i (by omega),dif_neg (by omega),if_neg (by omega)]
    exact registers layout i lo hi
  · rw [low (S+z+2) (by omega),dif_neg (by omega),if_neg (by omega)]
    exact left layout
  · intro i lo hi
    rw [low i (by omega),dif_pos ⟨lo,hi⟩]
    exact ⟨_,rfl⟩
  · rw [low (S+z+2+n+1) (by omega),dif_neg (by omega),if_neg (by omega)]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using right layout
  · rw [low (S+z+2+n+2) (by omega),dif_neg (by omega),if_pos (by omega),if_pos (by omega)]
  · intro i lo hi
    rw [low i (by omega),dif_neg (by omega),if_pos (by omega),if_neg (by omega)]
  · rw [low F le_rfl,dif_neg (by omega),if_neg (by omega)]
    exact fence layout
  · intro j hj
    by_cases bound:j ≤ 12
    · simp only [D,if_pos bound]
      exact caller_blanks T S z n F r g W M 1 nodes used rem quota beta arenaH j bound
    · have eq:j=13:=by omega
      subst j
      change E (SerializedBody.delimiter F r n 12+6)=none
      dsimp only [E]
      rw [high_caller T S z n F r g W M 1 nodes used rem quota beta _ arenaH (by change F < F+13*r+2*n+16+6;omega),if_neg (by omega)]
      exact imageOutside T F r n g W (S-min M S) nodes used rem quota _ (Or.inr (by omega)) |>.trans
        (metadataEmpty layout _ (by change SerializedBody.delimiter F r n 12 < SerializedBody.delimiter F r n 12+6;omega) le_rfl)
  · intro j i hj lo hi
    by_cases bound:j < 12
    · have hi':i < SerializedBody.delimiter F r n (j+1):=by
        simpa only [D,if_pos (show j+1 ≤ 12 by omega)] using hi
      have lo':SerializedBody.delimiter F r n j < i:=by
        simpa only [D,if_pos (show j ≤ 12 by omega)] using lo
      exact ⟨_,caller_cell T S z n F r g W M 1 nodes used rem quota beta arenaH j i bound lo' hi'⟩
    · have eq:j=12:=by omega
      subst j
      change SerializedBody.delimiter F r n 12 < i at lo
      change i < SerializedBody.delimiter F r n 12+6 at hi
      have lower:F < i:=by change F+13*r+2*n+16 < i at lo;omega
      refine ⟨false,?_⟩
      dsimp only [E]
      rw [high_caller T S z n F r g W M 1 nodes used rem quota beta i arenaH lower,if_pos ⟨lo,hi⟩]
  · intro i lo hi
    exact caller_cell T S z n F r g W M 1 nodes used rem quota beta arenaH 3 i (by decide) lo hi
  · intro i lo hi
    exact caller_cell T S z n F r g W M 1 nodes used rem quota beta arenaH 10 i (by decide) lo hi
end NormalFinalClosure
