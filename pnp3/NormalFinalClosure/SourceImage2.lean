import NormalFinalClosure.SourceAdvance2
import NormalFinalClosure.FrameFacts2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["put"]),
    (`NormalFinalClosure.SourceRoute2,`NormalFinalClosure,["LowFrame"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.headBefore","GuardFrame.eof","GuardFrame.registers","GuardFrame.left","GuardFrame.assignment","GuardFrame.right","GuardFrame.paid","GuardFrame.gap","GuardFrame.fence","GuardFrame.delimiters","GuardFrame.sourceCells"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["d_mono","frame_before"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact source image API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing source image owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source image owner"
      logInfo m!"source-image-exact-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev lowMk : {T : Nat → Option Bool} → {S z n F : Nat} →
    S+z+2+n+2 < F → T S=none → T (S+z+2)=none → T (S+z+2+n+1)=none →
    (∀ i,S < i → i < S+z+2 → ∃ b,T i=some b) →
    (∀ i,S+z+2 < i → i < S+z+2+n+1 → ∃ b,T i=some b) →
    T (S+z+2+n+2)=some true → (∀ i,S+z+2+n+2 < i → i < F → T i=none) →
    T F=some false → T (F+1)=none → LowFrame T S z n F := by
  run_tac do
    let owner:=`NormalFinalClosure.SourceRoute2
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure") "LowFrame") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing LowFrame constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing LowFrame owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong LowFrame owner"
    logInfo m!"source-full-low-frame-constructor|{name}|{ci.type}"
    closeMainGoal `lowMk (mkConst name (ci.levelParams.map Level.param))
private theorem rep_low {S z n F r W source T} (_fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (i : Nat) (hi:i ≤ F+1) :
    repImage T F r n S cursor a b c index records i=
      if i=cursor ∧ cursor < S then none else T i := by
  have noField (j : Nat) (hj:j ≤ 12):¬(D F r n j < i ∧ i < D F r n (j+1)):=by
    have h:=d_mono F r n 0 j (by omega) (by omega)
    change F+1 ≤ D F r n j at h
    omega
  simp only [repImage,noField 4 (by decide),noField 5 (by decide),noField 6 (by decide),
    noField 11 (by decide),noField 10 (by decide),if_false]
private theorem rep_unchanged {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (i : Nat) (lo:S ≤ i) (hi:i ≤ F+1) :
    repImage T F r n S cursor a b c index records i=T i := by
  rw [rep_low fr cursor a b c index records i hi,if_neg (by omega)]
private theorem physical_room {S z n F r W source T} (fr:GuardFrame S z n F r W source T) :
    S+z+2+n+2 < F := by
  have h:=headBefore fr
  by_contra no
  have eq:F=S+z+2+n+2:=by omega
  have a:=paid fr;have b:=fence fr
  rw [eq,a] at b
  cases b
private theorem frame_low {S z n F r W source T} (fr:GuardFrame S z n F r W source T) :
    LowFrame T S z n F := by
  refine lowMk (physical_room fr) (eof fr) (left fr) (right fr) ?_ (assignment fr) (paid fr) (gap fr) (fence fr) ?_
  · intro i lo hi
    exact ⟨false,registers fr i lo hi⟩
  · exact delimiters fr 0 (by decide)
private theorem rep_frame_low {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) :
    LowFrame (repImage T F r n S cursor a b c index records) S z n F := by
  have room:=physical_room fr
  have unchanged:=rep_unchanged fr cursor a b c index records
  refine lowMk room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [unchanged S le_rfl (by omega)];exact eof fr
  · rw [unchanged (S+z+2) (by omega) (by omega)];exact left fr
  · rw [unchanged (S+z+2+n+1) (by omega) (by omega)];exact right fr
  · intro i lo hi
    rw [unchanged i (by omega) (by omega)]
    exact ⟨false,registers fr i lo hi⟩
  · intro i lo hi
    rw [unchanged i (by omega) (by omega)]
    exact assignment fr i lo hi
  · rw [unchanged (S+z+2+n+2) (by omega) (by omega)];exact paid fr
  · intro i lo hi
    rw [unchanged i (by omega) (by omega)]
    exact gap fr i lo hi
  · rw [unchanged F (by omega) (by omega)];exact fence fr
  · rw [unchanged (F+1) (by omega) (by omega)]
    exact delimiters fr 0 (by decide)
private theorem rep_source {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (i : Nat) (lo:S-r ≤ i) (hi:i < S) :
    repImage T F r n S cursor a b c index records i=
      if i=cursor then none else some (source ⟨i,hi⟩) := by
  have room:=physical_room fr
  rw [rep_low fr cursor a b c index records i (by omega)]
  by_cases eq:i=cursor
  · subst i
    rw [if_pos ⟨rfl,hi⟩,if_pos rfl]
  · rw [if_neg (by omega),if_neg eq,sourceCells fr i lo hi]
/-- Exact finite-cell update of the shared representation after a physical
reader restores its current bit and lifts its successor. -/
private theorem rep_advance {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) (lo:S-r ≤ cursor) (hi:cursor < S) :
    put (put (repImage T F r n S cursor a b c index records) cursor (some (source ⟨cursor,hi⟩)))
      (cursor+1) (if cursor+1 < S then none else T (cursor+1))=
    repImage T F r n S (cursor+1) a b c index records := by
  have room:=physical_room fr
  funext i
  by_cases current:i=cursor
  · subst i
    rw [show put (put (repImage T F r n S cursor a b c index records) cursor (some (source ⟨cursor,hi⟩))) (cursor+1) (if cursor+1 < S then none else T (cursor+1)) cursor=some (source ⟨cursor,hi⟩) by simp only [put,show cursor≠cursor+1 by omega,if_false,if_true]]
    rw [rep_source fr (cursor+1) a b c index records cursor lo hi,if_neg (by omega)]
  · by_cases next:i=cursor+1
    · subst i
      simp only [put,if_true]
      rw [rep_low fr (cursor+1) a b c index records (cursor+1) (by omega)]
      by_cases physical:cursor+1 < S <;> simp only [physical,and_true,and_false,if_true,if_false]
    · simp only [put,current,next,if_false]
      dsimp only [repImage]
      rw [if_neg (by omega : ¬(i=cursor ∧ cursor < S)),if_neg (by omega : ¬(i=cursor+1 ∧ cursor+1 < S))]
end NormalFinalClosure
