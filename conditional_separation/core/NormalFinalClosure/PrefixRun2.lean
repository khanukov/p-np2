import NormalFinalClosure.PrefixSemantics2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.windowRoom","GuardFrame.rSource"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["beDone"]),
    (`NormalFinalClosure.PrefixCode2,`NormalFinalClosure,["compareState"]),
    (`NormalFinalClosure.PrefixLoop2,`NormalFinalClosure,["prefixGood","prefixGood_decidable","prefix_loop"]),
    (`NormalFinalClosure.PrefixEntry2,`NormalFinalClosure,["prefix_begin"]),
    (`NormalFinalClosure.PrefixSemantics2,`NormalFinalClosure,["windowBits","encodeBits","prefixRecords_original"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing actual BE-to-prefix composition API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing BE-to-prefix composition owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong BE-to-prefix composition owner"
      logInfo m!"actual-BE-prefix-composition-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing BE-prefix composition Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing BE-prefix composition Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong BE-prefix composition Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
/-- The whole prepared BE-exit to complete original prefix/padding execution.
No live callback is padded to a deadline. The physical buffer is derived from
literal executed writes and includes original bytes beyond decoder consumption. -/
private theorem prefix_run (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (i : Nat) (cap:i ≤ W) :
    let offset:=S-r+bitLength W
    ∃ t,t ≤ 8192*(r+1)*(D F r n 13+1) ∧
      if prefixGood source (min offset S) W i then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beDone k (sourceMode source (min offset S))) (D F r n 0)
          (repImage T F r n S (min offset S) (W-i) 0 0 i []))
        (node (compareState k (sourceMode source (min (offset+W) S))) (D F r n 0)
          (repImage T F r n S (min (offset+W) S) (W-i) 0 0 0
            (encodeBits (windowBits source offset i)++List.replicate (W-i) 0)))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beDone k (sourceMode source (min offset S))) (D F r n 0)
          (repImage T F r n S (min offset S) (W-i) 0 0 i []))
        (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  intro offset
  obtain ⟨a,ap,begin⟩:=prefix_begin k fr (min offset S) i
  have wr:=windowRoom fr
  have rs:=rSource fr
  obtain ⟨b,bp,loop⟩:=prefix_loop k fr W (min offset S) (W-i) i []
    (by dsimp only [offset];omega) (by omega) cap (by simpa only [List.length_nil,Nat.zero_add] using wr)
    (by intro j hj;simp only [List.length_nil] at hj;omega)
  refine ⟨a+b,?_,?_⟩
  · have mono:512*(W+1)*(D F r n 13+1) ≤ 512*(r+1)*(D F r n 13+1):=by nlinarith
    have mono2:4096*(W+1)*(D F r n 13+1) ≤ 4096*(r+1)*(D F r n 13+1):=by nlinarith
    nlinarith only [ap,bp,mono,mono2]
  · by_cases good:prefixGood source (min offset S) W i
    · rw [if_pos good] at loop ⊢
      rw [prefixRecords_original source W offset i cap,List.nil_append,
        show min (min offset S+W) S=min (offset+W) S by omega] at loop
      exact begin.append loop
    · rw [if_neg good] at loop ⊢
      exact begin.append loop
end NormalFinalClosure
