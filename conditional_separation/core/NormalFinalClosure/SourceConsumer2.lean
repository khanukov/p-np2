import NormalFinalClosure.IndexImage2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid"]),
    (`NormalFinalClosure.SourceAdvance2,`NormalFinalClosure,["AdvanceRows","advance"]),
    (`NormalFinalClosure.SourceImage2,`NormalFinalClosure,["physical_room","rep_frame_low","rep_source"]),
    (`NormalFinalClosure.SourceUpdates2,`NormalFinalClosure,["rep_restore","rep_lift"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","sourceMode_physical","sourceMode_virtual"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing shared native source consumer API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing native source consumer owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong native source consumer owner"
      logInfo m!"shared-original-source-consumer-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing BE Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing BE Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong BE Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private theorem source_consume (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a b c index : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S)
    (entry out : Fin 3 → Fin (machine2 k).stateCount)
    (physicalCode:∀ bit,AdvanceRows (Safe:=Safe2 k) (entry (if bit then 1 else 0)) out bit)
    (virtualSafe:Safe2 k (entry 2))
    (virtualCode:(machine2 k).step (entry 2) none=(out 2,none,.stay)) :
    ∃ t,t ≤ 16*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (entry (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor a b c index records))
      (node (out (sourceMode source (min (cursor+1) S))) (D F r n 0)
        (repImage T F r n S (min (cursor+1) S) a b c index records)) := by
  have room:=physical_room fr
  have fit:F+1 ≤ D F r n 13:=by change F+1 ≤ F+13*r+2*n+22;omega
  by_cases phys:cursor < S
  · rw [sourceMode_physical phys]
    have hole:repImage T F r n S cursor a b c index records cursor=none:=by
      rw [rep_source fr cursor a b c index records cursor lo phys,if_pos rfl]
    obtain ⟨mode,E,cases',path⟩:=advance (rep_frame_low fr cursor a b c index records) fit phys hole (by
      intro i il ih
      rw [rep_source fr cursor a b c index records i (by omega) ih,if_neg (by omega)]
      exact ⟨_,rfl⟩) (physicalCode (source ⟨cursor,phys⟩))
    refine ⟨2*(F+1-cursor)+5,by omega,?_⟩
    rcases cases' with ⟨last,hm,ht⟩|⟨v,next,hm,hv,ht⟩
    · rw [hm,ht,rep_restore fr cursor a b c index records lo phys] at path
      rw [show min (cursor+1) S=S by omega,sourceMode_virtual le_rfl]
      exact path
    · have bit:v=source ⟨cursor+1,next⟩:=by
        rw [rep_source fr cursor a b c index records (cursor+1) (by omega) next,if_neg (by omega)] at hv
        exact (Option.some.inj hv).symm
      rw [hm,ht,rep_restore fr cursor a b c index records lo phys,rep_lift fr (cursor+1) a b c index records next,bit] at path
      rw [show min (cursor+1) S=cursor+1 by omega,sourceMode_physical next]
      exact path
  · have eq:cursor=S:=by omega
    subst cursor
    rw [sourceMode_virtual le_rfl,show min (S+1) S=S by omega,sourceMode_virtual le_rfl]
    have g:=rep_grid fr S a b c index records
    have row:=keep (entry 2) (out 2) (D F r n 0) (D F r n 0)
      (repImage T F r n S S a b c index records) .stay (P:=D F r n 13) fit fit
      virtualSafe (by rw [blanks g 0 (by decide)];exact virtualCode) rfl
    exact ⟨1,by omega,row⟩
end NormalFinalClosure
