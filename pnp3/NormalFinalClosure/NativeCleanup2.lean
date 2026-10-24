import NormalFinalClosure.CleanupCertificates2
import NormalFinalClosure.SourceUpdates2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.Cleanup2,`NormalFinalClosure,["CleanChain","clean_chain"]),
    (`NormalFinalClosure.CleanupCertificates2,`NormalFinalClosure,["cleanup_3139","cleanup_3325","cleanup_3495","cleanup_3681","cleanup_3867","cleanup_4037"]),
    (`NormalFinalClosure.SourceCertificates2,`NormalFinalClosure,["restore_3122","restore_3308","restore_3664","restore_3850","virtualRestore_3494","virtualRestore_4036"]),
    (`NormalFinalClosure.SourceRoute2,`NormalFinalClosure,["RestoreRows","restore"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid"]),
    (`NormalFinalClosure.SourceImage2,`NormalFinalClosure,["rep_frame_low","rep_source","physical_room"]),
    (`NormalFinalClosure.SourceUpdates2,`NormalFinalClosure,["rep_restore"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing complete literal cleanup API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing complete literal cleanup owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong complete literal cleanup owner"
      logInfo m!"complete-literal-cleanup-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing complete cleanup Node"
    let some i:=e.getModuleIdxFor? name | throwError "Missing complete cleanup Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong complete cleanup Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private def start (k : Nat) (answer : Bool) (mode : Fin 3) := ns2 k
  (if answer then if mode.val=0 then 3122 else if mode.val=1 then 3308 else 3494
   else if mode.val=0 then 3664 else if mode.val=1 then 3850 else 4036)
private def after (k : Nat) (answer : Bool) (mode : Fin 3) := ns2 k
  (if answer then if mode.val=0 then 3139 else if mode.val=1 then 3325 else 3495
   else if mode.val=0 then 3681 else if mode.val=1 then 3867 else 4037)
private theorem chainCode (k : Nat) (answer : Bool) (mode : Fin 3) :
    CleanChain (Safe:=Safe2 k) (after k answer mode) (if answer then (machine2 k).accept else (machine2 k).reject) := by
  cases answer <;> fin_cases mode
  · exact cleanup_3681 k
  · exact cleanup_3867 k
  · exact cleanup_4037 k
  · exact cleanup_3139 k
  · exact cleanup_3325 k
  · exact cleanup_3495 k
private theorem restoreCode (k : Nat) (answer b : Bool) :
    RestoreRows (Safe:=Safe2 k) (start k answer (if b then 1 else 0)) (after k answer (if b then 1 else 0)) b := by
  cases answer <;> cases b
  · exact restore_3664 k
  · exact restore_3850 k
  · exact restore_3122 k
  · exact restore_3308 k
private theorem virtualCode (k : Nat) (answer : Bool) :
    (machine2 k).step (start k answer 2) none=(after k answer 2,none,.stay) := by
  cases answer
  · exact virtualRestore_4036 k
  · exact virtualRestore_3494 k
private theorem startSafe (k : Nat) (answer : Bool) : Safe2 k (start k answer 2) := by
  cases answer <;> exact ns2_safe k _
/-- All physical cleanup entries execute to a literal final sink/H/full cleared
image. No logical success/failure is assumed; answer selects the ACTUAL fixed
clean-ok/clean-bad entry already reached by the native decision code. -/
private theorem cleanup_physical (k : Nat) (answer : Bool) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a b c index : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) (hi:cursor < S) :
    ∃ t,t ≤ 1024*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (start k answer (if source ⟨cursor,hi⟩ then 1 else 0)) (D F r n 0)
        (repImage T F r n S cursor a b c index records))
      (node (if answer then (machine2 k).accept else (machine2 k).reject) (S+z+2+n+1)
        (repImage T F r n S S 0 0 0 0 [])) := by
  have room:=physical_room fr
  have fit:F+1 ≤ D F r n 13:=by change F+1 ≤ F+13*r+2*n+22;omega
  have hole:repImage T F r n S cursor a b c index records cursor=none:=by
    rw [rep_source fr cursor a b c index records cursor lo hi,if_pos rfl]
  have first:=restore (rep_frame_low fr cursor a b c index records) fit hi hole (by
    intro i low high
    rw [rep_source fr cursor a b c index records i (by omega) high,if_neg (by omega)]
    exact ⟨_,rfl⟩) (restoreCode k answer (source ⟨cursor,hi⟩))
  rw [rep_restore fr cursor a b c index records lo hi] at first
  obtain ⟨t,price,last⟩:=clean_chain fr (chainCode k answer (if source ⟨cursor,hi⟩ then 1 else 0)) a b c index records
  have path:=first.append last
  refine ⟨2*(F+1-cursor)+5+t,?_,path⟩
  omega
/-- Virtual EOF cleanup performs its distinct one stay entry, without writing
or erasing a virtual source cell, then the same real full cleanup and terminal. -/
private theorem cleanup_virtual (k : Nat) (answer : Bool) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a b c index : Nat) (records : List Nat)
    (virtual:S ≤ cursor) :
    ∃ t,t ≤ 1024*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (start k answer 2) (D F r n 0) (repImage T F r n S cursor a b c index records))
      (node (if answer then (machine2 k).accept else (machine2 k).reject) (S+z+2+n+1)
        (repImage T F r n S S 0 0 0 0 [])) := by
  have same:repImage T F r n S cursor a b c index records=repImage T F r n S S a b c index records:=by
    funext i
    simp only [repImage,show ¬(i=cursor ∧ cursor < S) by omega,show ¬(i=S ∧ S < S) by omega,if_false]
  rw [same]
  have at0:(repImage T F r n S S a b c index records) (D F r n 0)=none:=by
    have grid:=rep_grid fr S a b c index records
    exact blanks grid 0 (by decide)
  have first:=keep (start k answer 2) (after k answer 2) (D F r n 0) (D F r n 0)
    (repImage T F r n S S a b c index records) .stay (P:=D F r n 13)
    (by change F+1 ≤ F+13*r+2*n+22;omega) (by change F+1 ≤ F+13*r+2*n+22;omega)
    (startSafe k answer) (by rw [at0];exact virtualCode k answer) rfl
  obtain ⟨t,price,last⟩:=clean_chain fr (chainCode k answer 2) a b c index records
  exact ⟨1+t,by omega,first.append last⟩
end NormalFinalClosure
