import NormalFinalClosure.AdvanceCertificates2
import NormalFinalClosure.RepCounters2
import NormalFinalClosure.SourceUpdates2
import NormalFinalClosure.Horner2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Unary","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.window"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.SourceImage2,`NormalFinalClosure,["physical_room","rep_frame_low","rep_source"]),
    (`NormalFinalClosure.SourceUpdates2,`NormalFinalClosure,["rep_restore","rep_lift"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_disjoint","rep_nohole","rep_field4","rep_field5","rep_field11"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["three"]),
    (`NormalFinalClosure.SourceAdvance2,`NormalFinalClosure,["AdvanceRows","advance"]),
    (`NormalFinalClosure.AdvanceCertificates2,`NormalFinalClosure,["advance_1118","advance_1970","virtualAdvance_2702"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing shared BE representation API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing BE representation owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong BE representation owner"
      logInfo m!"BE-representation-interface|{name}|{ci.type}"
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
private def sourceMode {S : Nat} (source : Fin S → Bool) (c : Nat) : Fin 3 :=
  if h:c < S then if source ⟨c,h⟩ then 1 else 0 else 2
private def beState (k : Nat) (mode : Fin 3) := if mode.val=0 then ns2 k 850 else if mode.val=1 then ns2 k 1628 else ns2 k 2434
private def beAdvance (k : Nat) (mode : Fin 3) := if mode.val=0 then ns2 k 1118 else if mode.val=1 then ns2 k 1970 else ns2 k 2702
private theorem sourceMode_physical {S source c} (h:c < S) :
    sourceMode (S:=S) source c=(if source ⟨c,h⟩ then 1 else 0) := by
  simp only [sourceMode,dif_pos h]
private theorem sourceMode_virtual {S source c} (h:S ≤ c) : sourceMode (S:=S) source c=2 := by
  simp only [sourceMode,dif_neg (show ¬c < S by omega)]
private theorem rep_unary3 {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index : Nat) (records : List Nat) :
    Unary (D F r n) (repImage T F r n S cursor a b c index records) 3 W := by
  intro i lo hi
  rw [show repImage T F r n S cursor a b c index records i=T i by
    simp only [repImage,if_neg (rep_nohole fr cursor i 3 (by decide) ⟨lo,hi⟩),
      if_neg (rep_disjoint (by decide : 3 ≤ 12) (by decide : 4 ≤ 12) (by decide) ⟨lo,hi⟩),
      if_neg (rep_disjoint (by decide : 3 ≤ 12) (by decide : 5 ≤ 12) (by decide) ⟨lo,hi⟩),
      if_neg (rep_disjoint (by decide : 3 ≤ 12) (by decide : 6 ≤ 12) (by decide) ⟨lo,hi⟩),
      if_neg (rep_disjoint (by decide : 3 ≤ 12) (by decide : 11 ≤ 12) (by decide) ⟨lo,hi⟩),
      if_neg (rep_disjoint (by decide : 3 ≤ 12) (by decide : 10 ≤ 12) (by decide) ⟨lo,hi⟩)]]
  exact window fr i lo hi
private theorem rep_horner {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a b c index v tmp available : Nat) (records : List Nat) :
    three (repImage T F r n S cursor a b c index records) (D F r n) 11 5 4 v tmp available=
      repImage T F r n S cursor available tmp c v records := by
  dsimp only [three]
  rw [rep_field11 fr,rep_field5 fr,rep_field4 fr]
private theorem beAdvance_code (k : Nat) (b : Bool) :
    AdvanceRows (Safe:=Safe2 k) (beAdvance k (if b then 1 else 0)) (beState k) b := by
  cases b
  · exact advance_1118 k
  · exact advance_1970 k
/-- A full physical index-source consume on the shared original-source image.
Virtual EOF consumes one literal stay, preserving its distinct mode2 and tape. -/
private theorem be_advance (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a b c index : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) :
    ∃ t,t ≤ 16*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (beAdvance k (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor a b c index records))
      (node (beState k (sourceMode source (min (cursor+1) S))) (D F r n 0)
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
      exact ⟨_,rfl⟩) (beAdvance_code k (source ⟨cursor,phys⟩))
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
    have row:=keep (beAdvance k 2) (beState k 2) (D F r n 0) (D F r n 0)
      (repImage T F r n S S a b c index records) .stay (P:=D F r n 13) fit fit
      (ns2_safe k 2702) (by rw [blanks g 0 (by decide)];exact virtualAdvance_2702 k) rfl
    exact ⟨1,by omega,row⟩
end NormalFinalClosure
