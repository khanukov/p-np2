import NormalFinalClosure.BEDigit2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","dec_zero"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.windowRoom"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary6"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","beState"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["be_dec","beDone"]),
    (`NormalFinalClosure.BEBit2,`NormalFinalClosure,["modeDigit"]),
    (`NormalFinalClosure.BEDigit2,`NormalFinalClosure,["digit_run"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["op_price"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing total native BE recurrence API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing total native BE owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong total native BE owner"
      logInfo m!"total-native-BE-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing total BE Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing total BE Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong total BE Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
/-- Proof-only fold of ORIGINAL padded source bits, not a machine instruction
or runtime oracle. Its capped physical refinement is the theorem below. -/
private def indexValue {S : Nat} (source : Fin S → Bool) : Nat → Nat → Nat → Nat
  | _,0,acc=>acc
  | cursor,v+1,acc=>indexValue source (min (cursor+1) S) v (2*acc+modeDigit (sourceMode source cursor))
private theorem indexValue_ge {S : Nat} (source : Fin S → Bool) (v cursor acc : Nat) :
    acc ≤ indexValue source cursor v acc := by
  induction v generalizing cursor acc with
  | zero=>exact le_rfl
  | succ v ih=>
    have h:=ih (min (cursor+1) S) (2*acc+modeDigit (sourceMode source cursor))
    change acc ≤ indexValue source (min (cursor+1) S) v (2*acc+modeDigit (sourceMode source cursor))
    omega
/-- COMPLETE actual BE loop, all remaining lengths and every physical/virtual
source boundary. Overflow is literal reject/H with exact full cleared image;
success has the exact value, counters, cursor and live prefix-copy control.
Every recursive digit is charged for its real unary and shuttle rows. -/
private theorem be_loop (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (v cursor index : Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) (ir:index ≤ W) (vr:v ≤ r) :
    let result:=indexValue source cursor v index
    ∃ t,t ≤ 8192*(v+1)*(W+1)*(D F r n 13+1) ∧
      if result ≤ W then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 v index []))
        (node (beDone k (sourceMode source (min (cursor+v) S))) (D F r n 0)
          (repImage T F r n S (min (cursor+v) S) (W-result) 0 0 result []))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 v index []))
        (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  induction v generalizing cursor index with
  | zero=>
    have g:=rep_grid fr cursor (W-index) 0 0 index []
    have zero:=dec_zero g (by decide) le_rfl (rep_width F r n 6 (by simp))
      (rep_unary6 fr cursor (W-index) 0 0 index []) (be_dec k (sourceMode source cursor))
    refine ⟨2*(D F r n 6-D F r n 0+6)+3,?_,?_⟩
    · have p:=op_price (D F r n) 6 0 (D F r n 13)
        (d_mono F r n 6 13 (by decide) (by decide)) (by decide) (by omega)
      have up:32*(D F r n 13+1) ≤ 8192*(0+1)*(W+1)*(D F r n 13+1):=by nlinarith
      exact p.trans up
    · change (if index ≤ W then _ else _)
      rw [if_pos ir,show min (cursor+0) S=cursor by omega]
      exact zero
  | succ v ih=>
    obtain ⟨a,ap,headPath⟩:=digit_run k fr cursor v index lo hi ir vr
    let next:=2*index+modeDigit (sourceMode source cursor)
    have eq:indexValue source cursor (v+1) index=indexValue source (min (cursor+1) S) v next:=rfl
    by_cases stepOK:next ≤ W
    · rw [if_pos stepOK] at headPath
      obtain ⟨b,bp,tail⟩:=ih (min (cursor+1) S) next (by omega) (by omega) stepOK (by omega)
      refine ⟨a+b,?_,?_⟩
      · nlinarith only [ap,bp]
      · change (if indexValue source cursor (v+1) index ≤ W then _ else _)
        rw [eq]
        by_cases allOK:indexValue source (min (cursor+1) S) v next ≤ W
        · rw [if_pos allOK] at tail ⊢
          have whole:=headPath.append tail
          rw [show min (min (cursor+1) S+v) S=min (cursor+(v+1)) S by omega] at whole
          exact whole
        · rw [if_neg allOK] at tail ⊢
          exact headPath.append tail
    · rw [if_neg stepOK] at headPath
      have ge:=indexValue_ge source v (min (cursor+1) S) next
      have doom:¬indexValue source cursor (v+1) index ≤ W:=by rw [eq];omega
      refine ⟨a,?_,?_⟩
      · have up:8192*(W+1)*(D F r n 13+1) ≤ 8192*(v+1+1)*(W+1)*(D F r n 13+1):=by nlinarith
        exact ap.trans up
      · change (if indexValue source cursor (v+1) index ≤ W then _ else _)
        rw [if_neg doom]
        exact headPath
end NormalFinalClosure
