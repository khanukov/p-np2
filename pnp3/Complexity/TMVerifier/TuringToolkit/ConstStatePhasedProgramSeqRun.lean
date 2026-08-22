import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]

/-!
## Dependency-closed full runs of two sequential programs

`ConstStatePhasedProgram.lean` supplies the two configuration embeddings,
their multi-step commutation theorems, and the boundary lift.  This module
assembles those pieces once.  In particular, the handoff head bound is derived
from the tape-length comparison; callers do not have to provide the same fact
twice under different configuration types.
-/

/-- The semantic data needed to reuse a standalone full run inductively
inside `seq`.

`prefixSafe` contains the non-automatic part of the existing P1 embedding
premise.  Phase membership itself follows from the configuration's `Fin` type.
`reachesAcceptPhase` records arrival at the declared accept *phase* at the time
bound; it does not assert TM acceptance, which would also require the accepting
local state.  It justifies the one boundary step when the program is P1.
`postcondition` records the program-specific meaning of the standalone run;
the composition theorem transports it without prescribing a tape layout.

For P2, phase arrival and prefix accept-phase avoidance are intentionally
stronger than `seq_run_full` alone needs.  They are retained because
`RunSpec.seq` uses them to produce a `RunSpec` for the composite, making the
interface closed under sequential composition. -/
structure RunSpec (P : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P.toPhased.toTM) n)
    (Post : Configuration (M := P.toPhased.toTM) n → Prop) : Prop where
  prefixSafe : ∀ s < P.timeBound n,
    let c_s := TM.runConfig (M := P.toPhased.toTM) c s
    c_s.state.fst.val ≠ P.acceptPhase.val ∧
    ((P.toPhased.toTM.step c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
      c_s.head.val + 1 < P.toPhased.toTM.tapeLength n)
  reachesAcceptPhase :
    (TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)).state.fst.val =
      P.acceptPhase.val
  postcondition : Post (TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n))

/-- The boundary step after a completed P1 run is exactly the existing P2
embedding of `liftP1ToP2`.  The only cross-program condition is that P2's tape
is at least as long as P1's; this condition also derives the lift's head bound.
-/
theorem seq_boundary_step_eq_embedSeqP2Config_lift
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c1Final : Configuration (M := P1.toPhased.toTM) n)
    (hAcceptPhase : c1Final.state.fst.val = P1.acceptPhase.val)
    (hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n) :
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c1Final) =
      embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c1Final hHead) := by
  intro hHead
  have hPhase : (embedSeqConfig P1 P2 c1Final).state.fst.val < P1.numPhases := by
    exact c1Final.state.fst.isLt
  have hAcceptEmbedded :
      (embedSeqConfig P1 P2 c1Final).state.fst.val = P1.acceptPhase.val := hAcceptPhase
  have hState := stepConfig_seq_P1_boundary_phase P1 P2
    (embedSeqConfig P1 P2 c1Final) hPhase hAcceptEmbedded
  have hLocalState := stepConfig_seq_P1_boundary_state P1 P2
    (embedSeqConfig P1 P2 c1Final) hPhase hAcceptEmbedded
  have hHeadStep := stepConfig_seq_P1_boundary_head P1 P2
    (embedSeqConfig P1 P2 c1Final) hPhase hAcceptEmbedded
  have hTapeStep := stepConfig_seq_P1_boundary_tape P1 P2
    (embedSeqConfig P1 P2 c1Final) hPhase hAcceptEmbedded
  obtain ⟨hLiftPhase, hLiftState, hLiftHead, hLiftTape⟩ :=
    embedSeqP2Config_liftP1ToP2_eq_embedded_shape P1 P2 c1Final hHead hLen
  cases hL : TM.stepConfig (M := (seq P1 P2).toPhased.toTM)
      (embedSeqConfig P1 P2 c1Final) with
  | mk sL headL tapeL =>
    cases hR : embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c1Final hHead) with
    | mk sR headR tapeR =>
      have hs : sL = sR := by
        rw [hL] at hState hLocalState
        rw [hR] at hLiftPhase hLiftState
        have hval : sL.fst.val = sR.fst.val := by
          rw [hState, hLiftPhase]
        have hfst : sL.fst = sR.fst := Fin.ext hval
        have hsnd : sL.snd = sR.snd := by
          rw [hLocalState, hLiftState]
        exact Sigma.ext hfst (by rw [hfst]; exact heq_of_eq hsnd)
      have hh : headL = headR := by
        rw [hL] at hHeadStep
        rw [hR] at hLiftHead
        have hHeadStep' : headL = (embedSeqConfig P1 P2 c1Final).head := by
          simpa only using hHeadStep
        have hLiftHead' : headR.val = c1Final.head.val := by
          simpa only using hLiftHead
        apply Fin.ext
        have hLeft : headL.val = c1Final.head.val := by
          rw [hHeadStep']
          rfl
        rw [hLeft, hLiftHead']
      have ht : tapeL = tapeR := by
        rw [hL] at hTapeStep
        rw [hR] at hLiftTape
        have hTapeStep' : tapeL = (embedSeqConfig P1 P2 c1Final).tape := by
          simpa only using hTapeStep
        have hLiftTape' : tapeR = (embedSeqConfig P1 P2 c1Final).tape := by
          simpa only using hLiftTape
        rw [hTapeStep', hLiftTape']
      subst hs
      subst hh
      subst ht
      rfl

/-- Full semantic composition for two `ConstStatePhasedProgram`s.

Starting from P1 configuration `c1`, the composite starts at
`embedSeqConfig P1 P2 c1`.  After P1's run and the boundary step, P2 starts
from `liftP1ToP2` applied to P1's final configuration.  The final composite
configuration is exactly `embedSeqP2Config` of P2's standalone final
configuration.  Both component postconditions are returned at those exact
standalone configurations. -/
theorem seq_run_full
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c1 : Configuration (M := P1.toPhased.toTM) n)
    (Post1 : Configuration (M := P1.toPhased.toTM) n → Prop)
    (Post2 : Configuration (M := P2.toPhased.toTM) n → Prop)
    (hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n)
    (spec1 : RunSpec P1 c1 Post1)
    (spec2 :
      let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
        Nat.lt_of_lt_of_le c1Final.head.isLt hLen
      RunSpec P2 (liftP1ToP2 P1 P2 c1Final hHead) Post2) :
    let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    let c2Init := liftP1ToP2 P1 P2 c1Final hHead
    let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    TM.runConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c1) ((seq P1 P2).timeBound n) =
      embedSeqP2Config P1 P2 c2Final ∧
    Post1 c1Final ∧ Post2 c2Final := by
  dsimp only
  let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
  let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
    Nat.lt_of_lt_of_le c1Final.head.isLt hLen
  let c2Init := liftP1ToP2 P1 P2 c1Final hHead
  let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
  have hP1Run :
      TM.runConfig (M := (seq P1 P2).toPhased.toTM)
          (embedSeqConfig P1 P2 c1) (P1.timeBound n) =
        embedSeqConfig P1 P2 c1Final :=
    embedSeqConfig_runConfig_eq P1 P2 c1 (P1.timeBound n) (by
      intro s hs
      let c_s := TM.runConfig (M := P1.toPhased.toTM) c1 s
      exact ⟨c_s.state.fst.isLt, spec1.prefixSafe s hs⟩)
  have hBoundary :
      TM.runConfig (M := (seq P1 P2).toPhased.toTM)
          (embedSeqConfig P1 P2 c1) (P1.timeBound n + 1) =
        embedSeqP2Config P1 P2 c2Init := by
    rw [runConfig_succ, hP1Run]
    exact seq_boundary_step_eq_embedSeqP2Config_lift P1 P2 c1Final
      spec1.reachesAcceptPhase hLen
  have hP2Run :
      TM.runConfig (M := (seq P1 P2).toPhased.toTM)
          (embedSeqP2Config P1 P2 c2Init) (P2.timeBound n) =
        embedSeqP2Config P1 P2 c2Final :=
    embedSeqP2Config_runConfig_eq P1 P2 c2Init (P2.timeBound n)
      (fun s hs =>
        let c_s := TM.runConfig (M := P2.toPhased.toTM) c2Init s
        ⟨c_s.state.fst.isLt, (spec2.prefixSafe s hs).2⟩)
  refine ⟨?_, spec1.postcondition, spec2.postcondition⟩
  rw [seq_timeBound]
  have hTime : P1.timeBound n + P2.timeBound n + 1 =
      (P1.timeBound n + 1) + P2.timeBound n := by omega
  rw [hTime, runConfig_add, hBoundary, hP2Run]

/-- Sequential closure of `RunSpec`.

The composite postcondition identifies the exact final composite
configuration and preserves both component postconditions at their standalone
final configurations.  Unlike `seq_run_full` by itself, this theorem has the
same `RunSpec` shape as its component hypotheses and is therefore the genuine
induction interface for future right-nested `seqList` correctness.

The P2 fields that are stronger than configuration flow alone requires are
used here: prefix accept-phase avoidance proves that the composite does not
reach its accept phase early, and final phase arrival proves that it reaches
the composite accept phase at the declared bound. -/
theorem RunSpec.seq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c1 : Configuration (M := P1.toPhased.toTM) n)
    (Post1 : Configuration (M := P1.toPhased.toTM) n → Prop)
    (Post2 : Configuration (M := P2.toPhased.toTM) n → Prop)
    (hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n)
    (spec1 : RunSpec P1 c1 Post1)
    (spec2 :
      let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
        Nat.lt_of_lt_of_le c1Final.head.isLt hLen
      RunSpec P2 (liftP1ToP2 P1 P2 c1Final hHead) Post2) :
    let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    let c2Init := liftP1ToP2 P1 P2 c1Final hHead
    let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    RunSpec (seq P1 P2) (embedSeqConfig P1 P2 c1) (fun c =>
      c = embedSeqP2Config P1 P2 c2Final ∧
      Post1 c1Final ∧ Post2 c2Final) := by
  dsimp only
  let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
  let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
    Nat.lt_of_lt_of_le c1Final.head.isLt hLen
  let c2Init := liftP1ToP2 P1 P2 c1Final hHead
  let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
  have hP1Run :
      TM.runConfig (M := (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM)
          (embedSeqConfig P1 P2 c1) (P1.timeBound n) =
        embedSeqConfig P1 P2 c1Final :=
    embedSeqConfig_runConfig_eq P1 P2 c1 (P1.timeBound n) (by
      intro s hs
      let c_s := TM.runConfig (M := P1.toPhased.toTM) c1 s
      exact ⟨c_s.state.fst.isLt, spec1.prefixSafe s hs⟩)
  have hBoundary :
      TM.runConfig (M := (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM)
          (embedSeqConfig P1 P2 c1) (P1.timeBound n + 1) =
        embedSeqP2Config P1 P2 c2Init := by
    rw [runConfig_succ, hP1Run]
    exact seq_boundary_step_eq_embedSeqP2Config_lift P1 P2 c1Final
      spec1.reachesAcceptPhase hLen
  have hFinal := seq_run_full P1 P2 c1 Post1 Post2 hLen spec1 spec2
  refine {
    prefixSafe := ?_
    reachesAcceptPhase := ?_
    postcondition := ?_
  }
  · intro s hs
    let c_s := TM.runConfig
      (M := (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM)
      (embedSeqConfig P1 P2 c1) s
    change c_s.state.fst.val ≠ (ConstStatePhasedProgram.seq P1 P2).acceptPhase.val ∧
      (((ConstStatePhasedProgram.seq P1 P2).toPhased.toTM.step
          c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
        c_s.head.val + 1 <
          (ConstStatePhasedProgram.seq P1 P2).toPhased.toTM.tapeLength n)
    by_cases hP1 : s ≤ P1.timeBound n
    · have hP1Prefix : c_s = embedSeqConfig P1 P2
          (TM.runConfig (M := P1.toPhased.toTM) c1 s) := by
        exact embedSeqConfig_runConfig_eq P1 P2 c1 s (by
          intro r hr
          let c_r := TM.runConfig (M := P1.toPhased.toTM) c1 r
          exact ⟨c_r.state.fst.isLt, spec1.prefixSafe r (by omega)⟩)
      constructor
      · rw [hP1Prefix]
        simp only [embedSeqConfig_state_fst_val, seq_acceptPhase_val]
        have hPhase :=
          (TM.runConfig (M := P1.toPhased.toTM) c1 s).state.fst.isLt
        simp only [toPhased_numPhases] at hPhase
        omega
      · intro _
        rw [hP1Prefix]
        simp only [embedSeqConfig_head_val]
        have hHeadBound :=
          (TM.runConfig (M := P1.toPhased.toTM) c1 s).head.isLt
        simp only [PhasedProgram.toTM_tapeLength, toPhased_timeBound] at hHeadBound ⊢
        simp only [seq_timeBound]
        omega
    · let r := s - (P1.timeBound n + 1)
      have hr : r < P2.timeBound n := by
        dsimp only [r]
        simp only [seq_timeBound] at hs
        omega
      have hsSplit : s = P1.timeBound n + 1 + r := by
        dsimp only [r]
        omega
      have hP2Prefix : c_s = embedSeqP2Config P1 P2
          (TM.runConfig (M := P2.toPhased.toTM) c2Init r) := by
        dsimp only [c_s]
        rw [hsSplit, runConfig_add, hBoundary]
        exact embedSeqP2Config_runConfig_eq P1 P2 c2Init r (by
          intro q hq
          let c_q := TM.runConfig (M := P2.toPhased.toTM) c2Init q
          exact ⟨c_q.state.fst.isLt, (spec2.prefixSafe q (by omega)).2⟩)
      constructor
      · rw [hP2Prefix]
        simp only [embedSeqP2Config_state_fst_val, seq_acceptPhase_val]
        exact fun hEq => (spec2.prefixSafe r hr).1 (Nat.add_left_cancel hEq)
      · intro _
        rw [hP2Prefix]
        simp only [embedSeqP2Config_head_val]
        have hHeadBound :=
          (TM.runConfig (M := P2.toPhased.toTM) c2Init r).head.isLt
        simp only [PhasedProgram.toTM_tapeLength, toPhased_timeBound] at hHeadBound ⊢
        simp only [seq_timeBound]
        omega
  · rw [hFinal.1]
    simp only [embedSeqP2Config_state_fst_val, seq_acceptPhase_val]
    exact congrArg (fun phase => P1.numPhases + phase) spec2.reachesAcceptPhase
  · exact hFinal

/-- Terminal closure for the singleton `seqList` case.

Unlike `RunSpec.seq`, this theorem does not run `idleCS` as a standalone
second program and therefore needs no impossible comparison from `P`'s tape
length to the shorter idle tape.  It transports the `P` run inside the
composite, takes the handoff step there, and records directly that this step
preserves the embedded final head and tape.  Since `idleCS` starts at its
accept phase, that same boundary step reaches the composite accept phase. -/
theorem RunSpec.seqList_singleton [Inhabited S]
    (P : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P.toPhased.toTM) n)
    (Post : Configuration (M := P.toPhased.toTM) n → Prop)
    (spec : RunSpec P c Post) :
    let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
    RunSpec (seqList [P]) (embedSeqConfig P idleCS c) (fun cSeq =>
      cSeq.head = (embedSeqConfig P idleCS cFinal).head ∧
      cSeq.tape = (embedSeqConfig P idleCS cFinal).tape ∧
      Post cFinal) := by
  dsimp only
  let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
  have hPRun :
      TM.runConfig (M := (ConstStatePhasedProgram.seq P idleCS).toPhased.toTM)
          (embedSeqConfig P idleCS c) (P.timeBound n) =
        embedSeqConfig P idleCS cFinal :=
    embedSeqConfig_runConfig_eq P idleCS c (P.timeBound n) (by
      intro s hs
      let c_s := TM.runConfig (M := P.toPhased.toTM) c s
      exact ⟨c_s.state.fst.isLt, spec.prefixSafe s hs⟩)
  have hFinal :
      TM.runConfig (M := (seqList [P]).toPhased.toTM)
          (embedSeqConfig P idleCS c) ((seqList [P]).timeBound n) =
        TM.stepConfig (M := (ConstStatePhasedProgram.seq P idleCS).toPhased.toTM)
          (embedSeqConfig P idleCS cFinal) := by
    change TM.runConfig (M := (ConstStatePhasedProgram.seq P idleCS).toPhased.toTM)
        (embedSeqConfig P idleCS c) (P.timeBound n + 0 + 1) = _
    rw [Nat.add_zero, runConfig_succ, hPRun]
  refine RunSpec.mk ?_ ?_ ?_
  · intro s hs
    let c_s := TM.runConfig (M := (seqList [P]).toPhased.toTM)
      (embedSeqConfig P idleCS c) s
    change c_s.state.fst.val ≠ (seqList [P]).acceptPhase.val ∧
      (((seqList [P]).toPhased.toTM.step
          c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
        c_s.head.val + 1 < (seqList [P]).toPhased.toTM.tapeLength n)
    have hsP : s ≤ P.timeBound n := by
      change s < P.timeBound n + 0 + 1 at hs
      omega
    have hPrefix : c_s = embedSeqConfig P idleCS
        (TM.runConfig (M := P.toPhased.toTM) c s) := by
      exact embedSeqConfig_runConfig_eq P idleCS c s (by
        intro r hr
        let c_r := TM.runConfig (M := P.toPhased.toTM) c r
        exact ⟨c_r.state.fst.isLt, spec.prefixSafe r (by omega)⟩)
    constructor
    · rw [hPrefix]
      change (TM.runConfig (M := P.toPhased.toTM) c s).state.fst.val ≠
        P.numPhases + 0
      have hPhase :=
        (TM.runConfig (M := P.toPhased.toTM) c s).state.fst.isLt
      simp only [toPhased_numPhases] at hPhase
      omega
    · intro _
      rw [hPrefix]
      simp only [embedSeqConfig_head_val]
      have hHeadBound :=
        (TM.runConfig (M := P.toPhased.toTM) c s).head.isLt
      simp only [PhasedProgram.toTM_tapeLength, toPhased_timeBound] at hHeadBound ⊢
      change _ < n + (P.timeBound n + 0 + 1) + 1
      omega
  · rw [hFinal]
    have hPhase : (embedSeqConfig P idleCS cFinal).state.fst.val < P.numPhases := by
      exact cFinal.state.fst.isLt
    have hBoundary := stepConfig_seq_P1_boundary_phase P idleCS
      (embedSeqConfig P idleCS cFinal) hPhase spec.reachesAcceptPhase
    change
      (TM.stepConfig (M := (ConstStatePhasedProgram.seq P idleCS).toPhased.toTM)
        (embedSeqConfig P idleCS cFinal)).state.fst.val = P.numPhases + 0
    simpa only using hBoundary
  · rw [hFinal]
    have hPhase : (embedSeqConfig P idleCS cFinal).state.fst.val < P.numPhases := by
      exact cFinal.state.fst.isLt
    exact ⟨
      stepConfig_seq_P1_boundary_head P idleCS
        (embedSeqConfig P idleCS cFinal) hPhase spec.reachesAcceptPhase,
      stepConfig_seq_P1_boundary_tape P idleCS
        (embedSeqConfig P idleCS cFinal) hPhase spec.reachesAcceptPhase,
      spec.postcondition⟩

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
