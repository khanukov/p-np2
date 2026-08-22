import Complexity.TMVerifier.TuringToolkit.GateWrappers

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

end ConstStatePhasedProgram

namespace GateEvalCS

open Pnp3.Internal.PsubsetPpoly.TM
open ConstStatePhasedProgram

/-!
### Concrete two-constant-gate instance

This theorem exercises the generic API with two real gate programs.  It states
the standalone meaning of both pieces as sequential tape writes and identifies
the composite final configuration with the lifted/embedded second run.
-/

/-- A full `seq` run of two `gateConstCS` pieces is exactly the embedded
standalone second-gate run.  The two postconditions record, in order, the write
performed by P1 on the original configuration and the write performed by P2 on
the boundary lift.  In particular, the second postcondition is relative to
`c2Init`, not directly to P1's original configuration. -/
theorem gateConstCS_seq_run_full
    (b1 b2 : Bool) (d1 d2 : Nat) (hD : d1 ≤ d2) {n : Nat}
    (c1 : Configuration (M := (gateConstCS b1 d1).toPhased.toTM) n)
    (hPhase : c1.state.fst.val = 0)
    (hState : c1.state.snd = (false, false))
    (hBound1 : (c1.head : Nat) + d1 <
      (gateConstCS b1 d1).toPhased.toTM.tapeLength n) :
    let P1 := gateConstCS b1 d1
    let P2 := gateConstCS b2 d2
    let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n := by
      show n + (2 * d1 + 3) + 1 ≤ n + (2 * d2 + 3) + 1
      omega
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    let c2Init := liftP1ToP2 P1 P2 c1Final hHead
    let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    TM.runConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c1) ((seq P1 P2).timeBound n) =
      embedSeqP2Config P1 P2 c2Final ∧
    c1Final.tape = c1.write ⟨(c1.head : Nat) + d1, hBound1⟩ b1 ∧
    c2Final.tape = c2Init.write
      ⟨(c2Init.head : Nat) + d2, by
        have hHeadEq : c1Final.head = c1.head := by
          obtain ⟨_, _, _, _, h, _⟩ :=
            CombineAtOffset.combineAtOffsetCS_run_full d1 d1 d1
              (le_refl _) (le_refl _) (fun _ _ => b1) c1 hPhase hState hBound1
          simpa [P1, c1Final, gateConstCS_timeBound] using h
        change (c1Final.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n
        rw [hHeadEq]
        show (c1.head : Nat) + d2 < n + (2 * d2 + 3) + 1
        have hBound1' : (c1.head : Nat) + d1 < n + (2 * d1 + 3) + 1 := hBound1
        omega⟩ b2 := by
  dsimp only
  let P1 := gateConstCS b1 d1
  let P2 := gateConstCS b2 d2
  let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
  have hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n := by
    show n + P1.timeBound n + 1 ≤ n + P2.timeBound n + 1
    simp only [P1, P2, gateConstCS_timeBound]
    omega
  let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
    Nat.lt_of_lt_of_le c1Final.head.isLt hLen
  let c2Init := liftP1ToP2 P1 P2 c1Final hHead
  let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
  obtain ⟨_, _, hP1Accept, _, hP1Head, hP1Tape⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full d1 d1 d1
      (le_refl _) (le_refl _) (fun _ _ => b1) c1 hPhase hState hBound1
  have hP1Head' : c1Final.head = c1.head := by
    simpa [c1Final, P1, gateConstCS_timeBound] using hP1Head
  have hBound2Init : (c2Init.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n := by
    change (c1Final.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n
    rw [hP1Head']
    show (c1.head : Nat) + d2 < n + (2 * d2 + 3) + 1
    have hBound1' : (c1.head : Nat) + d1 < n + (2 * d1 + 3) + 1 := hBound1
    omega
  have hP2Phase : c2Init.state.fst.val = 0 := rfl
  have hP2State : c2Init.state.snd = (false, false) := rfl
  obtain ⟨_, _, hP2Accept, _, _, hP2Tape⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full d2 d2 d2
      (le_refl _) (le_refl _) (fun _ _ => b2) c2Init hP2Phase hP2State hBound2Init
  let post1 : Configuration (M := P1.toPhased.toTM) n → Prop :=
    fun c => c.tape = c1.write ⟨(c1.head : Nat) + d1, hBound1⟩ b1
  let post2 : Configuration (M := P2.toPhased.toTM) n → Prop :=
    fun c => c.tape = c2Init.write ⟨(c2Init.head : Nat) + d2, hBound2Init⟩ b2
  let spec1 : RunSpec P1 c1 post1 := {
    prefixSafe := by
      intro s hs
      exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
        d1 d1 d1 (le_refl _) (le_refl _) (fun _ _ => b1)
        c1 hPhase hState hBound1 s (by simpa [P1] using hs) |>.2
    reachesAcceptPhase := by
      simpa [P1] using hP1Accept
    postcondition := by
      simpa [P1, post1, gateConstCS_timeBound] using hP1Tape
  }
  let spec2 : RunSpec P2 c2Init post2 := {
    prefixSafe := by
      intro s hs
      exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
        d2 d2 d2 (le_refl _) (le_refl _) (fun _ _ => b2)
        c2Init hP2Phase hP2State hBound2Init s (by simpa [P2] using hs) |>.2
    reachesAcceptPhase := by
      simpa [P2] using hP2Accept
    postcondition := by
      simpa [P2, post2, gateConstCS_timeBound] using hP2Tape
  }
  have hRun := seq_run_full P1 P2 c1 post1 post2 hLen spec1 spec2
  exact hRun

end GateEvalCS
end TM
end PsubsetPpoly
end Internal
end Pnp3
