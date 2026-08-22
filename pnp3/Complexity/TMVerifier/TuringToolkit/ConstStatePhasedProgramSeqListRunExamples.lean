import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRun
import Complexity.TMVerifier.TuringToolkit.GateWrappers

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace GateEvalCS

open Pnp3.Internal.PsubsetPpoly.TM
open ConstStatePhasedProgram

/-!
### Concrete non-dependent `seqList` composition

The two-gate theorem is the smallest semantic example that uses both the
adjacent lift/embed bridge and the exact singleton terminal closure.
-/

/-- Two ordered constant-gate programs form an actual `seqList` `RunSpec`.
The final composite configuration is exact, including the terminal boundary
step after the second gate, and both standalone tape-write postconditions are
preserved.  `d1 ≤ d2` supplies precisely the adjacent tape monotonicity used by
the bridge; this is not a theorem about unrestricted program lists. -/
theorem gateConstCS_seqList_two_runSpec
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
    let hBound2 : (c2Init.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n := by
      have hHeadEq : c1Final.head = c1.head := by
        obtain ⟨_, _, _, _, h, _⟩ :=
          CombineAtOffset.combineAtOffsetCS_run_full d1 d1 d1
            (le_refl _) (le_refl _) (fun _ _ => b1) c1 hPhase hState hBound1
        simpa [P1, c1Final, gateConstCS_timeBound] using h
      change (c1Final.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n
      rw [hHeadEq]
      show (c1.head : Nat) + d2 < n + (2 * d2 + 3) + 1
      have hBound1' : (c1.head : Nat) + d1 < n + (2 * d1 + 3) + 1 := hBound1
      omega
    let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    let c2Boundary := TM.stepConfig (M := (seq P2 idleCS).toPhased.toTM)
      (embedSeqConfig P2 idleCS c2Final)
    RunSpec (seqList [P1, P2])
      (embedSeqConfig P1 (seqList [P2]) c1) (fun cSeq =>
        cSeq = embedSeqP2Config P1 (seqList [P2]) c2Boundary ∧
        c1Final.tape = c1.write ⟨(c1.head : Nat) + d1, hBound1⟩ b1 ∧
        c2Final.tape = c2Init.write ⟨(c2Init.head : Nat) + d2, hBound2⟩ b2) := by
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
  obtain ⟨_, _, hP1Accept, _, hP1Head, hP1Tape⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full d1 d1 d1
      (le_refl _) (le_refl _) (fun _ _ => b1) c1 hPhase hState hBound1
  have hP1Head' : c1Final.head = c1.head := by
    simpa [c1Final, P1, gateConstCS_timeBound] using hP1Head
  have hBound2 : (c2Init.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n := by
    change (c1Final.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n
    rw [hP1Head']
    show (c1.head : Nat) + d2 < n + (2 * d2 + 3) + 1
    have hBound1' : (c1.head : Nat) + d1 < n + (2 * d1 + 3) + 1 := hBound1
    omega
  have hP2Phase : c2Init.state.fst.val = 0 := rfl
  have hP2State : c2Init.state.snd = (false, false) := rfl
  obtain ⟨_, _, hP2Accept, _, _, hP2Tape⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full d2 d2 d2
      (le_refl _) (le_refl _) (fun _ _ => b2)
      c2Init hP2Phase hP2State hBound2
  let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
  let c2Boundary := TM.stepConfig (M := (seq P2 idleCS).toPhased.toTM)
    (embedSeqConfig P2 idleCS c2Final)
  let post1 : Configuration (M := P1.toPhased.toTM) n → Prop :=
    fun c => c.tape = c1.write ⟨(c1.head : Nat) + d1, hBound1⟩ b1
  let post2 : Configuration (M := P2.toPhased.toTM) n → Prop :=
    fun c => c.tape = c2Init.write ⟨(c2Init.head : Nat) + d2, hBound2⟩ b2
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
        c2Init hP2Phase hP2State hBound2 s (by simpa [P2] using hs) |>.2
    reachesAcceptPhase := by
      simpa [P2] using hP2Accept
    postcondition := by
      simpa [P2, post2, gateConstCS_timeBound] using hP2Tape
  }
  let postTail : Configuration (M := (seqList [P2]).toPhased.toTM) n → Prop :=
    fun cTail => cTail = c2Boundary ∧ post2 c2Final
  have tailSpec : RunSpec (seqList [P2])
      (embedSeqConfig P2 idleCS c2Init) postTail := by
    exact RunSpec.seqList_singleton_exact P2 c2Init post2 spec2
  have combined := RunSpec.seqList_cons P1 P2 [] c1 post1 postTail
    hLen spec1 tailSpec
  exact combined.imp (by
    intro cSeq hPost
    rcases hPost with ⟨hFinal, hPost1, hTail⟩
    rcases hTail with ⟨hTailFinal, hPost2⟩
    rw [hTailFinal] at hFinal
    exact ⟨hFinal, hPost1, hPost2⟩)

/-- Direct full-run corollary of `gateConstCS_seqList_two_runSpec`. -/
theorem gateConstCS_seqList_two_run_full
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
    let hBound2 : (c2Init.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n := by
      have hHeadEq : c1Final.head = c1.head := by
        obtain ⟨_, _, _, _, h, _⟩ :=
          CombineAtOffset.combineAtOffsetCS_run_full d1 d1 d1
            (le_refl _) (le_refl _) (fun _ _ => b1) c1 hPhase hState hBound1
        simpa [P1, c1Final, gateConstCS_timeBound] using h
      change (c1Final.head : Nat) + d2 < P2.toPhased.toTM.tapeLength n
      rw [hHeadEq]
      show (c1.head : Nat) + d2 < n + (2 * d2 + 3) + 1
      have hBound1' : (c1.head : Nat) + d1 < n + (2 * d1 + 3) + 1 := hBound1
      omega
    let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    let c2Boundary := TM.stepConfig (M := (seq P2 idleCS).toPhased.toTM)
      (embedSeqConfig P2 idleCS c2Final)
    let cSeqFinal := TM.runConfig (M := (seqList [P1, P2]).toPhased.toTM)
      (embedSeqConfig P1 (seqList [P2]) c1) ((seqList [P1, P2]).timeBound n)
    cSeqFinal = embedSeqP2Config P1 (seqList [P2]) c2Boundary ∧
    c1Final.tape = c1.write ⟨(c1.head : Nat) + d1, hBound1⟩ b1 ∧
    c2Final.tape = c2Init.write ⟨(c2Init.head : Nat) + d2, hBound2⟩ b2 := by
  exact (gateConstCS_seqList_two_runSpec
    b1 b2 d1 d2 hD c1 hPhase hState hBound1).postcondition

/-- Three-gate recursion probe.  Unlike the semantic two-gate theorem above,
this theorem accepts the three standalone gate specifications as inputs; its
purpose is to pin that `seqList_cons` composes twice using only the two
adjacent destination comparisons. -/
theorem gateConstCS_seqList_three_recursion_probe
    (b1 b2 b3 : Bool) (d1 d2 d3 : Nat)
    (h12 : d1 ≤ d2) (h23 : d2 ≤ d3) {n : Nat}
    (c1 : Configuration (M := (gateConstCS b1 d1).toPhased.toTM) n)
    (spec1 : RunSpec (gateConstCS b1 d1) c1 (fun _ => True))
    (spec2 :
      let P1 := gateConstCS b1 d1
      let P2 := gateConstCS b2 d2
      let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hLen12 : P1.toPhased.toTM.tapeLength n ≤
          P2.toPhased.toTM.tapeLength n := by
        show n + (2 * d1 + 3) + 1 ≤ n + (2 * d2 + 3) + 1
        omega
      let hHead2 := Nat.lt_of_lt_of_le c1Final.head.isLt hLen12
      RunSpec P2 (liftP1ToP2 P1 P2 c1Final hHead2) (fun _ => True))
    (spec3 :
      let P1 := gateConstCS b1 d1
      let P2 := gateConstCS b2 d2
      let P3 := gateConstCS b3 d3
      let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hLen12 : P1.toPhased.toTM.tapeLength n ≤
          P2.toPhased.toTM.tapeLength n := by
        show n + (2 * d1 + 3) + 1 ≤ n + (2 * d2 + 3) + 1
        omega
      let hHead2 := Nat.lt_of_lt_of_le c1Final.head.isLt hLen12
      let c2Init := liftP1ToP2 P1 P2 c1Final hHead2
      let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
      let hLen23 : P2.toPhased.toTM.tapeLength n ≤
          P3.toPhased.toTM.tapeLength n := by
        show n + (2 * d2 + 3) + 1 ≤ n + (2 * d3 + 3) + 1
        omega
      let hHead3 := Nat.lt_of_lt_of_le c2Final.head.isLt hLen23
      RunSpec P3 (liftP1ToP2 P2 P3 c2Final hHead3) (fun _ => True)) :
    let P1 := gateConstCS b1 d1
    let P2 := gateConstCS b2 d2
    let P3 := gateConstCS b3 d3
    RunSpec (seqList [P1, P2, P3])
      (embedSeqConfig P1 (seqList [P2, P3]) c1) (fun _ => True) := by
  dsimp only
  let P1 := gateConstCS b1 d1
  let P2 := gateConstCS b2 d2
  let P3 := gateConstCS b3 d3
  let c1Final := TM.runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
  have hLen12 : P1.toPhased.toTM.tapeLength n ≤
      P2.toPhased.toTM.tapeLength n := by
    show n + P1.timeBound n + 1 ≤ n + P2.timeBound n + 1
    simp only [P1, P2, gateConstCS_timeBound]
    omega
  let hHead2 := Nat.lt_of_lt_of_le c1Final.head.isLt hLen12
  let c2Init := liftP1ToP2 P1 P2 c1Final hHead2
  let c2Final := TM.runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
  have hLen23 : P2.toPhased.toTM.tapeLength n ≤
      P3.toPhased.toTM.tapeLength n := by
    show n + P2.timeBound n + 1 ≤ n + P3.timeBound n + 1
    simp only [P2, P3, gateConstCS_timeBound]
    omega
  let hHead3 := Nat.lt_of_lt_of_le c2Final.head.isLt hLen23
  let c3Init := liftP1ToP2 P2 P3 c2Final hHead3
  have tail3 : RunSpec (seqList [P3])
      (embedSeqConfig P3 idleCS c3Init) (fun _ => True) :=
    (RunSpec.seqList_singleton_exact P3 c3Init (fun _ => True) spec3).imp
      (fun _ _ => trivial)
  have tail23 : RunSpec (seqList [P2, P3])
      (embedSeqConfig P2 (seqList [P3]) c2Init) (fun _ => True) :=
    (RunSpec.seqList_cons P2 P3 [] c2Init (fun _ => True) (fun _ => True)
      hLen23 spec2 tail3).imp (fun _ _ => trivial)
  exact (RunSpec.seqList_cons P1 P2 [P3] c1 (fun _ => True) (fun _ => True)
    hLen12 spec1 tail23).imp (fun _ _ => trivial)

end GateEvalCS
end TM
end PsubsetPpoly
end Internal
end Pnp3
