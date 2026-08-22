import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRun
import Complexity.TMVerifier.TuringToolkit.GateWrappers

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace GateEvalCS

open Pnp3.Internal.PsubsetPpoly.TM
open ConstStatePhasedProgram

/-!
### Concrete constant-gate instances

The singleton theorem exercises the terminal closure used by the `seqList`
base case.  The two-piece theorem exercises ordinary `RunSpec.seq`-style
composition and identifies the composite final configuration with the
lifted/embedded second run.
-/

/-- A concrete `RunSpec` for the actual singleton-list representation
`seqList [gateConstCS b d]`.  Its terminal handoff preserves the embedded
standalone gate's final head and tape, while the standalone postcondition
records the gate's write. -/
theorem gateConstCS_seqList_singleton_runSpec
    (b : Bool) (d : Nat) {n : Nat}
    (c : Configuration (M := (gateConstCS b d).toPhased.toTM) n)
    (hPhase : c.state.fst.val = 0)
    (hState : c.state.snd = (false, false))
    (hBound : (c.head : Nat) + d <
      (gateConstCS b d).toPhased.toTM.tapeLength n) :
    let P := gateConstCS b d
    let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
    RunSpec (seqList [P]) (embedSeqConfig P idleCS c) (fun cSeq =>
      cSeq.head = (embedSeqConfig P idleCS cFinal).head ∧
      cSeq.tape = (embedSeqConfig P idleCS cFinal).tape ∧
      cFinal.tape = c.write ⟨(c.head : Nat) + d, hBound⟩ b) := by
  dsimp only
  let P := gateConstCS b d
  let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
  obtain ⟨_, _, hAccept, _, _, hTape⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full d d d
      (le_refl _) (le_refl _) (fun _ _ => b) c hPhase hState hBound
  let post : Configuration (M := P.toPhased.toTM) n → Prop :=
    fun c' => c'.tape = c.write ⟨(c.head : Nat) + d, hBound⟩ b
  let spec : RunSpec P c post := RunSpec.mk
    (by
      intro s hs
      exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
        d d d (le_refl _) (le_refl _) (fun _ _ => b)
        c hPhase hState hBound s (by simpa [P] using hs) |>.2)
    (by simpa [P] using hAccept)
    (by simpa [P, post, gateConstCS_timeBound] using hTape)
  exact RunSpec.seqList_singleton P c post spec

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
