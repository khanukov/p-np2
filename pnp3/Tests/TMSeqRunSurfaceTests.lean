import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRun

namespace Pnp3.Tests.TMSeqRunSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.GateEvalCS

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]

/-- Pin the `RunSpec` constructor fields and their order. -/
theorem check_RunSpec_mk
    (P : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P.toPhased.toTM) n)
    (Post : Configuration (M := P.toPhased.toTM) n → Prop)
    (hPrefix : ∀ s < P.timeBound n,
      let c_s := runConfig (M := P.toPhased.toTM) c s
      c_s.state.fst.val ≠ P.acceptPhase.val ∧
      ((P.toPhased.toTM.step c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
        c_s.head.val + 1 < P.toPhased.toTM.tapeLength n))
    (hReach :
      (runConfig (M := P.toPhased.toTM) c (P.timeBound n)).state.fst.val =
        P.acceptPhase.val)
    (hPost : Post (runConfig (M := P.toPhased.toTM) c (P.timeBound n))) :
    RunSpec P c Post :=
  RunSpec.mk hPrefix hReach hPost

/-- Pin the three public `RunSpec` projections. -/
theorem check_RunSpec_projections
    (P : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P.toPhased.toTM) n)
    (Post : Configuration (M := P.toPhased.toTM) n → Prop)
    (spec : RunSpec P c Post) :
    (∀ s < P.timeBound n,
      let c_s := runConfig (M := P.toPhased.toTM) c s
      c_s.state.fst.val ≠ P.acceptPhase.val ∧
      ((P.toPhased.toTM.step c_s.state (c_s.tape c_s.head)).snd.snd = Move.right →
        c_s.head.val + 1 < P.toPhased.toTM.tapeLength n)) ∧
    (runConfig (M := P.toPhased.toTM) c
        (P.timeBound n)).state.fst.val = P.acceptPhase.val ∧
    Post (runConfig (M := P.toPhased.toTM) c (P.timeBound n)) :=
  ⟨spec.prefixSafe, spec.reachesAcceptPhase, spec.postcondition⟩

/-- Pin the exact boundary-handoff theorem signature, including its single
tape-length comparison and derived lift head bound. -/
theorem check_seq_boundary_step_eq_embedSeqP2Config_lift
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c1Final : Configuration (M := P1.toPhased.toTM) n)
    (hAcceptPhase : c1Final.state.fst.val = P1.acceptPhase.val)
    (hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n) :
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    stepConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c1Final) =
      embedSeqP2Config P1 P2 (liftP1ToP2 P1 P2 c1Final hHead) :=
  seq_boundary_step_eq_embedSeqP2Config_lift P1 P2 c1Final hAcceptPhase hLen

/-- Pin the reusable two-program theorem's configuration flow and semantic
postcondition surface. -/
theorem check_seq_run_full
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c1 : Configuration (M := P1.toPhased.toTM) n)
    (Post1 : Configuration (M := P1.toPhased.toTM) n → Prop)
    (Post2 : Configuration (M := P2.toPhased.toTM) n → Prop)
    (hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n)
    (spec1 : RunSpec P1 c1 Post1)
    (spec2 :
      let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
        Nat.lt_of_lt_of_le c1Final.head.isLt hLen
      RunSpec P2 (liftP1ToP2 P1 P2 c1Final hHead) Post2) :
    let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    let c2Init := liftP1ToP2 P1 P2 c1Final hHead
    let c2Final := runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    runConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c1) ((seq P1 P2).timeBound n) =
      embedSeqP2Config P1 P2 c2Final ∧
    Post1 c1Final ∧ Post2 c2Final :=
  seq_run_full P1 P2 c1 Post1 Post2 hLen spec1 spec2

/-- Pin the induction-facing closure theorem and its honest composite
postcondition: exact final configuration plus both component postconditions. -/
theorem check_RunSpec_seq
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c1 : Configuration (M := P1.toPhased.toTM) n)
    (Post1 : Configuration (M := P1.toPhased.toTM) n → Prop)
    (Post2 : Configuration (M := P2.toPhased.toTM) n → Prop)
    (hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n)
    (spec1 : RunSpec P1 c1 Post1)
    (spec2 :
      let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
        Nat.lt_of_lt_of_le c1Final.head.isLt hLen
      RunSpec P2 (liftP1ToP2 P1 P2 c1Final hHead) Post2) :
    let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    let c2Init := liftP1ToP2 P1 P2 c1Final hHead
    let c2Final := runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    RunSpec (seq P1 P2) (embedSeqConfig P1 P2 c1) (fun c =>
      c = embedSeqP2Config P1 P2 c2Final ∧
      Post1 c1Final ∧ Post2 c2Final) :=
  RunSpec.seq P1 P2 c1 Post1 Post2 hLen spec1 spec2

/-- Pin the honest singleton terminal closure.  Its result is a `RunSpec` for
the actual `seqList [P]`, and its postcondition preserves the embedded P1
final head and tape without constructing a standalone idle configuration. -/
theorem check_RunSpec_seqList_singleton [Inhabited S]
    (P : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P.toPhased.toTM) n)
    (Post : Configuration (M := P.toPhased.toTM) n → Prop)
    (spec : RunSpec P c Post) :
    let cFinal := runConfig (M := P.toPhased.toTM) c (P.timeBound n)
    RunSpec (seqList [P]) (embedSeqConfig P idleCS c) (fun cSeq =>
      cSeq.head = (embedSeqConfig P idleCS cFinal).head ∧
      cSeq.tape = (embedSeqConfig P idleCS cFinal).tape ∧
      Post cFinal) :=
  RunSpec.seqList_singleton P c Post spec

/-- Pin a concrete compiling `RunSpec` surface for a singleton constant-gate
`seqList`, including its tape-write meaning. -/
theorem check_gateConstCS_seqList_singleton_runSpec
    (b : Bool) (d : Nat) {n : Nat}
    (c : Configuration (M := (gateConstCS b d).toPhased.toTM) n)
    (hPhase : c.state.fst.val = 0)
    (hState : c.state.snd = (false, false))
    (hBound : (c.head : Nat) + d <
      (gateConstCS b d).toPhased.toTM.tapeLength n) :
    let P := gateConstCS b d
    let cFinal := runConfig (M := P.toPhased.toTM) c (P.timeBound n)
    RunSpec (seqList [P]) (embedSeqConfig P idleCS c) (fun cSeq =>
      cSeq.head = (embedSeqConfig P idleCS cFinal).head ∧
      cSeq.tape = (embedSeqConfig P idleCS cFinal).tape ∧
      cFinal.tape = c.write ⟨(c.head : Nat) + d, hBound⟩ b) :=
  gateConstCS_seqList_singleton_runSpec b d c hPhase hState hBound

/-- Pin the concrete theorem's full result type.  It needs only the first
gate's tape bound; the second follows from ordered destinations.  Its second
write postcondition is deliberately relative to the P1-to-P2 boundary lift. -/
theorem check_gateConstCS_seq_run_full
    (b1 b2 : Bool) (d1 d2 : Nat) (hD : d1 ≤ d2) {n : Nat}
    (c1 : Configuration (M := (gateConstCS b1 d1).toPhased.toTM) n)
    (hPhase : c1.state.fst.val = 0)
    (hState : c1.state.snd = (false, false))
    (hBound1 : (c1.head : Nat) + d1 <
      (gateConstCS b1 d1).toPhased.toTM.tapeLength n) :
    let P1 := gateConstCS b1 d1
    let P2 := gateConstCS b2 d2
    let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n := by
      show n + (2 * d1 + 3) + 1 ≤ n + (2 * d2 + 3) + 1
      omega
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    let c2Init := liftP1ToP2 P1 P2 c1Final hHead
    let c2Final := runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    runConfig (M := (seq P1 P2).toPhased.toTM)
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
        omega⟩ b2 :=
  gateConstCS_seq_run_full b1 b2 d1 d2 hD c1 hPhase hState hBound1

end Pnp3.Tests.TMSeqRunSurface
