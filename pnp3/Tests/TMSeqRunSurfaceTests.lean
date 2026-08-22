import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRunExamples
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRunExamples

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

/-- Pin weakening of a `RunSpec` postcondition. -/
theorem check_RunSpec_imp
    {P : ConstStatePhasedProgram S} {n : Nat}
    {c : Configuration (M := P.toPhased.toTM) n}
    {Post Post' : Configuration (M := P.toPhased.toTM) n → Prop}
    (spec : RunSpec P c Post)
    (h : ∀ c', Post c' → Post' c') :
    RunSpec P c Post' :=
  RunSpec.imp spec h

/-- Pin the adjacent-only lift/embed bridge used by list recursion. -/
theorem check_liftP1ToSeq_eq_embedSeqConfig_lift
    (P1 P2 Ptail : ConstStatePhasedProgram S) {n : Nat}
    (c1Final : Configuration (M := P1.toPhased.toTM) n)
    (h12 : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n) :
    let h1Tail : P1.toPhased.toTM.tapeLength n ≤
        (seq P2 Ptail).toPhased.toTM.tapeLength n :=
      Nat.le_trans h12 (seq_tapeLength_ge_P1 P2 Ptail n)
    let hHead2 : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt h12
    let hHeadTail : c1Final.head.val <
        (seq P2 Ptail).toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt h1Tail
    liftP1ToP2 P1 (seq P2 Ptail) c1Final hHeadTail =
      embedSeqConfig P2 Ptail (liftP1ToP2 P1 P2 c1Final hHead2) :=
  liftP1ToSeq_eq_embedSeqConfig_lift P1 P2 Ptail c1Final h12

/-- Pin the singleton's exact terminal boundary configuration. -/
theorem check_RunSpec_seqList_singleton_exact [Inhabited S]
    (P : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P.toPhased.toTM) n)
    (Post : Configuration (M := P.toPhased.toTM) n → Prop)
    (spec : RunSpec P c Post) :
    let cFinal := runConfig (M := P.toPhased.toTM) c (P.timeBound n)
    let cBoundary := stepConfig (M := (seq P idleCS).toPhased.toTM)
      (embedSeqConfig P idleCS cFinal)
    RunSpec (seqList [P]) (embedSeqConfig P idleCS c)
      (fun cSeq => cSeq = cBoundary ∧ Post cFinal) :=
  RunSpec.seqList_singleton_exact P c Post spec

/-- Pin the semantic cons combiner: exact final configuration and both
standalone head/tail postconditions, under adjacent monotonicity. -/
theorem check_RunSpec_seqList_cons [Inhabited S]
    (P Q : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S)) {n : Nat}
    (cP : Configuration (M := P.toPhased.toTM) n)
    (PostP : Configuration (M := P.toPhased.toTM) n → Prop)
    (PostTail : Configuration
      (M := (seqList (Q :: rest)).toPhased.toTM) n → Prop)
    (hPQ : P.toPhased.toTM.tapeLength n ≤ Q.toPhased.toTM.tapeLength n)
    (specP : RunSpec P cP PostP)
    (specTail :
      let cPFinal := runConfig (M := P.toPhased.toTM) cP (P.timeBound n)
      let hHeadQ := Nat.lt_of_lt_of_le cPFinal.head.isLt hPQ
      let cQInit := liftP1ToP2 P Q cPFinal hHeadQ
      RunSpec (seqList (Q :: rest))
        (embedSeqConfig Q (seqList rest) cQInit) PostTail) :
    let cPFinal := runConfig (M := P.toPhased.toTM) cP (P.timeBound n)
    let hPTail : P.toPhased.toTM.tapeLength n ≤
        (seqList (Q :: rest)).toPhased.toTM.tapeLength n :=
      Nat.le_trans hPQ (seq_tapeLength_ge_P1 Q (seqList rest) n)
    let hHeadTail := Nat.lt_of_lt_of_le cPFinal.head.isLt hPTail
    let cTailInit := liftP1ToP2 P (seqList (Q :: rest)) cPFinal hHeadTail
    let cTailFinal := runConfig
      (M := (seqList (Q :: rest)).toPhased.toTM)
      cTailInit ((seqList (Q :: rest)).timeBound n)
    RunSpec (seqList (P :: Q :: rest))
      (embedSeqConfig P (seqList (Q :: rest)) cP) (fun cFinal =>
        cFinal = embedSeqP2Config P (seqList (Q :: rest)) cTailFinal ∧
        PostP cPFinal ∧ PostTail cTailFinal) :=
  RunSpec.seqList_cons P Q rest cP PostP PostTail hPQ specP specTail

/-- Pin construction of one adjacent readiness edge. -/
theorem check_ReadyStep
    {n : Nat} (ready : Ready (S := S) n)
    (P Q : ConstStatePhasedProgram S)
    (hPQ : P.toPhased.toTM.tapeLength n ≤ Q.toPhased.toTM.tapeLength n)
    (hReady : ∀ c, ready P c →
      let cFinal := runConfig (M := P.toPhased.toTM) c (P.timeBound n)
      let hHead := Nat.lt_of_lt_of_le cFinal.head.isLt hPQ
      ready Q (liftP1ToP2 P Q cFinal hHead)) :
    ReadyStep ready P Q :=
  ⟨hPQ, hReady⟩

/-- Pin the arbitrary nonempty list driver and its intentionally payload-free
postcondition. -/
theorem check_RunSpec_seqList_of_forall [Inhabited S]
    {n : Nat} (ready : Ready (S := S) n)
    (P : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S))
    (c : Configuration (M := P.toPhased.toTM) n)
    (hReady : ready P c)
    (hSpecs : List.Forall (fun Q => ∀ cQ, ready Q cQ →
      RunSpec Q cQ (fun _ => True)) (P :: rest))
    (hSteps : List.Chain' (ReadyStep ready) (P :: rest)) :
    RunSpec (seqList (P :: rest))
      (embedSeqConfig P (seqList rest) c) (fun _ => True) :=
  RunSpec.seqList_of_forall ready P rest c hReady hSpecs hSteps

/-- Pin constant-gate tape-length monotonicity for arbitrary gate values,
destination offsets, and input length. -/
theorem check_gateConstCS_tapeLength_mono
    (b1 b2 : Bool) (d1 d2 n : Nat) (hD : d1 ≤ d2) :
    (gateConstCS b1 d1).toPhased.toTM.tapeLength n ≤
      (gateConstCS b2 d2).toPhased.toTM.tapeLength n :=
  gateConstCS_tapeLength_mono b1 b2 d1 d2 n hD

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
    let hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n :=
      gateConstCS_tapeLength_mono b1 b2 d1 d2 n hD
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

/-- Pin the concrete two-gate `seqList` result that exercises both the
adjacent bridge and the exact singleton terminal step. -/
theorem check_gateConstCS_seqList_two_runSpec
    (b1 b2 : Bool) (d1 d2 : Nat) (hD : d1 ≤ d2) {n : Nat}
    (c1 : Configuration (M := (gateConstCS b1 d1).toPhased.toTM) n)
    (hPhase : c1.state.fst.val = 0)
    (hState : c1.state.snd = (false, false))
    (hBound1 : (c1.head : Nat) + d1 <
      (gateConstCS b1 d1).toPhased.toTM.tapeLength n) :
    let P1 := gateConstCS b1 d1
    let P2 := gateConstCS b2 d2
    let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n :=
      gateConstCS_tapeLength_mono b1 b2 d1 d2 n hD
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
    let c2Final := runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    let c2Boundary := stepConfig (M := (seq P2 idleCS).toPhased.toTM)
      (embedSeqConfig P2 idleCS c2Final)
    RunSpec (seqList [P1, P2])
      (embedSeqConfig P1 (seqList [P2]) c1) (fun cSeq =>
        cSeq = embedSeqP2Config P1 (seqList [P2]) c2Boundary ∧
        c1Final.tape = c1.write ⟨(c1.head : Nat) + d1, hBound1⟩ b1 ∧
        c2Final.tape = c2Init.write ⟨(c2Init.head : Nat) + d2, hBound2⟩ b2) :=
  gateConstCS_seqList_two_runSpec b1 b2 d1 d2 hD c1 hPhase hState hBound1

/-- Pin the direct full-run corollary, including the exact boundary
configuration and both standalone tape-write equations. -/
theorem check_gateConstCS_seqList_two_run_full
    (b1 b2 : Bool) (d1 d2 : Nat) (hD : d1 ≤ d2) {n : Nat}
    (c1 : Configuration (M := (gateConstCS b1 d1).toPhased.toTM) n)
    (hPhase : c1.state.fst.val = 0)
    (hState : c1.state.snd = (false, false))
    (hBound1 : (c1.head : Nat) + d1 <
      (gateConstCS b1 d1).toPhased.toTM.tapeLength n) :
    let P1 := gateConstCS b1 d1
    let P2 := gateConstCS b2 d2
    let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n :=
      gateConstCS_tapeLength_mono b1 b2 d1 d2 n hD
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
    let c2Final := runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    let c2Boundary := stepConfig (M := (seq P2 idleCS).toPhased.toTM)
      (embedSeqConfig P2 idleCS c2Final)
    let cSeqFinal := runConfig (M := (seqList [P1, P2]).toPhased.toTM)
      (embedSeqConfig P1 (seqList [P2]) c1) ((seqList [P1, P2]).timeBound n)
    cSeqFinal = embedSeqP2Config P1 (seqList [P2]) c2Boundary ∧
    c1Final.tape = c1.write ⟨(c1.head : Nat) + d1, hBound1⟩ b1 ∧
    c2Final.tape = c2Init.write ⟨(c2Init.head : Nat) + d2, hBound2⟩ b2 :=
  gateConstCS_seqList_two_run_full
    b1 b2 d1 d2 hD c1 hPhase hState hBound1

/-- Pin the three-gate recursion probe and all three dependent standalone
specification inputs. -/
theorem check_gateConstCS_seqList_three_recursion_probe
    (b1 b2 b3 : Bool) (d1 d2 d3 : Nat)
    (h12 : d1 ≤ d2) (h23 : d2 ≤ d3) {n : Nat}
    (c1 : Configuration (M := (gateConstCS b1 d1).toPhased.toTM) n)
    (spec1 : RunSpec (gateConstCS b1 d1) c1 (fun _ => True))
    (spec2 :
      let P1 := gateConstCS b1 d1
      let P2 := gateConstCS b2 d2
      let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hLen12 : P1.toPhased.toTM.tapeLength n ≤
          P2.toPhased.toTM.tapeLength n :=
        gateConstCS_tapeLength_mono b1 b2 d1 d2 n h12
      let hHead2 := Nat.lt_of_lt_of_le c1Final.head.isLt hLen12
      RunSpec P2 (liftP1ToP2 P1 P2 c1Final hHead2) (fun _ => True))
    (spec3 :
      let P1 := gateConstCS b1 d1
      let P2 := gateConstCS b2 d2
      let P3 := gateConstCS b3 d3
      let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hLen12 : P1.toPhased.toTM.tapeLength n ≤
          P2.toPhased.toTM.tapeLength n :=
        gateConstCS_tapeLength_mono b1 b2 d1 d2 n h12
      let hHead2 := Nat.lt_of_lt_of_le c1Final.head.isLt hLen12
      let c2Init := liftP1ToP2 P1 P2 c1Final hHead2
      let c2Final := runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
      let hLen23 : P2.toPhased.toTM.tapeLength n ≤
          P3.toPhased.toTM.tapeLength n :=
        gateConstCS_tapeLength_mono b2 b3 d2 d3 n h23
      let hHead3 := Nat.lt_of_lt_of_le c2Final.head.isLt hLen23
      RunSpec P3 (liftP1ToP2 P2 P3 c2Final hHead3) (fun _ => True)) :
    let P1 := gateConstCS b1 d1
    let P2 := gateConstCS b2 d2
    let P3 := gateConstCS b3 d3
    RunSpec (seqList [P1, P2, P3])
      (embedSeqConfig P1 (seqList [P2, P3]) c1) (fun _ => True) :=
  gateConstCS_seqList_three_recursion_probe
    b1 b2 b3 d1 d2 d3 h12 h23 c1 spec1 spec2 spec3

/-- Pin the explicit readiness predicate used by the homogeneous-list
instantiation. -/
theorem check_gateConstCSReady
    (b : Bool) (d n : Nat)
    (P : ConstStatePhasedProgram (Bool × Bool))
    (c : Configuration (M := P.toPhased.toTM) n) :
    gateConstCSReady b d n P c ↔
      P = gateConstCS b d ∧
      c.state.fst.val = 0 ∧
      c.state.snd = (false, false) ∧
      (c.head : Nat) + d < P.toPhased.toTM.tapeLength n :=
  Iff.rfl

/-- Pin the concrete arbitrary-length, homogeneous same-offset use of the
phase-only list driver. -/
theorem check_gateConstCS_seqList_replicate_runSpec
    (b : Bool) (d copies : Nat) {n : Nat}
    (c : Configuration (M := (gateConstCS b d).toPhased.toTM) n)
    (hPhase : c.state.fst.val = 0)
    (hState : c.state.snd = (false, false))
    (hBound : (c.head : Nat) + d <
      (gateConstCS b d).toPhased.toTM.tapeLength n) :
    let P := gateConstCS b d
    RunSpec (seqList (P :: List.replicate copies P))
      (embedSeqConfig P (seqList (List.replicate copies P)) c)
      (fun _ => True) :=
  gateConstCS_seqList_replicate_runSpec b d copies c hPhase hState hBound

end Pnp3.Tests.TMSeqRunSurface
