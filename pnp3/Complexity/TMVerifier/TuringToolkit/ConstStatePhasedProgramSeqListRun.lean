import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRun

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]

/-!
## Non-dependent runs of right-nested program lists

This module is the light list layer over `ConstStatePhasedProgramSeqRun`.
Recursive handoffs compare adjacent programs only.  The comparison is
essential: embedding through the next program truncates the previous tape at
the next program's tape length, so there is no corresponding theorem for
unrestricted lists.
-/

/-- Weaken the semantic postcondition of a `RunSpec`. -/
theorem RunSpec.imp
    {P : ConstStatePhasedProgram S} {n : Nat}
    {c : Configuration (M := P.toPhased.toTM) n}
    {Post Post' : Configuration (M := P.toPhased.toTM) n → Prop}
    (spec : RunSpec P c Post)
    (h : ∀ c', Post c' → Post' c') :
    RunSpec P c Post' :=
  ⟨spec.prefixSafe, spec.reachesAcceptPhase, h _ spec.postcondition⟩

/-- Lifting directly into a composite tail agrees with first lifting into its
head and then embedding.  The only size premise is the explicit comparison
between the adjacent programs `P1` and `P2`. -/
theorem liftP1ToSeq_eq_embedSeqConfig_lift
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
      embedSeqConfig P2 Ptail (liftP1ToP2 P1 P2 c1Final hHead2) := by
  dsimp only
  let h1Tail : P1.toPhased.toTM.tapeLength n ≤
      (seq P2 Ptail).toPhased.toTM.tapeLength n :=
    Nat.le_trans h12 (seq_tapeLength_ge_P1 P2 Ptail n)
  let hHead2 : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
    Nat.lt_of_lt_of_le c1Final.head.isLt h12
  let hHeadTail : c1Final.head.val <
      (seq P2 Ptail).toPhased.toTM.tapeLength n :=
    Nat.lt_of_lt_of_le c1Final.head.isLt h1Tail
  let cL := liftP1ToP2 P1 (seq P2 Ptail) c1Final hHeadTail
  let cR := embedSeqConfig P2 Ptail
    (liftP1ToP2 P1 P2 c1Final hHead2)
  have hs : cL.state = cR.state := by
    rfl
  have hh : cL.head = cR.head := by
    apply Fin.ext
    rfl
  have ht : cL.tape = cR.tape := by
    funext i
    dsimp only [cL, cR, liftP1ToP2, embedSeqConfig]
    by_cases h1 : i.val < P1.toPhased.toTM.tapeLength n
    · have h2 : i.val < P2.toPhased.toTM.tapeLength n :=
        Nat.lt_of_lt_of_le h1 h12
      simp only [dif_pos h1, dif_pos h2]
    ·
      by_cases h2 : i.val < P2.toPhased.toTM.tapeLength n
      · simp only [dif_neg h1, dif_pos h2]
      · simp only [dif_neg h1, dif_neg h2]
  change cL = cR
  cases hL : cL with
  | mk sL headL tapeL =>
    cases hR : cR with
    | mk sR headR tapeR =>
      rw [hL, hR] at hs hh ht
      change sL = sR at hs
      change headL = headR at hh
      change tapeL = tapeR at ht
      subst sR
      subst headR
      subst tapeR
      rfl

/-- Exact singleton terminal closure.  The final configuration is the actual
boundary step into the `idleCS` phase, rather than merely a configuration with
the same head and tape. -/
theorem RunSpec.seqList_singleton_exact [Inhabited S]
    (P : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := P.toPhased.toTM) n)
    (Post : Configuration (M := P.toPhased.toTM) n → Prop)
    (spec : RunSpec P c Post) :
    let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
    let cBoundary := TM.stepConfig
      (M := (ConstStatePhasedProgram.seq P idleCS).toPhased.toTM)
      (embedSeqConfig P idleCS cFinal)
    RunSpec (seqList [P]) (embedSeqConfig P idleCS c)
      (fun cSeq => cSeq = cBoundary ∧ Post cFinal) := by
  dsimp only
  let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
  let cBoundary := TM.stepConfig
    (M := (ConstStatePhasedProgram.seq P idleCS).toPhased.toTM)
    (embedSeqConfig P idleCS cFinal)
  have base := RunSpec.seqList_singleton P c Post spec
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
        cBoundary := by
    change TM.runConfig (M := (ConstStatePhasedProgram.seq P idleCS).toPhased.toTM)
        (embedSeqConfig P idleCS c) (P.timeBound n + 0 + 1) = _
    rw [Nat.add_zero, runConfig_succ, hPRun]
  exact ⟨base.prefixSafe, base.reachesAcceptPhase,
    hFinal, spec.postcondition⟩

/-- Add one program to a nonempty `seqList` tail.  The result preserves the
exact final composite configuration and both the head and tail postconditions.
The tape comparison is deliberately adjacent (`P` versus `Q`). -/
theorem RunSpec.seqList_cons [Inhabited S]
    (P Q : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S)) {n : Nat}
    (cP : Configuration (M := P.toPhased.toTM) n)
    (PostP : Configuration (M := P.toPhased.toTM) n → Prop)
    (PostTail : Configuration
      (M := (seqList (Q :: rest)).toPhased.toTM) n → Prop)
    (hPQ : P.toPhased.toTM.tapeLength n ≤ Q.toPhased.toTM.tapeLength n)
    (specP : RunSpec P cP PostP)
    (specTail :
      let cPFinal := TM.runConfig (M := P.toPhased.toTM) cP (P.timeBound n)
      let hHeadQ := Nat.lt_of_lt_of_le cPFinal.head.isLt hPQ
      let cQInit := liftP1ToP2 P Q cPFinal hHeadQ
      RunSpec (seqList (Q :: rest))
        (embedSeqConfig Q (seqList rest) cQInit) PostTail) :
    let cPFinal := TM.runConfig (M := P.toPhased.toTM) cP (P.timeBound n)
    let hPTail : P.toPhased.toTM.tapeLength n ≤
        (seqList (Q :: rest)).toPhased.toTM.tapeLength n :=
      Nat.le_trans hPQ (seq_tapeLength_ge_P1 Q (seqList rest) n)
    let hHeadTail := Nat.lt_of_lt_of_le cPFinal.head.isLt hPTail
    let cTailInit := liftP1ToP2 P (seqList (Q :: rest)) cPFinal hHeadTail
    let cTailFinal := TM.runConfig
      (M := (seqList (Q :: rest)).toPhased.toTM)
      cTailInit ((seqList (Q :: rest)).timeBound n)
    RunSpec (seqList (P :: Q :: rest))
      (embedSeqConfig P (seqList (Q :: rest)) cP) (fun cFinal =>
        cFinal = embedSeqP2Config P (seqList (Q :: rest)) cTailFinal ∧
        PostP cPFinal ∧ PostTail cTailFinal) := by
  dsimp only
  let cPFinal := TM.runConfig (M := P.toPhased.toTM) cP (P.timeBound n)
  let hPTail : P.toPhased.toTM.tapeLength n ≤
      (seqList (Q :: rest)).toPhased.toTM.tapeLength n :=
    Nat.le_trans hPQ (seq_tapeLength_ge_P1 Q (seqList rest) n)
  let hHeadTail := Nat.lt_of_lt_of_le cPFinal.head.isLt hPTail
  let cTailInit := liftP1ToP2 P (seqList (Q :: rest)) cPFinal hHeadTail
  have hBridge : cTailInit = embedSeqConfig Q (seqList rest)
      (liftP1ToP2 P Q cPFinal
        (Nat.lt_of_lt_of_le cPFinal.head.isLt hPQ)) := by
    exact liftP1ToSeq_eq_embedSeqConfig_lift P Q (seqList rest) cPFinal hPQ
  have specTail' : RunSpec (seqList (Q :: rest)) cTailInit PostTail := by
    rw [hBridge]
    exact specTail
  exact RunSpec.seq P (seqList (Q :: rest)) cP PostP PostTail
    hPTail specP specTail'

/-- A caller-selected readiness invariant for standalone program starts. -/
abbrev Ready (n : Nat) :=
  (P : ConstStatePhasedProgram S) →
    Configuration (M := P.toPhased.toTM) n → Prop

/-- One adjacent control-flow handoff: tape lengths are monotone and readiness
is preserved by the preceding standalone run and boundary lift. -/
def ReadyStep {n : Nat} (ready : Ready (S := S) n)
    (P Q : ConstStatePhasedProgram S) : Prop :=
  ∃ hPQ : P.toPhased.toTM.tapeLength n ≤ Q.toPhased.toTM.tapeLength n,
    ∀ c, ready P c →
      let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
      let hHead := Nat.lt_of_lt_of_le cFinal.head.isLt hPQ
      ready Q (liftP1ToP2 P Q cFinal hHead)

/-- Non-dependent driver for an arbitrary nonempty list.  Each element has a
standalone `RunSpec` whenever its readiness invariant holds, and `ReadyStep`
supplies exactly the adjacent handoffs.  The `True` postcondition is
intentional: semantic clients use `RunSpec.seqList_cons` when they need to
retain heterogeneous head/tail facts. -/
theorem RunSpec.seqList_of_forall [Inhabited S]
    {n : Nat} (ready : Ready (S := S) n)
    (P : ConstStatePhasedProgram S)
    (rest : List (ConstStatePhasedProgram S))
    (c : Configuration (M := P.toPhased.toTM) n)
    (hReady : ready P c)
    (hSpecs : List.Forall (fun Q => ∀ cQ, ready Q cQ →
      RunSpec Q cQ (fun _ => True)) (P :: rest))
    (hSteps : List.Chain' (ReadyStep ready) (P :: rest)) :
    RunSpec (seqList (P :: rest))
      (embedSeqConfig P (seqList rest) c) (fun _ => True) := by
  induction rest generalizing P with
  | nil =>
      rw [List.forall_cons] at hSpecs
      have specP := hSpecs.1 c hReady
      exact (RunSpec.seqList_singleton_exact P c (fun _ => True) specP).imp
        (fun _ _ => trivial)
  | cons Q tail ih =>
      rw [List.forall_cons] at hSpecs
      have hStep : ReadyStep ready P Q := hSteps.rel_head
      obtain ⟨hPQ, hReadyNext⟩ := hStep
      let cFinal := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
      let hHeadQ := Nat.lt_of_lt_of_le cFinal.head.isLt hPQ
      let cQInit := liftP1ToP2 P Q cFinal hHeadQ
      have specP := hSpecs.1 c hReady
      have tailSpec : RunSpec (seqList (Q :: tail))
          (embedSeqConfig Q (seqList tail) cQInit) (fun _ => True) :=
        ih Q cQInit (hReadyNext c hReady) hSpecs.2 hSteps.tail
      exact (RunSpec.seqList_cons P Q tail c (fun _ => True) (fun _ => True)
        hPQ specP tailSpec).imp (fun _ _ => trivial)

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
