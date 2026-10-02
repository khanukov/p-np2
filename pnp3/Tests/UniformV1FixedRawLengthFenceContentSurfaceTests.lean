import Complexity.Uniform.V1.FixedRawLengthFenceOverflowWitness

/-! G3s Infrastructure. Full public propositions, raw empty/mixed pairs, and
phase-local boundary probes. The last probes supply countdown configurations;
they are separate from the closed raw-input overflow capstone. -/
namespace Pnp3.Tests.UniformV1FixedRawLengthFenceContentSurfaceTests
open Complexity.Uniform.V1 Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedRawLengthFence
set_option maxRecDepth 40000
set_option maxHeartbeats 800000

theorem check_run_update_of_unvisited
    (M : UniformTM) {n B : Nat} (c : Config M.stateCount n B)
    (p : Fin (tapeLength n B)) (b : Option Bool) (T : Nat)
    (havoid : ∀ t, t < T → (M.run t c).head ≠ p) :
    M.run T {c with tape := Function.update c.tape p b} =
      {(M.run T c) with tape := Function.update (M.run T c).tape p b} :=
  M.run_update_of_unvisited c p b T havoid

theorem check_raw_fenced_content_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2 * pairLength a m + 2 ≤ B) :
    prefixed.run (installClock (pairLength a m) + contentClock a m)
        (initialConfig prefixed B (encodePair x w)) =
      ⟨⟨109, by decide⟩, ⟨a+m, by simp only [tapeLength,pairLength]; omega⟩,
        fencedContentTape B x w⟩ :=
  raw_fenced_content_exact x w hroom

theorem check_raw_fenced_content_trace {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : 2 * pairLength a m + 2 ≤ B) :
    ∀ t, t ≤ contentClock a m →
      let c := prefixed.run (installClock (pairLength a m)+t)
        (initialConfig prefixed B (encodePair x w))
      c.head.val ≤ pairLength a m+1 ∧
      c.tape ⟨fencePos (pairLength a m), by dsimp [fencePos,tapeLength]; omega⟩ = some false ∧
      c.state ≠ prefixed.accept ∧ c.state ≠ prefixed.reject :=
  raw_fenced_content_trace x w hroom

theorem check_content_prefix_resources (a m : Nat) :
    2 * pairLength a m + 2 ≤ allocation (pairLength a m) ∧
    installClock (pairLength a m) + contentClock a m ≤ allocation (pairLength a m) :=
  content_prefix_resources a m

theorem check_overflow_values :
    FixedContentTagGate.tagMatches (Fin.append overflowX overflowW) = true ∧
    FixedContentGammaTerminator.gammaZeros? (Fin.append overflowX overflowW) = some 5 ∧
    FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt
      45 overflowX overflowW 21 FixedGammaPayloadDispatcher.qHasOne ∧
    FixedGammaTargetRegisterDecrement.borrow overflowX overflowW 5 = 0 ∧
    (∀ j, j ≤ 5 → (62 : Nat).testBit (5-j) =
      FixedGammaTargetRegisterDecrement.decBit overflowX overflowW 5 0 j) ∧
    (∀ b, 5 < b → (62 : Nat).testBit b = false) :=
  overflow_values

theorem check_overflow_h17_exact : prefixed.run 2335
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨⟨245, by decide⟩, ⟨25, by decide⟩, overflowTape 62 0⟩ :=
  overflow_h17_exact

theorem check_overflow_prereject_exact : prefixed.run 4442
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨⟨251,by decide⟩,⟨65,by decide⟩,overflowTape 23 38⟩ :=
  overflow_prereject_exact

theorem check_overflow_reject_row : prefixed.step ⟨251,by decide⟩ (some false) =
    (prefixed.reject,some false,Move.stay) :=
  overflow_reject_row

theorem check_overflow_reject_exact (s : Nat) : prefixed.run (4443+s)
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨prefixed.reject,⟨65,by decide⟩,overflowTape 23 38⟩ :=
  overflow_reject_exact s

theorem check_overflow_fence_trace : ∀ t, t ≤ 2926 →
    let c := prefixed.run (1517+t)
      (initialConfig prefixed 45 (encodePair overflowX overflowW))
    c.head.val ≤ 65 ∧ c.tape ⟨65,by decide⟩ = some false :=
  overflow_fence_trace

/-- Discharge the generic capstone's sole resource premise at the fixed allocation. -/
theorem check_allocated_content {a m : Nat} (x : Bitstring a) (w : Bitstring m) :
    prefixed.run (installClock (pairLength a m)+contentClock a m)
      (initialConfig prefixed (allocation (pairLength a m)) (encodePair x w)) =
        ⟨⟨109,by decide⟩,⟨a+m,by simp only [tapeLength,pairLength]; omega⟩,
          fencedContentTape (allocation (pairLength a m)) x w⟩ :=
  raw_fenced_content_exact x w (content_prefix_resources a m).1

private def snapshot {k n B : Nat} (c : Config k n B) :=
  (c.state.val,c.head.val,List.ofFn c.tape)
private theorem of_snapshot {k n B : Nat} {c d : Config k n B}
    (h : snapshot c = snapshot d) : c = d :=
  Config.ext_parts (Fin.ext (congrArg Prod.fst h))
    (Fin.ext (congrArg (fun x => x.2.1) h))
    (List.ofFn_injective (congrArg (fun x => x.2.2) h))

/-- Independent kernel execution: the empty pair has raw length one, not zero. -/
theorem check_empty_pair : prefixed.run 40
    (initialConfig prefixed 4 (encodePair (![] : Bitstring 0) (![] : Bitstring 0))) =
      ⟨⟨109,by decide⟩,⟨0,by decide⟩,fun i => if i.val = 5 then some false else none⟩ :=
  of_snapshot (by decide)

/-- Theorem-derived mixed pair; compaction retains raw-length configuration indices. -/
theorem check_mixed_pair : prefixed.run 241
    (initialConfig prefixed 12 (encodePair (![true] : Bitstring 1) (![false,true] : Bitstring 2))) =
      ⟨⟨109,by decide⟩,⟨3,by decide⟩,
        fun i => if i.val = 0 ∨ i.val = 2 then some true
          else if i.val = 1 ∨ i.val = 17 then some false else none⟩ := by
  have h := raw_fenced_content_exact (B := 12) (![true] : Bitstring 1)
    (![false,true] : Bitstring 2) (by decide)
  change prefixed.run 241 _ = _ at h
  rw [h]
  apply of_snapshot
  decide

/-- Concrete word, clocks, capacity and rejecting tape; no parser identification. -/
theorem check_witness_layout :
    List.ofFn (encodePair overflowX overflowW) =
      [false,true,true,false,true,true,false,false,true,false,false,false,false,false,false,true,true,true,true,true,true] ∧
    contentClock 1 18 = 484 ∧ installClock 21 = 1517 ∧ fencePos 21 = 65 ∧
    65-(19+3+5) = 38 ∧
    (List.ofFn (overflowTape 23 38)).drop 20 =
      [some false,some true,some false,some true,some true,some true,none] ++
        List.replicate 38 (some true) ++ [some false,none] := by decide

private def loopEntry (v r : Nat) : Config FixedGammaTargetUnaryCountdown.stateCount 21 45 :=
  ⟨FixedGammaTargetUnaryCountdown.qLoop,⟨26,by decide⟩,overflowTape v r⟩

/-- Phase-local tests of the strict boundary: use the last available mark, exhaust
at a full lane, or attempt one additional mark. These are not raw-input theorems. -/
theorem check_countdown_boundary :
    FixedGammaTargetUnaryCountdown.machine.run 91 (loopEntry 1 37) = loopEntry 0 38 ∧
    FixedGammaTargetUnaryCountdown.machine.run 15 (loopEntry 0 38) =
      ⟨FixedGammaTargetUnaryCountdown.qDone,⟨26,by decide⟩,overflowTape 0 38⟩ ∧
    FixedGammaTargetUnaryCountdown.machine.run 53 (loopEntry 1 38) =
      ⟨FixedGammaTargetUnaryCountdown.qRunEnd,⟨65,by decide⟩,overflowTape 0 38⟩ ∧
    FixedGammaTargetUnaryCountdown.machine.run 54 (loopEntry 1 38) =
      ⟨FixedGammaTargetUnaryCountdown.qReject,⟨65,by decide⟩,overflowTape 0 38⟩ := by
  repeat' apply And.intro
  all_goals apply of_snapshot; decide

end Pnp3.Tests.UniformV1FixedRawLengthFenceContentSurfaceTests
