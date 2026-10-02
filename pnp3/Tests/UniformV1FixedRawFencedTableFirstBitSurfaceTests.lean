import Complexity.Uniform.V1.FixedRawFencedTableFirstBit
import Tests.UniformV1FixedRawLengthFenceCountdownSurfaceTests

/-! G3v Infrastructure: full proposition pins, independent rows and exact execution. -/
namespace Pnp3.Tests.UniformV1FixedRawFencedTableFirstBitSurfaceTests
open Complexity.Uniform.V1 Complexity.Uniform.V1.PairEncoding Complexity.Uniform.V1.FixedRawLengthFence
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedRawFencedTableFirstBit

open FixedGammaTargetUnaryCountdown in
theorem check_exhaust_preterminal {a m B z r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a+m+2+z < tapeLength (pairLength a m) B)
    (c : Config FixedGammaTargetUnaryCountdown.stateCount (pairLength a m) B) (hq : c.state = FixedGammaTargetUnaryCountdown.qLoop)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = FixedGammaTargetUnaryCountdown.loopTape B x w z 0 r) :
    let e := FixedGammaTargetUnaryCountdown.machine.run (FixedGammaTargetUnaryCountdown.zeroClock z-1) c
    e.state = FixedGammaTargetUnaryCountdown.qFin ∧ e.head.val = a+m+2+z ∧ e.tape = FixedGammaTargetUnaryCountdown.loopTape B x w z 0 r :=
  FixedGammaTargetUnaryCountdown.exhaust_preterminal x w hroom c hq hh ht

open FixedRawLengthFence in
theorem check_raw_fenced_countdown_success_strict {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z) (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false) (hcap : v ≤ capacity a m z) :
    ∀ t, t < countdownSuccessClock a m z C (borrow x w z) v →
      (prefixed.run t (initialConfig prefixed B (encodePair x w))).state ≠ prefixed.accept ∧
      (prefixed.run t (initialConfig prefixed B (encodePair x w))).state ≠ prefixed.reject :=
  FixedRawLengthFence.raw_fenced_countdown_success_strict x w hr htag hg hz hfirst hv hhigh hcap

open FixedRawFencedTableFirstBit in
theorem check_table_and_resource_pins :
    suffix.stateCount = 11 ∧ Fintype.card (Fin suffix.stateCount × Option Bool) = 33 ∧
    suffix.start = qStart ∧ suffix.accept = qDone ∧ suffix.reject = qReject ∧
    suffix.rawStep = raw ∧ FixedRawFencedTableFirstBit.machine = FixedRawLengthFence.prefixed.seq suffix ∧
    FixedRawFencedTableFirstBit.machine.stateCount = 267 ∧ FixedRawFencedTableFirstBit.machine.accept.val = 265 ∧ FixedRawFencedTableFirstBit.machine.reject.val = 266 :=
  FixedRawFencedTableFirstBit.table_and_resource_pins

open FixedRawFencedTableFirstBit in
theorem check_seek_first_exact {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z) (htrail : 9+z < a+m)
    (c : Config suffix.stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = countdownTape B x w z 0 v) :
    let e := suffix.run (cursorClock a m z) c
    (e = ⟨qRead,⟨sourceCursor a m z,by have h := Nat.min_le_left (a+m) (sourceOffset z); simp only [sourceCursor,tapeLength,pairLength] at *; omega⟩,
      countdownTape B x w z 0 v⟩) ∧
    e.tape e.head = FixedContentTagGate.physicalSymbol (Fin.append x w) (sourceOffset z) :=
  FixedRawFencedTableFirstBit.seek_first_exact x w hr hg hz htrail c hq hh ht

open FixedRawFencedTableFirstBit in
theorem check_copy_first_exact {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z) (htrail : 9+z < a+m)
    (c : Config suffix.stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a+m+2+z) (ht : c.tape = countdownTape B x w z 0 v) (s : Nat) :
    suffix.run (copyClock a m z+s) c =
      ⟨suffix.accept,⟨a+m+1,by simp only [tapeLength,pairLength]; omega⟩,outputTape B x w z v (sourceBit x w z)⟩ :=
  FixedRawFencedTableFirstBit.copy_first_exact x w hr hg hz htrail c hq hh ht s

open FixedRawFencedTableFirstBit in
theorem check_raw_first_bit_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false)
    (hcap : v ≤ capacity a m z) (htrail : 9+z < a+m) (s : Nat) :
    FixedRawFencedTableFirstBit.machine.run (rawClock a m z C (borrow x w z) v+s)
      (initialConfig FixedRawFencedTableFirstBit.machine B (encodePair x w)) =
      ⟨FixedRawFencedTableFirstBit.machine.accept, ⟨a+m+1, by simp only [tapeLength, pairLength]; omega⟩,
        outputTape B x w z v (sourceBit x w z)⟩ :=
  FixedRawFencedTableFirstBit.raw_first_bit_exact x w hr htag hg hz hfirst hv hhigh hcap htrail s

open FixedRawFencedTableFirstBit in
theorem check_raw_overflow_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false)
    (hover : capacity a m z < v) (s : Nat) :
    FixedRawFencedTableFirstBit.machine.run (countdownRejectClock a m z C (borrow x w z)+s)
      (initialConfig FixedRawFencedTableFirstBit.machine B (encodePair x w)) =
      ⟨FixedRawFencedTableFirstBit.machine.reject,
        ⟨fencePos (pairLength a m), by
          simp only [fencePos, tapeLength] at *; omega⟩,
        countdownTape B x w z (v-capacity a m z-1) (capacity a m z)⟩ :=
  FixedRawFencedTableFirstBit.raw_overflow_exact x w hr htag hg hz hfirst hv hhigh hover s

open FixedRawFencedTableFirstBit in
theorem check_raw_clock_bound {a m z C d v : Nat}
    (hw : 9+z ≤ a+m) (hz : 2 ≤ z) (hd : d ≤ z)
    (hC : C ≤ 2*(a+m)*(a+m)) (hv : v ≤ capacity a m z) :
    rawClock a m z C d v ≤ deadline (pairLength a m) ∧
    countdownRejectClock a m z C d ≤ deadline (pairLength a m) ∧
    allocation (pairLength a m) ≤ deadline (pairLength a m) :=
  FixedRawFencedTableFirstBit.raw_clock_bound hw hz hd hC hv

theorem check_all_rows :
    suffix.step qStart (none) = (qRegL,none,Move.left) ∧
    suffix.step qStart (some false) = (qReject,some false,Move.stay) ∧
    suffix.step qStart (some true) = (qReject,some true,Move.stay) ∧
    suffix.step qRegL (none) = (qContentL,none,Move.left) ∧
    suffix.step qRegL (some false) = (qRegL,some false,Move.left) ∧
    suffix.step qRegL (some true) = (qReject,some true,Move.stay) ∧
    suffix.step qContentL (none) = (qOnTerm,none,Move.right) ∧
    suffix.step qContentL (some false) = (qContentL,some false,Move.left) ∧
    suffix.step qContentL (some true) = (qContentL,some true,Move.left) ∧
    suffix.step qOnTerm (none) = (qReject,none,Move.stay) ∧
    suffix.step qOnTerm (some false) = (qReject,some false,Move.stay) ∧
    suffix.step qOnTerm (some true) = (qRead,some true,Move.right) ∧
    suffix.step qRead (none) = (qWriteFalse,none,Move.right) ∧
    suffix.step qRead (some false) = (qSeekFalse,some false,Move.right) ∧
    suffix.step qRead (some true) = (qSeekTrue,some true,Move.right) ∧
    suffix.step qSeekFalse (none) = (qWriteFalse,none,Move.right) ∧
    suffix.step qSeekFalse (some false) = (qSeekFalse,some false,Move.right) ∧
    suffix.step qSeekFalse (some true) = (qSeekFalse,some true,Move.right) ∧
    suffix.step qSeekTrue (none) = (qWriteTrue,none,Move.right) ∧
    suffix.step qSeekTrue (some false) = (qSeekTrue,some false,Move.right) ∧
    suffix.step qSeekTrue (some true) = (qSeekTrue,some true,Move.right) ∧
    suffix.step qWriteFalse (none) = (qReject,none,Move.stay) ∧
    suffix.step qWriteFalse (some false) = (qDone,some false,Move.stay) ∧
    suffix.step qWriteFalse (some true) = (qReject,some true,Move.stay) ∧
    suffix.step qWriteTrue (none) = (qReject,none,Move.stay) ∧
    suffix.step qWriteTrue (some false) = (qDone,some true,Move.stay) ∧
    suffix.step qWriteTrue (some true) = (qReject,some true,Move.stay) ∧
    suffix.step qDone (none) = (qDone,none,Move.stay) ∧
    suffix.step qDone (some false) = (qDone,some false,Move.stay) ∧
    suffix.step qDone (some true) = (qDone,some true,Move.stay) ∧
    suffix.step qReject (none) = (qReject,none,Move.stay) ∧
    suffix.step qReject (some false) = (qReject,some false,Move.stay) ∧
    suffix.step qReject (some true) = (qReject,some true,Move.stay) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def probeWord (L : Nat) : Bitstring L := fun i => decide (i.val ∈ [0,2,3,6,10])
private def empty : Bitstring 0 := Fin.elim0
private def probeC : Nat := FixedGammaPayloadDispatcherRounds.pendingEndClock 2 1
theorem check_raw_minimal_virtual : FixedRawFencedTableFirstBit.machine.run (countdownSuccessClock 0 12 2 probeC 2 3+10)
    (initialConfig FixedRawFencedTableFirstBit.machine 28 (encodePair empty (probeWord 12))) =
    ⟨FixedRawFencedTableFirstBit.machine.accept,⟨13,by decide⟩,outputTape 28 empty (probeWord 12) 2 3 false⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.pending_virtual_strict_first_terminal
    (B := 28) (zeros := 2) (k := 1) empty (probeWord 12) (by decide) (by decide)
    (by decide) (by decide) (by intro j hj hj'; interval_cases j; decide) (by decide)).1
  have hv : ∀ j, j ≤ 2 → (3:Nat).testBit (2-j) = FixedGammaTargetRegisterDecrement.decBit empty (probeWord 12) 2 2 j := by
    intro j hj; interval_cases j <;> decide
  have hh : ∀ b, 2 < b → (3:Nat).testBit b = false := by
    intro b hb; exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 3 < 2^3) (Nat.pow_le_pow_right (by decide) (by omega)))
  have he := raw_fenced_countdown_success_exact empty (probeWord 12) (by decide) (by decide) (by decide) (by decide) hf hv hh (by decide) 0
  have hs := raw_fenced_countdown_success_strict empty (probeWord 12) (by decide) (by decide) (by decide) (by decide) hf hv hh (by decide)
  simp only [Nat.add_zero, show FixedGammaTargetRegisterDecrement.borrow empty (probeWord 12) 2 = 2 from by decide] at he hs
  unfold probeC
  rw [FixedRawFencedTableFirstBit.machine,UniformTM.seq_initialConfig,UniformTM.seq_handoff prefixed suffix _ (fun t ht => (hs t ht).1) (congrArg Config.state he)]
  rw [he]
  let c : Config 11 (pairLength 0 12) 28 := ⟨qStart,⟨16,by decide⟩,countdownTape 28 empty (probeWord 12) 2 0 3⟩
  change prefixed.seqEmbedRight suffix (suffix.run 10 c) = _
  have hc := copy_first_exact (z := 2) (v := 3) empty (probeWord 12) (by decide) (by decide) (by decide) (by decide) c rfl rfl rfl 0
  change suffix.run 10 c = _ at hc
  rw [hc]; rfl

/-- Materialization changes representation only, never the underlying run. -/
private def materialize {k n B : Nat} (c : Config k n B) : Config k n B :=
  let cells := Array.ofFn c.tape
  {c with tape := fun i => cells[i.val]'(by simp [cells])}
private theorem materialize_eq {k n B : Nat} (c : Config k n B) : materialize c = c := by
  apply Config.ext_parts (by rfl) (by rfl); funext i; simp [materialize]
private def compactRun (M : UniformTM) {n B : Nat} : Nat → Config M.stateCount n B → Config M.stateCount n B
  | 0,c => c
  | t+1,c => compactRun M t (materialize (M.stepConfig c))
theorem check_compact_run_eq (M : UniformTM) {n B : Nat} (t : Nat) (c : Config M.stateCount n B) :
    compactRun M t c = M.run t c := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => rw [compactRun,ih,materialize_eq,show t+1=1+t by omega,M.run_add]; rfl
private def checkRun (M : UniformTM) {n B : Nat} (c : Config M.stateCount n B)
    (t q h : Nat) (T : Fin (tapeLength n B) → Option Bool) : IO Unit := do
  let e := compactRun M t c
  unless e.state.val == q && e.head.val == h && List.ofFn e.tape == List.ofFn T do
    throw (IO.userError s!"G3v mismatch at {t}: state {e.state.val}/{q}, head {e.head.val}/{h}")
private def sample (L : Nat) (b : Bool) : Bitstring L := fun i =>
  if i.val = 13 then b else if 14 ≤ i.val then decide (i.val % 2 = 0) else probeWord L i
private theorem raw_physical (b : Bool) : FixedRawFencedTableFirstBit.machine.run 1265
    (initialConfig FixedRawFencedTableFirstBit.machine 32 (encodePair empty (sample 14 b))) =
      ⟨FixedRawFencedTableFirstBit.machine.accept,⟨15,by decide⟩,outputTape 32 empty (sample 14 b) 2 3 b⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.exhausted_strict_first_terminal
    (B := 32) (zeros := 2) empty (sample 14 b) (by cases b <;> decide) (by cases b <;> decide)
    (by decide) (by intro j hj hj'; interval_cases j <;> cases b <;> decide)).1
  exact raw_first_bit_exact (z := 2) (C := FixedGammaPayloadDispatcherRounds.zeroEndClock 2) (v := 3)
    empty (sample 14 b) (by decide) (by cases b <;> decide) (by cases b <;> decide) (by decide) hf
    (by intro j hj; interval_cases j <;> cases b <;> decide)
    (by intro j hj; exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 3 < 2^3)
      (Nat.pow_le_pow_right (by decide) (show 3 ≤ j by omega)))) (by decide) (by decide) 0
theorem check_raw_physical_false : FixedRawFencedTableFirstBit.machine.run 1265
    (initialConfig FixedRawFencedTableFirstBit.machine 32 (encodePair empty (sample 14 false))) =
      ⟨FixedRawFencedTableFirstBit.machine.accept,⟨15,by decide⟩,outputTape 32 empty (sample 14 false) 2 3 false⟩ :=
  raw_physical false
theorem check_raw_physical_true : FixedRawFencedTableFirstBit.machine.run 1265
    (initialConfig FixedRawFencedTableFirstBit.machine 32 (encodePair empty (sample 14 true))) =
      ⟨FixedRawFencedTableFirstBit.machine.accept,⟨15,by decide⟩,outputTape 32 empty (sample 14 true) 2 3 true⟩ :=
  raw_physical true
private def sampleClock (L : Nat) : Nat :=
  if L = 12 then probeC else FixedGammaPayloadDispatcherRounds.zeroEndClock 2
private def successProbe (L : Nat) (b : Bool) (B : Nat) : IO Unit := do
  let w := sample L b
  let T0 := countdownSuccessClock 0 L 2 (sampleClock L) 2 3
  let T := countdownTape B empty w 2 0 3
  let c := initialConfig FixedRawFencedTableFirstBit.machine B (encodePair empty w)
  let out := outputTape B empty w 2 3 (sourceBit empty w 2)
  checkRun prefixed (initialConfig prefixed B (encodePair empty w)) (T0-1) 253 (L+4) T
  checkRun FixedRawFencedTableFirstBit.machine c T0 256 (L+4) T
  checkRun FixedRawFencedTableFirstBit.machine c (T0+cursorClock 0 L 2) 260 (sourceCursor 0 L 2) T
  checkRun FixedRawFencedTableFirstBit.machine c (T0+copyClock 0 L 2-1)
    (if sourceBit empty w 2 then 264 else 263) (L+1) T
  for s in [0,2] do checkRun FixedRawFencedTableFirstBit.machine c (T0+copyClock 0 L 2+s) 265 (L+1) out
  IO.println s!"G3v full raw PASS: L={L}, bit={b}, B={B}, exact={T0+copyClock 0 L 2}"
#eval do
  successProbe 12 false 28 -- Minimal positive trail, partially virtual payload.
  successProbe 13 false 30 -- E=L, boundary blank.
  successProbe 14 false 32 -- E=L-1, false.
  successProbe 14 true 32 -- E=L-1, true overwrites the zero register cell.
  successProbe 17 false 38 -- Physical false and an arbitrary nonconstant later tail.
  successProbe 17 true 41 -- Physical true and a larger allocation.
  checkRun FixedRawFencedTableFirstBit.machine
    (initialConfig FixedRawFencedTableFirstBit.machine 28 (encodePair empty (sample 12 false)))
    (deadline 13) 265 13 (outputTape 28 empty (sample 12 false) 2 3 false)
  IO.println "G3v closed deadline PASS: R=13, deadline=28224"
#eval do
  let c : Config 11 (pairLength 0 11) 26 := ⟨qStart,⟨15,by decide⟩,countdownTape 26 empty (probeWord 11) 2 0 3⟩
  let e := compactRun suffix 200 c
  unless e.state.val == 2 && e.head.val == 0 do throw (IO.userError "excluded no-trail probe failed")
  IO.println "G3v excluded wholly virtual payload: qContentL at head zero after 200 steps; no verdict."

open UniformV1FixedRawLengthFenceCountdownSurfaceTests in
theorem check_tight_minimal : FixedRawFencedTableFirstBit.machine.run (4436+13)
    (initialConfig FixedRawFencedTableFirstBit.machine 44 (encodePair overflowX tightW)) =
      ⟨FixedRawFencedTableFirstBit.machine.accept,⟨20,by decide⟩,outputTape 44 overflowX tightW 5 38 false⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.pending_true_strict_first_terminal
    (B := 44) (zeros := 5) (k := 2) overflowX tightW (by decide) (by decide) (by decide) (by decide)
    (by intro j hj hj'; interval_cases j <;> decide) (by decide)).1
  exact raw_first_bit_exact (z := 5) (C := 53) (v := 38) overflowX tightW
    (by decide) (by decide) (by decide) (by decide) hf (by intro j hj; interval_cases j <;> decide)
    (by intro b hb; exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 38 < 2^6)
      (Nat.pow_le_pow_right (by decide) (show 6 ≤ b by omega)))) (by decide) (by decide) 0
open UniformV1FixedRawLengthFenceCountdownSurfaceTests in
theorem check_one_over : FixedRawFencedTableFirstBit.machine.run 4466
    (initialConfig FixedRawFencedTableFirstBit.machine 45 (encodePair overflowX overW)) =
      ⟨FixedRawFencedTableFirstBit.machine.reject,⟨65,by decide⟩,countdownTape 45 overflowX overW 5 0 38⟩ := by
  rw [FixedRawFencedTableFirstBit.machine,UniformTM.seq_initialConfig]
  have h := UniformTM.seq_reject_handoff prefixed suffix _ (congrArg Config.state check_one_over_capacity) 0
  simpa only [Nat.add_zero,check_one_over_capacity] using h
open UniformV1FixedRawLengthFenceCountdownSurfaceTests in
theorem check_g3s_overflow : FixedRawFencedTableFirstBit.machine.run 4443
    (initialConfig FixedRawFencedTableFirstBit.machine 45 (encodePair overflowX overflowW)) =
      ⟨FixedRawFencedTableFirstBit.machine.reject,⟨65,by decide⟩,overflowTape 23 38⟩ := by
  rw [FixedRawFencedTableFirstBit.machine,UniformTM.seq_initialConfig]
  have h := UniformTM.seq_reject_handoff prefixed suffix _ (congrArg Config.state check_g3s_overflow_from_generic) 0
  simpa only [Nat.add_zero,check_g3s_overflow_from_generic] using h
open UniformV1FixedRawLengthFenceCountdownSurfaceTests in
#eval do
  for B in [44,45] do
    checkRun FixedRawFencedTableFirstBit.machine (initialConfig FixedRawFencedTableFirstBit.machine B (encodePair overflowX tightW))
      4449 265 20 (outputTape B overflowX tightW 5 38 false)
  checkRun FixedRawFencedTableFirstBit.machine (initialConfig FixedRawFencedTableFirstBit.machine 45 (encodePair overflowX overW))
    4466 266 65 (countdownTape 45 overflowX overW 5 0 38)
  checkRun FixedRawFencedTableFirstBit.machine (initialConfig FixedRawFencedTableFirstBit.machine 45 (encodePair overflowX overflowW))
    4443 266 65 (overflowTape 23 38)
  IO.println "G3v exact capacity (minimal and larger allocation), F+1 and G3s overflow PASS"

end Pnp3.Tests.UniformV1FixedRawFencedTableFirstBitSurfaceTests
