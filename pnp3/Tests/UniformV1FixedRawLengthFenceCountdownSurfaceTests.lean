import Complexity.Uniform.V1.FixedRawLengthFenceCountdown
import Complexity.Uniform.V1.FixedRawLengthFenceOverflowWitness

/-! G3u Infrastructure: named full propositions and concrete raw executions. -/
namespace Pnp3.Tests.UniformV1FixedRawLengthFenceCountdownSurfaceTests
open Complexity.Uniform.V1 Complexity.Uniform.V1.PairEncoding Complexity.Uniform.V1.FixedRawLengthFence
open FixedGammaTargetRegisterDecrement (borrow decBit)

theorem check_raw_fenced_countdown_success_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z) (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false) (hcap : v ≤ capacity a m z) (s : Nat) :
    prefixed.run (countdownSuccessClock a m z C (borrow x w z) v+s)
      (initialConfig prefixed B (encodePair x w)) =
    ⟨prefixed.accept,⟨a+m+2+z,by have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z hg).1; simp only [tapeLength,pairLength] at *; omega⟩,countdownTape B x w z 0 v⟩ :=
  raw_fenced_countdown_success_exact x w hr htag hg hz hfirst hv hhigh hcap s

theorem check_raw_fenced_countdown_reject_exact {a m B z C v : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a) (w : Bitstring m)
    (hr : 2*pairLength a m+2 ≤ B) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z) (hz : 2 ≤ z)
    (hfirst : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q)
    (hv : ∀ j, j ≤ z → v.testBit (z-j) = decBit x w z (borrow x w z) j)
    (hhigh : ∀ b, z < b → v.testBit b = false) (hcap : capacity a m z < v) (s : Nat) :
    prefixed.run (countdownRejectClock a m z C (borrow x w z)+s)
      (initialConfig prefixed B (encodePair x w)) =
    ⟨prefixed.reject,⟨fencePos (pairLength a m),by simp only [tapeLength,pairLength,fencePos] at *; omega⟩,
      countdownTape B x w z (v-capacity a m z-1) (capacity a m z)⟩ :=
  raw_fenced_countdown_reject_exact x w hr htag hg hz hfirst hv hhigh hcap s

theorem check_countdown_clock_bound {a m z C d v : Nat} (hw : 9+z ≤ a+m) (hz : 2 ≤ z)
    (hd : d ≤ z) (hC : C ≤ 2*(a+m)*(a+m)) (hv : v ≤ capacity a m z) :
    countdownSuccessClock a m z C d v ≤ countdownDeadline (pairLength a m) ∧
    countdownRejectClock a m z C d ≤ countdownDeadline (pairLength a m) ∧
    allocation (pairLength a m) ≤ countdownDeadline (pairLength a m) :=
  countdown_clock_bound hw hz hd hC hv

theorem check_countdown_success_cells {a m B z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2*pairLength a m+2 ≤ B) (hv : v ≤ capacity a m z) :
    (∀ i : Fin (tapeLength (pairLength a m) B), i.val < a+m →
      countdownTape B x w z 0 v i = FixedGammaTargetPayloadExhaustion.finishTape B x w z i) ∧
    (∀ j, j ≤ z → ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a+m+1+j →
      countdownTape B x w z 0 v i = some false) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), i.val = a+m+2+z →
      countdownTape B x w z 0 v i = none) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), a+m+3+z ≤ i.val → i.val < a+m+3+z+v →
      countdownTape B x w z 0 v i = some true) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), a+m+3+z+v ≤ i.val → i.val < fencePos (pairLength a m) →
      countdownTape B x w z 0 v i = none) ∧
    (∀ i : Fin (tapeLength (pairLength a m) B), i.val = fencePos (pairLength a m) →
      countdownTape B x w z 0 v i = some false) :=
  countdown_success_cells x w hg hr hv

open FixedGammaTargetUnaryCountdown in
theorem check_entry_head_bound {a m B zeros v d : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a+m+2+zeros < tapeLength (pairLength a m) B) (hd : d ≤ zeros)
    (hlow : ∀ b, b < d → v.testBit b = true) (hstop : v.testBit d = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qStart)
    (hh : c.head.val = a+m+1+zeros-d) (ht : c.tape = loopTape B x w zeros v 0) :
    ∀ t, t ≤ d+2 → (machine.run t c).head.val ≤ a+m+2+zeros :=
  entry_head_bound x w hroom hd hlow hstop c hq hh ht

open FixedGammaTargetUnaryCountdown in
theorem check_round_traced {a m B zeros v r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 3 + zeros + r < tapeLength (pairLength a m) B) (hpos : 1 ≤ v)
    (hhigh : ∀ b, zeros < b → v.testBit b = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros v r) :
    let e := machine.run (roundClock zeros r) c
    (e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros (v - 1) (r + 1)) ∧
    (let s := machine.run (2*zeros+5+r) c
     s.state = qRunEnd ∧ s.head.val = a+m+3+zeros+r ∧
       s.tape = loopTape B x w zeros (v-1) r) ∧
    (∀ t, t < 2*zeros+5+r → (machine.run t c).head.val < a+m+3+zeros+r) ∧
    (∀ t, t ≤ roundClock zeros r → (machine.run t c).head.val ≤ a+m+3+zeros+r) :=
  round_traced x w hroom hpos hhigh c hq hh ht

open FixedGammaTargetUnaryCountdown in
theorem check_exhaust_traced {a m B zeros r : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros 0 r) :
    let e := machine.run (zeroClock zeros) c
    (e.state = qDone ∧ e.head.val = a + m + 2 + zeros ∧ e.tape = loopTape B x w zeros 0 r ∧
      (∀ t, zeroClock zeros ≤ t → machine.run t c = e)) ∧
    (∀ t, t ≤ zeroClock zeros → (machine.run t c).head.val ≤ a+m+2+zeros) :=
  exhaust_traced x w hroom c hq hh ht

/-- Same G3s geometry, with gamma payloads encoding 38, 39 and 40 before decrement. -/
def belowW : Bitstring 18 :=
  ![false,true,true,false,false,true,false,false,false,false,false,false,true,false,false,true,true,false]
def tightW : Bitstring 18 :=
  ![false,true,true,false,false,true,false,false,false,false,false,false,true,false,false,true,true,true]
def overW : Bitstring 18 :=
  ![false,true,true,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false]
private theorem high6 (v : Nat) (hv : v < 64) : ∀ b, 5 < b → v.testBit b = false := by
  intro b hb
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 6 ≤ b by omega)))

/-- Kernel-checked full raw execution just below capacity, with a nonzero borrow. -/
theorem check_below_capacity : prefixed.run 4347
    (initialConfig prefixed 45 (encodePair overflowX belowW)) =
      ⟨prefixed.accept,⟨26,by decide⟩,countdownTape 45 overflowX belowW 5 0 37⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.pending_true_strict_first_terminal
    (B := 45) (zeros := 5) (k := 2) overflowX belowW (by decide) (by decide) (by decide) (by decide)
    (by intro j hj hj'; interval_cases j <;> decide) (by decide)).1
  exact raw_fenced_countdown_success_exact (z := 5) (C := 53) (v := 37) overflowX belowW
    (by decide) (by decide) (by decide) (by decide) hf (by intro j hj; interval_cases j <;> decide)
    (high6 37 (by decide)) (by decide) 0

/-- Equality is success: the final mark is at cell 64 and false remains at 65. -/
theorem check_exact_capacity : prefixed.run 4436
    (initialConfig prefixed 45 (encodePair overflowX tightW)) =
      ⟨prefixed.accept,⟨26,by decide⟩,countdownTape 45 overflowX tightW 5 0 38⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.pending_true_strict_first_terminal
    (B := 45) (zeros := 5) (k := 2) overflowX tightW (by decide) (by decide) (by decide) (by decide)
    (by intro j hj hj'; interval_cases j <;> decide) (by decide)).1
  exact raw_fenced_countdown_success_exact (z := 5) (C := 53) (v := 38) overflowX tightW
    (by decide) (by decide) (by decide) (by decide) hf (by intro j hj; interval_cases j <;> decide)
    (high6 38 (by decide)) (by decide) 0

/-- The tight success also works at minimal allocation, with the fence at the last cell. -/
theorem check_exact_capacity_min_allocation : prefixed.run 4436
    (initialConfig prefixed 44 (encodePair overflowX tightW)) =
      ⟨prefixed.accept,⟨26,by decide⟩,countdownTape 44 overflowX tightW 5 0 38⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.pending_true_strict_first_terminal
    (B := 44) (zeros := 5) (k := 2) overflowX tightW (by decide) (by decide) (by decide) (by decide)
    (by intro j hj hj'; interval_cases j <;> decide) (by decide)).1
  exact raw_fenced_countdown_success_exact (z := 5) (C := 53) (v := 38) overflowX tightW
    (by decide) (by decide) (by decide) (by decide) hf (by intro j hj; interval_cases j <;> decide)
    (high6 38 (by decide)) (by decide) 0

/-- One above capacity rejects, even though its last decrement reaches zero. -/
theorem check_one_over_capacity : prefixed.run 4466
    (initialConfig prefixed 45 (encodePair overflowX overW)) =
      ⟨prefixed.reject,⟨65,by decide⟩,countdownTape 45 overflowX overW 5 0 38⟩ := by
  have hf := (FixedGammaPayloadDispatcherFirstArrival.pending_true_strict_first_terminal
    (B := 45) (zeros := 5) (k := 1) overflowX overW (by decide) (by decide) (by decide) (by decide)
    (by intro j hj hj'; interval_cases j; decide) (by decide)).1
  exact raw_fenced_countdown_reject_exact (z := 5) (C := 38) (v := 39) overflowX overW
    (by decide) (by decide) (by decide) (by decide) hf (by intro j hj; interval_cases j <;> decide)
    (high6 39 (by decide)) (by decide) 0

/-- Recover the independently proved G3s full-tape rejection using the universal result. -/
theorem check_g3s_overflow_from_generic : prefixed.run 4443
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨prefixed.reject,⟨65,by decide⟩,overflowTape 23 38⟩ := by
  have h := raw_fenced_countdown_reject_exact (B := 45) (z := 5) (C := 21) (v := 62)
    overflowX overflowW (by decide) overflow_values.1 overflow_values.2.1 (by decide)
    overflow_values.2.2.1 overflow_values.2.2.2.2.1 overflow_values.2.2.2.2.2 (by decide) 0
  change prefixed.run 4443 _ = _ at h
  rw [h]; apply Config.ext_parts (by rfl) (by rfl); funext i
  fin_cases i <;> decide

/- Materializing the finite tape avoids thousands of nested update closures in
Lean's interpreter. This is the identity on configurations, proved below. -/
private def materialize {k n B : Nat} (c : Config k n B) : Config k n B :=
  let cells := Array.ofFn c.tape
  {c with tape := fun i => cells[i.val]'(by simp [cells])}
private theorem materialize_eq {k n B : Nat} (c : Config k n B) : materialize c = c := by
  apply Config.ext_parts (by rfl) (by rfl)
  funext i; simp [materialize]
private def compactRun (M : UniformTM) {n B : Nat} : Nat → Config M.stateCount n B → Config M.stateCount n B
  | 0,c => c
  | t+1,c => compactRun M t (materialize (M.stepConfig c))

/-- The executable harness is exactly the original run, at every time and input configuration. -/
theorem check_compact_run_eq (M : UniformTM) {n B : Nat} (t : Nat) (c : Config M.stateCount n B) :
    compactRun M t c = M.run t c := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [compactRun,ih,materialize_eq,show t+1=1+t by omega,M.run_add]
    rfl

/-- Executable tests evaluate raw runs and compare every tape cell, independently
of the theorem proofs above. A mismatch fails elaboration of this command. -/
private def regression (B : Nat) (w : Bitstring 18) (t q h v r : Nat) : IO Unit := do
  let e := compactRun prefixed t (initialConfig prefixed B (encodePair overflowX w))
  unless e.state.val == q && e.head.val == h &&
      List.ofFn e.tape == List.ofFn (countdownTape B overflowX w 5 v r) do
    throw (IO.userError s!"G3u raw regression failed at time {t}")
  IO.println s!"G3u raw execution PASS: allocation={B}, time={t}, state={q}, head={h}, register={v}, marks={r}"
#eval regression 45 belowW 4347 254 26 0 37
#eval regression 45 tightW 4436 254 26 0 38
#eval regression 44 tightW 4436 254 26 0 38
#eval regression 45 overW 4466 255 65 0 38
#eval regression 45 overflowW 4443 255 65 23 38
end Pnp3.Tests.UniformV1FixedRawLengthFenceCountdownSurfaceTests
