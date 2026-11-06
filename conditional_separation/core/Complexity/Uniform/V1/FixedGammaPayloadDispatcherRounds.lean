import Complexity.Uniform.V1.FixedGammaPayloadDispatcher

/-!
# Fixed gamma-payload dispatcher positive rounds (Part A G2l)

Proof-only activation of the positive physical-true, first-virtual, and fully
exhausted paths of `FixedGammaPayloadDispatcher`.  All clocks start at the
dispatcher's actual G2a-derived `startConfig`; routed transitions introduce no
extra handoff step.  This module gives execution facts only, not payload
semantics or a whole-dispatcher characterization.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherRounds

set_option maxHeartbeats 800000

open PairEncoding
open FixedGammaPayloadDispatcher

def roundStartClock (zeros : Nat) : Nat :=
  FixedGammaPayloadRoundStep.coreTime zeros

def boundaryArrivalClock (zeros k : Nat) : Nat :=
  roundStartClock zeros + FixedGammaPayloadRoundDriver.boundaryClock zeros k

def pendingArrivalClock (zeros k : Nat) : Nat :=
  roundStartClock zeros + FixedGammaPayloadPendingOutcomes.pendingClock zeros k

def pendingEndClock (zeros k : Nat) : Nat :=
  pendingArrivalClock zeros k + FixedGammaPayloadPendingCleanup.cleanupClock zeros k

def exhaustedArrivalClock (zeros : Nat) : Nat :=
  roundStartClock zeros + FixedGammaPayloadExhausted.exhaustedClock zeros

def zeroEndClock (zeros : Nat) : Nat :=
  exhaustedArrivalClock zeros + FixedGammaPayloadZeroCleanup.cleanupClock zeros

theorem roundStartClock_eq (zeros : Nat) : roundStartClock zeros = 2 * zeros + 4 := rfl

theorem boundaryArrivalClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    boundaryArrivalClock zeros k = k * (2 * zeros + 4) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp [boundaryArrivalClock, roundStartClock,
    FixedGammaPayloadRoundDriver.boundaryClock,
    FixedGammaPayloadRoundStep.coreTime, FixedGammaPayloadRoundStep.roundCost]
  ring

theorem pendingArrivalClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    pendingArrivalClock zeros k = (k + 1) * (2 * zeros + 4) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp [pendingArrivalClock, roundStartClock,
    FixedGammaPayloadPendingOutcomes.pendingClock,
    FixedGammaPayloadRoundDriver.boundaryClock,
    FixedGammaPayloadRoundStep.coreTime, FixedGammaPayloadRoundStep.roundCost]
  ring

theorem pendingEndClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    pendingEndClock zeros k = 2 * zeros * k + 3 * zeros + 5 * k + 8 := by
  rw [pendingEndClock, pendingArrivalClock_eq hk]
  simp [FixedGammaPayloadPendingCleanup.cleanupClock]
  ring

theorem exhaustedArrivalClock_eq {zeros : Nat} (hzero : 0 < zeros) :
    exhaustedArrivalClock zeros = 2 * zeros * zeros + 5 * zeros + 3 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hzero
  simp [exhaustedArrivalClock, roundStartClock,
    FixedGammaPayloadExhausted.exhaustedClock,
    FixedGammaPayloadExhausted.exhaustedTail,
    FixedGammaPayloadRoundDriver.boundaryClock,
    FixedGammaPayloadRoundStep.coreTime, FixedGammaPayloadRoundStep.roundCost]
  ring

theorem zeroEndClock_eq {zeros : Nat} (hzero : 0 < zeros) :
    zeroEndClock zeros = 2 * zeros * zeros + 8 * zeros + 6 := by
  rw [zeroEndClock, exhaustedArrivalClock_eq hzero]
  simp [FixedGammaPayloadZeroCleanup.cleanupClock]
  omega

private theorem config_ext {S N B : Nat} {c d : Config S N B}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c; cases d; cases hs; cases hh; cases ht; rfl

private def mapConfig {P N B : Nat} (f : Fin P → Fin stateCount) (c : Config P N B) :
    Config stateCount N B := ⟨f c.state, c.head, c.tape⟩

private theorem step_map {N B : Nat} (M : UniformTM)
    (f : Fin M.stateCount → Fin stateCount) (c : Config M.stateCount N B)
    (ha : machine.step (f c.state) (c.tape c.head) =
      (f (M.step c.state (c.tape c.head)).1,
        (M.step c.state (c.tape c.head)).2.1,
        (M.step c.state (c.tape c.head)).2.2)) :
    machine.stepConfig (mapConfig f c) = mapConfig f (M.stepConfig c) := by
  rcases c with ⟨q, head, tape⟩
  simp only [mapConfig, UniformTM.stepConfig]
  rw [ha]

private theorem run_map {N B : Nat} (M : UniformTM)
    (f : Fin M.stateCount → Fin stateCount) (good : Fin M.stateCount → Prop)
    (ha : ∀ q s, good q → machine.step (f q) s =
      (f (M.step q s).1, (M.step q s).2.1, (M.step q s).2.2))
    (c : Config M.stateCount N B) (n : Nat)
    (hg : ∀ i, i < n → good (M.run i c).state) :
    machine.run n (mapConfig f c) = mapConfig f (M.run n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [UniformTM.run, UniformTM.run, ih (fun i hi => hg i (by omega))]
      exact step_map M f _ (ha _ _ (hg n (by omega)))

private theorem fixed_if_absorbing {N B : Nat} (M : UniformTM)
    (q : Fin M.stateCount) (hrow : ∀ s, M.step q s = (q, s, .stay))
    (c : Config M.stateCount N B) (hc : c.state = q) (n : Nat) : M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [UniformTM.run, ih]
      rcases c with ⟨state, head, tape⟩
      change state = q at hc
      subst state
      simp [UniformTM.stepConfig, hrow, moveHead]
      funext i
      by_cases hi : i = head <;> simp [hi]

private theorem avoids_absorbing_of_final {N B clock : Nat} (M : UniformTM)
    (q bad : Fin M.stateCount) (hrow : ∀ s, M.step bad s = (bad, s, .stay))
    (c : Config M.stateCount N B) (hfinal : (M.run clock c).state = q)
    (hne : q ≠ bad) : ∀ i, i < clock → (M.run i c).state ≠ bad := by
  intro i hi hbad
  have hd : M.run clock c = M.run (clock - i) (M.run i c) := by
    rw [← M.run_add]
    congr 1
    omega
  rw [fixed_if_absorbing M bad hrow _ hbad] at hd
  have hs := congrArg Config.state hd
  rw [hfinal, hbad] at hs
  exact hne hs

private def coreState (q : Fin FixedGammaPayloadCursorCore.stateCount) : Fin stateCount :=
  match q.val with
  | 0 => qCursorStart | 1 => qCursorBackFirst | 2 => qCursorBackSeen
  | 3 => qCursorSpend | 4 => qCursorSeekTerm | 5 => qCursorRead
  | 6 => qRoundStart | 7 => qCursorRestoreOne | 8 => qCursorRestoreVirtual
  | 9 => qCursorFillOne | 10 => qCursorFillVirtual | 11 => qHasOne
  | 12 => qAllZero | _ => qReject

private theorem core_action (q : Fin FixedGammaPayloadCursorCore.stateCount)
    (s : Option Bool) (h : q ≠ FixedGammaPayloadCursorCore.qNextFalse) :
    machine.step (coreState q) s =
      (coreState (FixedGammaPayloadCursorCore.machine.step q s).1,
        (FixedGammaPayloadCursorCore.machine.step q s).2.1,
        (FixedGammaPayloadCursorCore.machine.step q s).2.2) := by
  fin_cases q <;> try { exact (h rfl).elim } <;> cases s with
  | none => decide
  | some b => cases b <;> decide

private theorem actual_start_eq_core {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    startConfig B x w = mapConfig coreState
      (FixedGammaPayloadCursorCore.startConfig B x w) := by
  simp only [FixedGammaPayloadDispatcher.startConfig,
    FixedGammaPayloadCursorCore.startConfig]
  rw [FixedContentGammaAnchor.run_deadline x w htag]
  rfl

private def roundState (q : Fin FixedGammaPayloadRoundStep.stateCount) : Fin stateCount :=
  match q.val with
  | 0 => qRoundStart | 1 => qRoundBackPayload | 2 => qRoundBackCounter
  | 3 => qRoundSpend | 4 => qRoundSeekTerm | 5 => qRoundSeekHole
  | 6 => qRoundRead | 7 => qZeroScanRight | 8 => qPendingStart
  | 9 => qPendingStart | _ => qReject

private theorem round_action (q : Fin FixedGammaPayloadRoundStep.stateCount)
    (s : Option Bool)
    (h7 : q ≠ FixedGammaPayloadRoundStep.qExhausted)
    (h8 : q ≠ FixedGammaPayloadRoundStep.qOnePending)
    (h9 : q ≠ FixedGammaPayloadRoundStep.qVirtualPending) :
    machine.step (roundState q) s =
      (roundState (FixedGammaPayloadRoundStep.machine.step q s).1,
        (FixedGammaPayloadRoundStep.machine.step q s).2.1,
        (FixedGammaPayloadRoundStep.machine.step q s).2.2) := by
  fin_cases q <;> try { exact (h7 rfl).elim } <;> try { exact (h8 rfl).elim } <;>
    try { exact (h9 rfl).elim } <;> cases s with
  | none => decide
  | some b => cases b <;> decide

private theorem round_run_to {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (n : Nat)
    (hgood : ∀ i, i < n →
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qExhausted ∧
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qOnePending ∧
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qVirtualPending) :
    machine.run n (mapConfig roundState
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)) =
      mapConfig roundState (FixedGammaPayloadRoundStep.machine.run n
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)) := by
  apply run_map FixedGammaPayloadRoundStep.machine roundState
    (fun q => q ≠ FixedGammaPayloadRoundStep.qExhausted ∧
      q ≠ FixedGammaPayloadRoundStep.qOnePending ∧
      q ≠ FixedGammaPayloadRoundStep.qVirtualPending)
    (fun q s h => round_action q s h.1 h.2.1 h.2.2) _ n
  exact hgood

private def pendingState (q : Fin FixedGammaPayloadPendingCleanup.stateCount) : Fin stateCount :=
  match q.val with
  | 0 => qPendingStart | 1 => qPendingBackOne | 2 => qPendingBackVirtual
  | 3 => qPendingFillOne | 4 => qPendingFillVirtual | 5 => qHasOne
  | 6 => qAllZero | _ => qReject

private theorem pending_action (q : Fin FixedGammaPayloadPendingCleanup.stateCount)
    (s : Option Bool) :
    machine.step (pendingState q) s =
      (pendingState (FixedGammaPayloadPendingCleanup.machine.step q s).1,
        (FixedGammaPayloadPendingCleanup.machine.step q s).2.1,
        (FixedGammaPayloadPendingCleanup.machine.step q s).2.2) := by
  fin_cases q <;> cases s with
  | none => decide
  | some b => cases b <;> decide

private theorem pending_allZero_iff (q : Fin FixedGammaPayloadPendingCleanup.stateCount) :
    pendingState q = qAllZero ↔ q = FixedGammaPayloadPendingCleanup.qVirtual := by
  fin_cases q <;> decide

private theorem pending_hasOne_iff (q : Fin FixedGammaPayloadPendingCleanup.stateCount) :
    pendingState q = qHasOne ↔ q = FixedGammaPayloadPendingCleanup.qOne := by
  fin_cases q <;> decide

private def zeroState (q : Fin FixedGammaPayloadZeroCleanup.stateCount) : Fin stateCount :=
  match q.val with
  | 0 => qZeroScanRight | 1 => qZeroBackTerm | 2 => qZeroFillCounter
  | 3 => qAllZero | _ => qReject

private theorem zero_action (q : Fin FixedGammaPayloadZeroCleanup.stateCount)
    (s : Option Bool) :
    machine.step (zeroState q) s =
      (zeroState (FixedGammaPayloadZeroCleanup.machine.step q s).1,
        (FixedGammaPayloadZeroCleanup.machine.step q s).2.1,
        (FixedGammaPayloadZeroCleanup.machine.step q s).2.2) := by
  fin_cases q <;> cases s with
  | none => decide
  | some b => cases b <;> decide

private theorem zero_allZero_iff (q : Fin FixedGammaPayloadZeroCleanup.stateCount) :
    zeroState q = qAllZero ↔ q = FixedGammaPayloadZeroCleanup.qDone := by
  fin_cases q <;> decide

private theorem dispatcher_round_start {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (hfalse : (Fin.append x w) ⟨9 + zeros, hp⟩ = false) :
    machine.run (roundStartClock zeros) (startConfig B x w) =
      mapConfig roundState (FixedGammaPayloadRoundStep.startConfig B x w zeros) := by
  rw [actual_start_eq_core x w htag]
  have hend := FixedGammaPayloadCursorCore.first_physical_false_exact
    (B := B) x w htag hg hzero hp hfalse
  have hpre := FixedGammaPayloadCursorCore.first_read_reachable
    (B := B) x w htag hg hzero
  have hgood : ∀ i, i < roundStartClock zeros →
      (FixedGammaPayloadCursorCore.machine.run i
        (FixedGammaPayloadCursorCore.startConfig B x w)).state ≠
          FixedGammaPayloadCursorCore.qNextFalse := by
    intro i hi
    by_cases heq : i = 2 * zeros + 3
    · subst i
      rw [hpre.1]
      decide
    · apply avoids_absorbing_of_final FixedGammaPayloadCursorCore.machine
        FixedGammaPayloadCursorCore.qRead FixedGammaPayloadCursorCore.qNextFalse
        (fun s => FixedGammaPayloadCursorCore.table_and_resource_pins.2.2.2.2.2.2.1 s)
        _ hpre.1 (by decide) i
      simp [roundStartClock, FixedGammaPayloadRoundStep.coreTime] at hi
      omega
  rw [run_map FixedGammaPayloadCursorCore.machine coreState
    (fun q => q ≠ FixedGammaPayloadCursorCore.qNextFalse) core_action _ _ hgood]
  dsimp only [mapConfig, FixedGammaPayloadRoundStep.startConfig,
    FixedGammaPayloadRoundStep.retag, roundStartClock]
  apply config_ext
  · simpa [mapConfig, FixedGammaPayloadRoundStep.coreTime, coreState, roundState]
      using congrArg coreState hend.1
  · rfl
  · rfl

private theorem first_false_from_prefix {a m zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m) (hk : 1 ≤ k)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    ∃ hp : 9 + zeros < a + m, (Fin.append x w) ⟨9 + zeros, hp⟩ = false := by
  have h := hprefix (9 + zeros) (by omega) (by omega)
  unfold FixedContentTagGate.physicalSymbol at h
  split at h
  · rename_i hp
    exact ⟨hp, Option.some.inj h⟩
  · contradiction

theorem round_start_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k ≤ zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (roundStartClock zeros) (startConfig B x w)
    d.state = qRoundStart ∧ d.head.val = 9 + zeros ∧
      d.tape = FixedGammaPayloadRoundStep.roundTape B x w zeros 1 := by
  obtain ⟨hp, hf⟩ := first_false_from_prefix x w hk hprefix
  rw [dispatcher_round_start x w htag hg (by omega) hp hf]
  have hh := FixedGammaPayloadRoundStep.handoff_exact
    (B := B) x w htag hg (by omega) hp hf
  refine ⟨rfl, ?_, ?_⟩
  · change (FixedGammaPayloadRoundStep.startConfig B x w zeros).head.val = 9 + zeros
    exact hh.2.1.trans (by omega)
  · exact hh.2.2

theorem boundary_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k ≤ zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (boundaryArrivalClock zeros k) (startConfig B x w)
    d.state = qRoundStart ∧ d.head.val = 8 + zeros + k ∧
      d.tape = FixedGammaPayloadRoundStep.roundTape B x w zeros k := by
  obtain ⟨hp, hf⟩ := first_false_from_prefix x w hk hprefix
  have hb := FixedGammaPayloadRoundDriver.boundary_reachable
    (B := B) x w htag hg hk hkz hprefix
  rw [boundaryArrivalClock, machine.run_add, dispatcher_round_start x w htag hg
    (by omega) hp hf]
  have hgood : ∀ i, i < FixedGammaPayloadRoundDriver.boundaryClock zeros k →
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qExhausted ∧
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qOnePending ∧
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qVirtualPending := by
    intro i hi
    refine ⟨?_, ?_, ?_⟩ <;>
      apply avoids_absorbing_of_final FixedGammaPayloadRoundStep.machine
        FixedGammaPayloadRoundStep.qStart _
        (fun s => by cases s with | none => decide | some b => cases b <;> decide)
        _ hb.1 (by decide) i hi
  rw [round_run_to x w _ hgood]
  change roundState _ = qRoundStart ∧ _
  exact ⟨by rw [hb.1]; rfl, hb.2.1, hb.2.2⟩

private theorem pending_start_common {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hend : (FixedGammaPayloadRoundStep.machine.run
      (FixedGammaPayloadPendingOutcomes.pendingClock zeros k)
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state =
        FixedGammaPayloadRoundStep.qOnePending ∨
      (FixedGammaPayloadRoundStep.machine.run
        (FixedGammaPayloadPendingOutcomes.pendingClock zeros k)
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state =
          FixedGammaPayloadRoundStep.qVirtualPending) :
    machine.run (pendingArrivalClock zeros k) (startConfig B x w) =
      mapConfig roundState (FixedGammaPayloadRoundStep.machine.run
        (FixedGammaPayloadPendingOutcomes.pendingClock zeros k)
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)) := by
  obtain ⟨hp, hf⟩ := first_false_from_prefix x w hk hprefix
  rw [pendingArrivalClock, machine.run_add, dispatcher_round_start x w htag hg
    (by omega) hp hf]
  apply round_run_to x w
  intro i hi
  have hpending := FixedGammaPayloadPendingOutcomes.pending_first_arrival
    (B := B) x w htag hg hk hkz hprefix i hi
  refine ⟨?_, hpending.1, hpending.2⟩
  rcases hend with he | he
  · exact avoids_absorbing_of_final FixedGammaPayloadRoundStep.machine
      FixedGammaPayloadRoundStep.qOnePending
      FixedGammaPayloadRoundStep.qExhausted
      (fun s => by cases s with | none => decide | some b => cases b <;> decide)
      _ he (by decide) i hi
  · exact avoids_absorbing_of_final FixedGammaPayloadRoundStep.machine
      FixedGammaPayloadRoundStep.qVirtualPending
      FixedGammaPayloadRoundStep.qExhausted
      (fun s => by cases s with | none => decide | some b => cases b <;> decide)
      _ he (by decide) i hi

theorem pending_true_start_exact {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (pendingArrivalClock zeros k) (startConfig B x w)
    d.state = qPendingStart ∧ d.head.val = 9 + zeros + k ∧
      d.tape = FixedGammaPayloadPendingOutcomes.pendingTape B x w k := by
  have h := FixedGammaPayloadPendingOutcomes.pending_true_reachable
    (B := B) x w htag hg hk hkz hprefix htrue
  rw [pending_start_common x w htag hg hk hkz hprefix (Or.inl h.1)]
  exact ⟨by change roundState _ = _; rw [h.1]; rfl, h.2.1, h.2.2⟩

theorem pending_virtual_start_exact {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := machine.run (pendingArrivalClock zeros k) (startConfig B x w)
    d.state = qPendingStart ∧ d.head.val = 9 + zeros + k ∧
      d.tape = FixedGammaPayloadPendingOutcomes.pendingTape B x w k := by
  have h := FixedGammaPayloadPendingOutcomes.pending_virtual_reachable
    (B := B) x w htag hg hk hkz hprefix hvirtual
  rw [pending_start_common x w htag hg hk hkz hprefix (Or.inr h.1)]
  exact ⟨by change roundState _ = _; rw [h.1]; rfl, h.2.1, h.2.2⟩

theorem exhausted_start_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (exhaustedArrivalClock zeros) (startConfig B x w)
    d.state = qZeroScanRight ∧ d.head.val = 8 + zeros ∧
      d.tape = FixedGammaPayloadRoundStep.roundTape B x w zeros zeros := by
  obtain ⟨hp, hf⟩ := first_false_from_prefix (zeros := zeros) x w
    (show 1 ≤ zeros by omega) (by intro j hlo hhi; exact hprefix j hlo (by omega))
  have h := FixedGammaPayloadExhausted.exhausted_reachable
    (B := B) x w htag hg hzero hprefix
  have hb := FixedGammaPayloadRoundDriver.last_boundary_reachable
    (B := B) x w htag hg hzero hprefix
  rw [exhaustedArrivalClock, machine.run_add,
    dispatcher_round_start x w htag hg hzero hp hf]
  have hgood : ∀ i, i < FixedGammaPayloadExhausted.exhaustedClock zeros →
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qExhausted ∧
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qOnePending ∧
      (FixedGammaPayloadRoundStep.machine.run i
        (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠
          FixedGammaPayloadRoundStep.qVirtualPending := by
    intro i hi
    have hpending (bad) (hne : FixedGammaPayloadRoundStep.qExhausted ≠ bad)
        (hrow : ∀ s, FixedGammaPayloadRoundStep.machine.step bad s = (bad, s, .stay)) :
        (FixedGammaPayloadRoundStep.machine.run i
          (FixedGammaPayloadRoundStep.startConfig B x w zeros)).state ≠ bad :=
      avoids_absorbing_of_final FixedGammaPayloadRoundStep.machine
        FixedGammaPayloadRoundStep.qExhausted bad hrow _
        h.1 hne i hi
    refine ⟨?_, hpending FixedGammaPayloadRoundStep.qOnePending (by decide)
      (fun s => by cases s with | none => decide | some b => cases b <;> decide),
      hpending FixedGammaPayloadRoundStep.qVirtualPending (by decide)
      (fun s => by cases s with | none => decide | some b => cases b <;> decide)⟩
    by_cases hearly : i < FixedGammaPayloadRoundDriver.boundaryClock zeros zeros
    · exact avoids_absorbing_of_final FixedGammaPayloadRoundStep.machine
        FixedGammaPayloadRoundStep.qStart
        FixedGammaPayloadRoundStep.qExhausted
        (fun s => by cases s with | none => decide | some b => cases b <;> decide)
        _ hb.1 (by decide) i hearly
    · have hlocal : i - FixedGammaPayloadRoundDriver.boundaryClock zeros zeros <
          FixedGammaPayloadExhausted.exhaustedTail zeros := by
        simp [FixedGammaPayloadExhausted.exhaustedClock] at hi
        omega
      have hs := FixedGammaPayloadExhausted.exhausted_strict x w hg hzero hprefix _ hb
        (i - FixedGammaPayloadRoundDriver.boundaryClock zeros zeros) hlocal
      have heq : FixedGammaPayloadRoundStep.machine.run i
          (FixedGammaPayloadRoundStep.startConfig B x w zeros) =
          FixedGammaPayloadRoundStep.machine.run
            (i - FixedGammaPayloadRoundDriver.boundaryClock zeros zeros)
            (FixedGammaPayloadRoundStep.machine.run
              (FixedGammaPayloadRoundDriver.boundaryClock zeros zeros)
              (FixedGammaPayloadRoundStep.startConfig B x w zeros)) := by
        rw [← FixedGammaPayloadRoundStep.machine.run_add]
        congr 1
        omega
      simpa only [heq] using hs
  rw [round_run_to x w _ hgood]
  change roundState _ = qZeroScanRight ∧ _
  exact ⟨by rw [h.1]; rfl, h.2.1, h.2.2⟩

def TrueExecution {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros k : Nat) : Prop :=
  let d := machine.run (pendingEndClock zeros k) (startConfig B x w)
  d.state = qHasOne ∧ d.head.val = 6 ∧
  d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
  (∀ s, s < pendingEndClock zeros k →
    (machine.run s (startConfig B x w)).state ≠ qHasOne) ∧
  (∀ s, (machine.run s (startConfig B x w)).state ≠ qAllZero ∧
    (machine.run s (startConfig B x w)).state ≠ qReject)

def VirtualExecution {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros k : Nat) : Prop :=
  let d := machine.run (pendingEndClock zeros k) (startConfig B x w)
  d.state = qAllZero ∧ d.head.val = 6 ∧
  d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
  (∀ s, s < pendingEndClock zeros k →
    (machine.run s (startConfig B x w)).state ≠ qAllZero) ∧
  (∀ s, (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
    (machine.run s (startConfig B x w)).state ≠ qReject)

def ZeroExecution {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : Prop :=
  let d := machine.run (zeroEndClock zeros) (startConfig B x w)
  d.state = qAllZero ∧ d.head.val = 6 ∧
  d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
  (∀ s, s < zeroEndClock zeros →
    (machine.run s (startConfig B x w)).state ≠ qAllZero) ∧
  (∀ s, (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
    (machine.run s (startConfig B x w)).state ≠ qReject)

private theorem dispatcher_wrong_excluded {N B clock : Nat} (c : Config stateCount N B)
    (good bad : Fin stateCount) (hend : (machine.run clock c).state = good)
    (hgood : ∀ d : Config stateCount N B, d.state = good → ∀ r, machine.run r d = d)
    (hbadAbs : ∀ d : Config stateCount N B, d.state = bad → ∀ r, machine.run r d = d)
    (hne : good ≠ bad) (s : Nat) : (machine.run s c).state ≠ bad := by
  by_cases hs : s ≤ clock
  · intro hbad
    have hd : machine.run clock c = machine.run (clock - s) (machine.run s c) := by
      rw [← machine.run_add]; congr 1; omega
    have hfix := hbadAbs (machine.run s c) hbad (clock - s)
    have hh := congrArg Config.state (hd.trans hfix)
    rw [hend, hbad] at hh
    exact hne hh
  · have hafter : machine.run s c = machine.run (s - clock) (machine.run clock c) := by
      rw [← machine.run_add]; congr 1; omega
    intro hbad
    have hgood : (machine.run s c).state = good := by
      rw [hafter]
      have hf := hgood (machine.run clock c) hend (s - clock)
      rw [hf]
      exact hend
    exact hne (hgood.symm.trans hbad)

private theorem strict_from_cleanup {N B arrival localClock : Nat} (c : Config stateCount N B)
    (startTag doneTag : Fin stateCount) (hstart : (machine.run arrival c).state = startTag)
    (hne : startTag ≠ doneTag)
    (hdone : ∀ d : Config stateCount N B, d.state = doneTag → ∀ r, machine.run r d = d)
    (hlocal : ∀ r, r < localClock →
      (machine.run r (machine.run arrival c)).state ≠ doneTag)
    (s : Nat) (hs : s < arrival + localClock) : (machine.run s c).state ≠ doneTag := by
  by_cases hearly : s < arrival
  · intro hbad
    have hd : machine.run arrival c = machine.run (arrival - s) (machine.run s c) := by
      rw [← machine.run_add]; congr 1; omega
    have hfix := hdone (machine.run s c) hbad (arrival - s)
    have hh := congrArg Config.state (hd.trans hfix)
    rw [hstart, hbad] at hh
    exact hne hh
  · have heq : machine.run s c = machine.run (s - arrival) (machine.run arrival c) := by
      rw [← machine.run_add]; congr 1; omega
    rw [heq]
    exact hlocal _ (by omega)

theorem true_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) : TrueExecution B x w zeros k := by
  have hs := pending_true_start_exact (B := B) x w htag hg hk hkz hprefix htrue
  have hc := FixedGammaPayloadPendingCleanup.true_cleanup_exact
    (B := B) x w htag hg hk hkz hprefix htrue
  have hh := FixedGammaPayloadPendingCleanup.handoff_from_pending_true_reachable
    (B := B) x w htag hg hk hkz hprefix htrue
  have hsim := run_map FixedGammaPayloadPendingCleanup.machine pendingState
    (fun _ => True) (fun q s _ => pending_action q s)
    (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k)
    (FixedGammaPayloadPendingCleanup.cleanupClock zeros k) (fun _ _ => trivial)
  have hstartCfg : machine.run (pendingArrivalClock zeros k) (startConfig B x w) =
      mapConfig pendingState (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k) := by
    rw [hh.2.2.2]
    rw [pending_start_common x w htag hg hk hkz hprefix (Or.inl hh.1)]
    dsimp only [mapConfig, FixedGammaPayloadPendingCleanup.retag]
    apply config_ext
    · simpa [mapConfig, roundState, pendingState]
        using congrArg roundState hh.1
    · rfl
    · rfl
  unfold TrueExecution
  have hlen : 6 < tapeLength (pairLength a m) B := by
    have := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
    unfold tapeLength pairLength
    omega
  have hend : machine.run (pendingEndClock zeros k) (startConfig B x w) =
      ⟨qHasOne, ⟨6, hlen⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ := by
    rw [pendingEndClock, machine.run_add, hstartCfg, hsim, hc.1]
    rfl
  refine ⟨congrArg Config.state hend, congrArg (fun d => d.head.val) hend,
    congrArg Config.tape hend, ?_, ?_⟩
  · intro s hlt
    apply strict_from_cleanup _ qPendingStart qHasOne hs.1 (by decide)
      (fun d hd r => endpoints_absorb d |>.2.1 hd r) _ s
      (by simpa [pendingEndClock] using hlt)
    intro r hr
    rw [hstartCfg, run_map FixedGammaPayloadPendingCleanup.machine pendingState
      (fun _ => True) (fun q z _ => pending_action q z)
      (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k) r
      (fun _ _ => trivial)]
    intro hbad
    exact (hc.2.1 r hr).1 ((pending_hasOne_iff _).1 hbad)
  · intro s
    exact ⟨dispatcher_wrong_excluded _ qHasOne qAllZero
      (congrArg Config.state hend) (fun d hd r => endpoints_absorb d |>.2.1 hd r)
      (fun d hd r => endpoints_absorb d |>.1 hd r) (by decide) s,
      dispatcher_wrong_excluded _ qHasOne qReject
      (congrArg Config.state hend) (fun d hd r => endpoints_absorb d |>.2.1 hd r)
      (fun d hd r => endpoints_absorb d |>.2.2 hd r) (by decide) s⟩

theorem virtual_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) : VirtualExecution B x w zeros k := by
  have hs := pending_virtual_start_exact (B := B) x w htag hg hk hkz hprefix hvirtual
  have hc := FixedGammaPayloadPendingCleanup.virtual_cleanup_exact
    (B := B) x w htag hg hk hkz hprefix hvirtual
  have hh := FixedGammaPayloadPendingCleanup.handoff_from_pending_virtual_reachable
    (B := B) x w htag hg hk hkz hprefix hvirtual
  have hstartCfg : machine.run (pendingArrivalClock zeros k) (startConfig B x w) =
      mapConfig pendingState (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k) := by
    rw [hh.2.2.2]
    rw [pending_start_common x w htag hg hk hkz hprefix (Or.inr hh.1)]
    dsimp only [mapConfig, FixedGammaPayloadPendingCleanup.retag]
    apply config_ext
    · simpa [mapConfig, roundState, pendingState]
        using congrArg roundState hh.1
    · rfl
    · rfl
  unfold VirtualExecution
  have hlen : 6 < tapeLength (pairLength a m) B := by
    have := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
    unfold tapeLength pairLength
    omega
  have hend : machine.run (pendingEndClock zeros k) (startConfig B x w) =
      ⟨qAllZero, ⟨6, hlen⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ := by
    rw [pendingEndClock, machine.run_add, hstartCfg,
      run_map FixedGammaPayloadPendingCleanup.machine pendingState
        (fun _ => True) (fun q s _ => pending_action q s) _ _ (fun _ _ => trivial), hc.1]
    rfl
  refine ⟨congrArg Config.state hend, congrArg (fun d => d.head.val) hend,
    congrArg Config.tape hend, ?_, ?_⟩
  · intro s hlt
    apply strict_from_cleanup _ qPendingStart qAllZero hs.1 (by decide)
      (fun d hd r => endpoints_absorb d |>.1 hd r) _ s
      (by simpa [pendingEndClock] using hlt)
    intro r hr
    rw [hstartCfg, run_map FixedGammaPayloadPendingCleanup.machine pendingState
      (fun _ => True) (fun q z _ => pending_action q z) _ r (fun _ _ => trivial)]
    intro hbad
    exact (hc.2.1 r hr).2 ((pending_allZero_iff _).1 hbad)
  · intro s
    exact ⟨dispatcher_wrong_excluded _ qAllZero qHasOne
      (congrArg Config.state hend) (fun d hd r => endpoints_absorb d |>.1 hd r)
      (fun d hd r => endpoints_absorb d |>.2.1 hd r) (by decide) s,
      dispatcher_wrong_excluded _ qAllZero qReject
      (congrArg Config.state hend) (fun d hd r => endpoints_absorb d |>.1 hd r)
      (fun d hd r => endpoints_absorb d |>.2.2 hd r) (by decide) s⟩

theorem zero_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    ZeroExecution B x w zeros := by
  have hs := exhausted_start_exact (B := B) x w htag hg hzero hprefix
  have hc := FixedGammaPayloadZeroCleanup.cleanup_exact
    (B := B) x w htag hg hzero hprefix
  have hh := FixedGammaPayloadZeroCleanup.handoff_from_exhausted_reachable
    (B := B) x w htag hg hzero hprefix
  dsimp only at hh
  have hstartCfg : machine.run (exhaustedArrivalClock zeros) (startConfig B x w) =
      mapConfig zeroState (FixedGammaPayloadZeroCleanup.startConfig B x w zeros) := by
    rw [hh.2.2.2]
    apply config_ext
    · exact hs.1
    · apply Fin.ext; exact hs.2.1.trans hh.2.1.symm
    · exact hs.2.2.trans hh.2.2.1.symm
  unfold ZeroExecution
  have hlen : 6 < tapeLength (pairLength a m) B := by
    have := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
    unfold tapeLength pairLength
    omega
  have hend : machine.run (zeroEndClock zeros) (startConfig B x w) =
      ⟨qAllZero, ⟨6, hlen⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ := by
    rw [zeroEndClock, machine.run_add, hstartCfg,
      run_map FixedGammaPayloadZeroCleanup.machine zeroState
        (fun _ => True) (fun q s _ => zero_action q s) _ _ (fun _ _ => trivial), hc.1]
    rfl
  refine ⟨congrArg Config.state hend, congrArg (fun d => d.head.val) hend,
    congrArg Config.tape hend, ?_, ?_⟩
  · intro s hlt
    apply strict_from_cleanup _ qZeroScanRight qAllZero hs.1 (by decide)
      (fun d hd r => endpoints_absorb d |>.1 hd r) _ s
      (by simpa [zeroEndClock] using hlt)
    intro r hr
    rw [hstartCfg, run_map FixedGammaPayloadZeroCleanup.machine zeroState
      (fun _ => True) (fun q z _ => zero_action q z) _ r (fun _ _ => trivial)]
    intro hbad
    exact hc.2 r hr ((zero_allZero_iff _).1 hbad)
  · intro s
    exact ⟨dispatcher_wrong_excluded _ qAllZero qHasOne
      (congrArg Config.state hend) (fun d hd r => endpoints_absorb d |>.1 hd r)
      (fun d hd r => endpoints_absorb d |>.2.1 hd r) (by decide) s,
      dispatcher_wrong_excluded _ qAllZero qReject
      (congrArg Config.state hend) (fun d hd r => endpoints_absorb d |>.1 hd r)
      (fun d hd r => endpoints_absorb d |>.2.2 hd r) (by decide) s⟩

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherRounds
