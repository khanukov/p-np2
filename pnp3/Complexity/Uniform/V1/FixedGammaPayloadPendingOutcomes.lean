import Complexity.Uniform.V1.FixedGammaPayloadRoundDriver

/-!
# Fixed gamma-payload pending outcomes (Part A G2h)

Proof-only exact outcomes for a nonfinal successor round.  All clocks are local
to `FixedGammaPayloadRoundStep`; no cleanup, semantic verdict, whole-payload
claim, or cross-machine clock is provided.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadPendingOutcomes

open PairEncoding
open FixedGammaPayloadRoundStep
open FixedGammaPayloadRoundDriver

/-- Tape after restoring the old cursor, before any pending-outcome cleanup. -/
def pendingTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (k : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = 7 ∨ (8 ≤ i.val ∧ i.val < 9 + k) then none
  else FixedPairContentMarkerErase.contentTape B x w i

/-- Outside marker 7 and the spent counter prefix, the pending tape is content. -/
theorem pendingTape_footprint {a m B k : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hcounter : ¬ (8 ≤ i.val ∧ i.val < 9 + k)) :
    pendingTape B x w k i = FixedPairContentMarkerErase.contentTape B x w i := by
  simp [pendingTape, h7, hcounter]

/-- Successor-local time of the pending outcome from boundary `k`. -/
def pendingClock (zeros k : Nat) : Nat := boundaryClock zeros k + roundCost zeros

/-- A pending round lands at the next boundary's clock value. -/
theorem pendingClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    pendingClock zeros k = boundaryClock zeros (k + 1) := by
  rw [pendingClock, boundaryClock_succ hk]

/-- Bounds needed by both physical-true and virtual pending arms. -/
theorem pending_no_clamp_facts {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hk : 1 ≤ k)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    0 < 7 + k ∧ 9 + zeros + k < tapeLength (pairLength a m) B := by
  have hp := prefix_physical_bound x w hk hprefix
  unfold tapeLength pairLength
  omega

private theorem config_ext {N B : Nat} {c d : Config stateCount N B}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c; cases d; cases hs; cases hh; cases ht; rfl

private theorem step_eq {N B : Nat} (c : Config stateCount N B)
    (q' : Fin stateCount) (s' : Option Bool) (mv : Move)
    (h : machine.step c.state (c.tape c.head) = (q', s', mv)) :
    machine.stepConfig c =
      ⟨q', moveHead c.head mv, fun i => if i = c.head then s' else c.tape i⟩ := by
  apply config_ext
  · change (machine.step c.state (c.tape c.head)).1 = q'; rw [h]
  · change moveHead c.head (machine.step c.state (c.tape c.head)).2.2 = _; rw [h]
  · funext i
    change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1 else c.tape i) = _
    rw [h]

private def cfg {a m : Nat} (B : Nat) (q : Fin stateCount) (j : Nat)
    (hj : j < tapeLength (pairLength a m) B)
    (t : Fin (tapeLength (pairLength a m) B) → Option Bool) :
    Config stateCount (pairLength a m) B := ⟨q, ⟨j, hj⟩, t⟩

private theorem step_keep {a m B j : Nat} (q q' : Fin stateCount)
    (hj : j < tapeLength (pairLength a m) B) (t) (s : Option Bool) (mv : Move)
    (hr : t ⟨j, hj⟩ = s) (ha : machine.step q s = (q', s, mv)) :
    machine.stepConfig (cfg B q j hj t) = cfg B q' (moveHead ⟨j, hj⟩ mv).val
      (by exact (moveHead ⟨j, hj⟩ mv).isLt) t := by
  rw [step_eq _ q' s mv (by simpa [cfg, hr] using ha)]
  apply config_ext <;> try rfl
  funext i
  by_cases hi : i = ⟨j, hj⟩ <;> simp [cfg, hi, hr]

private theorem content_at {a m B j : Nat} (x : Bitstring a) (w : Bitstring m)
    (hj : j < a + m) :
    FixedPairContentMarkerErase.contentTape B x w
      ⟨j, by unfold tapeLength pairLength; omega⟩ = some ((Fin.append x w) ⟨j, hj⟩) := by
  simp [FixedPairContentMarkerErase.contentTape, hj]
private theorem start_none_action : machine.step qStart none =
    (qBackPayload, none, .left) := by decide
private theorem backPayload_false_action : machine.step qBackPayload (some false) =
    (qBackPayload, some false, .left) := by decide
private theorem backPayload_true_action : machine.step qBackPayload (some true) =
    (qBackCounter, some true, .left) := by decide
private theorem backCounter_false_action : machine.step qBackCounter (some false) =
    (qBackCounter, some false, .left) := by decide
private theorem backCounter_none_action : machine.step qBackCounter none =
    (qSpend, none, .right) := by decide
private theorem spend_false_action : machine.step qSpend (some false) =
    (qSeekTerm, none, .right) := by decide
private theorem seekTerm_false_action : machine.step qSeekTerm (some false) =
    (qSeekTerm, some false, .right) := by decide
private theorem seekTerm_true_action : machine.step qSeekTerm (some true) =
    (qSeekHole, some true, .right) := by decide
private theorem seekHole_false_action : machine.step qSeekHole (some false) =
    (qSeekHole, some false, .right) := by decide
private theorem seekHole_none_action : machine.step qSeekHole none =
    (qRead, some false, .right) := by decide

set_option maxHeartbeats 800000 in
private theorem pending_pre_read_exact {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B)
    (hc : RoundInvariant B x w zeros k c) :
    machine.run (2 * zeros + 3) c =
      cfg B qRead (9 + zeros + k) (by
        have hp := prefix_physical_bound x w hk hprefix
        unfold tapeLength pairLength
        omega) (pendingTape B x w k) := by
  have hpOld := prefix_physical_bound x w hk hprefix
  let t0 := roundTape B x w zeros k
  let t1 := fun i : Fin (tapeLength (pairLength a m) B) =>
    if i.val = 8 + k then none else t0 i
  let t2 := fun i : Fin (tapeLength (pairLength a m) B) =>
    if i.val = 8 + zeros + k then some false else t1 i
  have hlen : 9 + zeros + k < tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength; omega
  have hgamma := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hstart : machine.run 1 c = cfg B qBackPayload (7 + zeros + k) (by omega) t0 := by
    rcases hc with ⟨hs, hh, ht⟩
    have heq : c = cfg B qStart (8 + zeros + k) (by omega) t0 := by
      apply config_ext
      · simpa [cfg] using hs
      · apply Fin.ext; simpa [cfg] using hh
      · simpa [t0, cfg] using ht
    rw [heq]
    simp only [UniformTM.run]
    rw [step_keep qStart qBackPayload _ t0 none .left (by simp [t0, roundTape])
      start_none_action]
    apply config_ext <;> try rfl
    apply Fin.ext
    simp [cfg, moveHead]
    omega
  have hbackPayload (r : Nat) (hr : r ≤ k - 1) :
      machine.run r (cfg B qBackPayload (7 + zeros + k) (by omega) t0) =
        cfg B qBackPayload (7 + zeros + k - r) (by omega) t0 := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by omega)]
        have hjlow : 9 + zeros ≤ 7 + zeros + k - r := by omega
        have hjhigh : 7 + zeros + k - r < 9 + zeros + k := by omega
        have hb0 := hprefix (7 + zeros + k - r) hjlow hjhigh
        have hb : (Fin.append x w) ⟨7 + zeros + k - r, by omega⟩ = false := by
          simpa [FixedContentTagGate.physicalSymbol,
            show 7 + zeros + k - r < a + m by omega] using hb0
        have hread : t0 ⟨7 + zeros + k - r, by omega⟩ = some false := by
          have hct := content_at (B := B) x w (show 7 + zeros + k - r < a + m by omega)
          simp [t0, roundTape, show 7 + zeros + k - r ≠ 7 by omega,
            show ¬(8 ≤ 7 + zeros + k - r ∧ 7 + zeros + k - r < 8 + k) by omega,
            show 7 + zeros + k - r ≠ 8 + zeros + k by omega, hct, hb]
        rw [step_keep qBackPayload qBackPayload _ t0 (some false) .left hread
          backPayload_false_action]
        apply config_ext <;> try rfl
  have hterm : t0 ⟨8 + zeros, by omega⟩ = some true := by
    have hct := content_at (B := B) x w hgamma.1
    have hb : (Fin.append x w) ⟨8 + zeros, hgamma.1⟩ = true := by
      simpa [FixedContentTagGate.physicalSymbol, hgamma.1] using hgamma.2.1
    simp [t0, roundTape, hct, hb]
    omega
  have htoCounter : machine.run k (cfg B qBackPayload (7 + zeros + k) (by omega) t0) =
      cfg B qBackCounter (7 + zeros) (by omega) t0 := by
    have hr := hbackPayload (k - 1) (by omega)
    have hlast : machine.run 1
        (cfg B qBackPayload (7 + zeros + k - (k - 1)) (by omega) t0) =
        cfg B qBackCounter (7 + zeros) (by omega) t0 := by
      simp only [UniformTM.run]
      rw [step_keep qBackPayload qBackCounter _ t0 (some true) .left (by
      have he : (⟨7 + zeros + k - (k - 1), by omega⟩ :
          Fin (tapeLength (pairLength a m) B)) = ⟨8 + zeros, by omega⟩ := by
        apply Fin.ext; simp; omega
      simpa only [he] using hterm) backPayload_true_action]
      apply config_ext <;> try rfl
      apply Fin.ext
      simp [cfg, moveHead]
      omega
    calc
      machine.run k _ = machine.run 1 (machine.run (k - 1) _) := by
        rw [← machine.run_add, show k - 1 + 1 = k by omega]
      _ = _ := by rw [hr, hlast]
  have hbackCounter (r : Nat) (hr : r ≤ zeros - k) :
      machine.run r (cfg B qBackCounter (7 + zeros) (by omega) t0) =
        cfg B qBackCounter (7 + zeros - r) (by omega) t0 := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by omega)]
        have hzbit := hgamma.2.2 (zeros - r - 1) (by omega)
        have hb : (Fin.append x w) ⟨7 + zeros - r, by omega⟩ = false := by
          simpa [FixedContentTagGate.physicalSymbol, show 7 + zeros - r < a + m by omega,
            show 8 + (zeros - r - 1) = 7 + zeros - r by omega] using hzbit
        have hct := content_at (B := B) x w (show 7 + zeros - r < a + m by omega)
        have hread : t0 ⟨7 + zeros - r, by omega⟩ = some false := by
          simp [t0, roundTape, show 7 + zeros - r ≠ 7 by omega,
            show ¬(8 ≤ 7 + zeros - r ∧ 7 + zeros - r < 8 + k) by omega,
            show 7 + zeros - r ≠ 8 + zeros + k by omega, hct, hb]
        rw [step_keep qBackCounter qBackCounter _ t0 (some false) .left hread
          backCounter_false_action]
        apply config_ext <;> try rfl
  have hhole : t0 ⟨7 + k, by omega⟩ = none := by simp [t0, roundTape]; omega
  have htoSpend : machine.run (zeros - k + 1)
      (cfg B qBackCounter (7 + zeros) (by omega) t0) =
      cfg B qSpend (8 + k) (by omega) t0 := by
    rw [show zeros - k + 1 = (zeros - k) + 1 by omega, machine.run_add,
      hbackCounter (zeros - k) (by omega)]
    simp only [UniformTM.run]
    rw [step_keep qBackCounter qSpend _ t0 none .right (by
      have he : (⟨7 + zeros - (zeros - k), by omega⟩ :
          Fin (tapeLength (pairLength a m) B)) = ⟨7 + k, by omega⟩ := by
        apply Fin.ext; simp; omega
      simpa only [he] using hhole) backCounter_none_action]
    apply config_ext <;> try rfl
    apply Fin.ext
    simp [cfg, moveHead, show 7 + zeros - (zeros - k) + 1 <
      tapeLength (pairLength a m) B by unfold tapeLength pairLength; omega]
    omega
  have hspend : machine.run 1 (cfg B qSpend (8 + k) (by omega) t0) =
      cfg B qSeekTerm (9 + k) (by omega) t1 := by
    simp only [UniformTM.run]
    have hzbit := hgamma.2.2 k hkz
    have hb : (Fin.append x w) ⟨8 + k, by omega⟩ = false := by
      simpa [FixedContentTagGate.physicalSymbol, show 8 + k < a + m by omega] using hzbit
    have hct := content_at (B := B) x w (show 8 + k < a + m by omega)
    rw [step_eq _ qSeekTerm none .right (by
      simpa [cfg, t0, roundTape, hct, hb, show zeros ≠ 0 by omega, show 8 + k ≠ 7 by omega,
        show ¬(8 ≤ 8 + k ∧ 8 + k < 8 + k) by omega,
        show 8 + k ≠ 8 + zeros + k by omega] using spend_false_action)]
    apply config_ext
    · rfl
    · apply Fin.ext
      simp [cfg, moveHead, show 8 + k + 1 < tapeLength (pairLength a m) B by
        unfold tapeLength pairLength; omega]
      omega
    · funext i
      simp only [cfg]
      by_cases hi : i.val = 8 + k
      · have he : i = ⟨8 + k, by omega⟩ := Fin.ext hi
        rw [he]; simp [t1]
      · simp [t1, hi, show i ≠ ⟨8 + k, by omega⟩ by intro h; exact hi (congrArg Fin.val h)]
  have hseekTerm (r : Nat) (hr : r ≤ zeros - k - 1) :
      machine.run r (cfg B qSeekTerm (9 + k) (by omega) t1) =
        cfg B qSeekTerm (9 + k + r) (by omega) t1 := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by omega)]
        have hzbit := hgamma.2.2 (k + 1 + r) (by omega)
        have hb : (Fin.append x w) ⟨9 + k + r, by omega⟩ = false := by
          have he : 8 + (k + 1 + r) = 9 + k + r := by omega
          rw [he] at hzbit
          simpa [FixedContentTagGate.physicalSymbol,
            show 9 + k + r < a + m by omega] using hzbit
        have hct := content_at (B := B) x w (show 9 + k + r < a + m by omega)
        have hread : t1 ⟨9 + k + r, by omega⟩ = some false := by
          simp [t1, t0, roundTape, show 9 + k + r ≠ 8 + k by omega,
            show 9 + k + r ≠ 7 by omega,
            show ¬(8 ≤ 9 + k + r ∧ 9 + k + r < 8 + k) by omega,
            show 9 + k + r ≠ 8 + zeros + k by omega, hct, hb]
        rw [step_keep qSeekTerm qSeekTerm _ t1 (some false) .right hread seekTerm_false_action]
        apply config_ext <;> try rfl
        apply Fin.ext
        simp [cfg, moveHead, show 9 + k + r + 1 < tapeLength (pairLength a m) B by
          unfold tapeLength pairLength; omega]
        omega
  have htoHole : machine.run (zeros - k) (cfg B qSeekTerm (9 + k) (by omega) t1) =
      cfg B qSeekHole (9 + zeros) (by omega) t1 := by
    rw [show zeros - k = (zeros - k - 1) + 1 by omega, machine.run_add,
      hseekTerm (zeros - k - 1) (by omega)]
    simp only [UniformTM.run]
    have hread : t1 ⟨8 + zeros, by omega⟩ = some true := by
      simp [t1]
      exact ⟨by omega, hterm⟩
    rw [step_keep qSeekTerm qSeekHole _ t1 (some true) .right (by
      have he : (⟨9 + k + (zeros - k - 1), by omega⟩ :
          Fin (tapeLength (pairLength a m) B)) = ⟨8 + zeros, by omega⟩ := by
        apply Fin.ext; simp; omega
      simpa only [he] using hread) seekTerm_true_action]
    apply config_ext <;> try rfl
    apply Fin.ext
    simp [cfg, moveHead, show 9 + k + (zeros - k - 1) + 1 <
      tapeLength (pairLength a m) B by unfold tapeLength pairLength; omega]
    omega
  have hseekHole (r : Nat) (hr : r ≤ k - 1) :
      machine.run r (cfg B qSeekHole (9 + zeros) (by omega) t1) =
        cfg B qSeekHole (9 + zeros + r) (by omega) t1 := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by omega)]
        have hb0 := hprefix (9 + zeros + r) (by omega) (by omega)
        have hb : (Fin.append x w) ⟨9 + zeros + r, by omega⟩ = false := by
          simpa [FixedContentTagGate.physicalSymbol,
            show 9 + zeros + r < a + m by omega] using hb0
        have hct := content_at (B := B) x w (show 9 + zeros + r < a + m by omega)
        have hread : t1 ⟨9 + zeros + r, by omega⟩ = some false := by
          simp [t1, t0, roundTape, show 9 + zeros + r ≠ 8 + k by omega,
            show 9 + zeros + r ≠ 7 by omega,
            show ¬(8 ≤ 9 + zeros + r ∧ 9 + zeros + r < 8 + k) by omega,
            show 9 + zeros + r ≠ 8 + zeros + k by omega, hct, hb]
        rw [step_keep qSeekHole qSeekHole _ t1 (some false) .right hread seekHole_false_action]
        apply config_ext <;> try rfl
        apply Fin.ext
        simp [cfg, moveHead, show 9 + zeros + r + 1 < tapeLength (pairLength a m) B by
          unfold tapeLength pairLength; omega]
        omega
  have holdHole : t1 ⟨8 + zeros + k, by omega⟩ = none := by
    simp [t1, t0, roundTape]
  have htoRead : machine.run k (cfg B qSeekHole (9 + zeros) (by omega) t1) =
      cfg B qRead (9 + zeros + k) (by omega) t2 := by
    have hr := hseekHole (k - 1) (by omega)
    have hlast : machine.run 1 (cfg B qSeekHole (9 + zeros + (k - 1)) (by omega) t1) =
        cfg B qRead (9 + zeros + k) (by omega) t2 := by
      simp only [UniformTM.run]
      rw [step_eq _ qRead (some false) .right (by
        simpa [cfg, show 9 + zeros + (k - 1) = 8 + zeros + k by omega, holdHole]
          using seekHole_none_action)]
      apply config_ext
      · rfl
      · apply Fin.ext
        simp [cfg, moveHead, show 9 + zeros + (k - 1) + 1 <
          tapeLength (pairLength a m) B by unfold tapeLength pairLength; omega]
        omega
      · funext i
        simp only [cfg]
        by_cases hi : i.val = 8 + zeros + k
        · have he : i = ⟨8 + zeros + k, by omega⟩ := Fin.ext hi
          rw [he]
          simp [t2, show 9 + zeros + (k - 1) = 8 + zeros + k by omega]
        · simp [t2, hi, show i ≠ ⟨9 + zeros + (k - 1), by omega⟩ by
            intro h; apply hi; simpa [show 9 + zeros + (k - 1) = 8 + zeros + k by omega]
              using congrArg Fin.val h]
    calc
      machine.run k _ = machine.run 1 (machine.run (k - 1) _) := by
        rw [← machine.run_add, show k - 1 + 1 = k by omega]
      _ = _ := by rw [hr, hlast]
  have ht2 : t2 = pendingTape B x w k := by
    funext i
    simp only [t2, t1, t0, roundTape, pendingTape]
    by_cases hold : i.val = 8 + zeros + k
    · have he : i = (⟨8 + zeros + k, by omega⟩ :
          Fin (tapeLength (pairLength a m) B)) := Fin.ext hold
      rw [he]
      have hb0 := hprefix (8 + zeros + k) (by omega) (by omega)
      have hb : (Fin.append x w) ⟨8 + zeros + k, by omega⟩ = false := by
        simpa [FixedContentTagGate.physicalSymbol,
          show 8 + zeros + k < a + m by omega] using hb0
      have hct := content_at (B := B) x w (show 8 + zeros + k < a + m by omega)
      simp [hct, hb]
      omega
    · by_cases hsp : i.val = 8 + k <;>
      by_cases h7 : i.val = 7 <;>
      by_cases hz : 8 ≤ i.val ∧ i.val < 8 + k <;>
        simp [hold, hsp, h7, hz] <;> omega
  have htoRead' : machine.run k (cfg B qSeekHole (9 + zeros) (by omega) t1) =
      cfg B qRead (9 + zeros + k) (by omega) (pendingTape B x w k) := by
    simpa only [ht2] using htoRead
  rw [show 2 * zeros + 3 =
      1 + (k + (zeros - k + 1 + (1 + (zeros - k + k)))) by omega,
    machine.run_add, hstart,
    show k + (zeros - k + 1 + (1 + (zeros - k + k))) =
      k + ((zeros - k + 1) + (1 + ((zeros - k) + k))) by omega,
    machine.run_add, htoCounter, machine.run_add, htoSpend, machine.run_add, hspend,
    machine.run_add, htoHole]
  exact htoRead'

private theorem read_true_action : machine.step qRead (some true) =
    (qOnePending, some true, .stay) := by decide
private theorem read_virtual_action : machine.step qRead none =
    (qVirtualPending, none, .stay) := by decide
private theorem one_pending_action (s : Option Bool) : machine.step qOnePending s =
    (qOnePending, s, .stay) := by
  cases s with | none => decide | some b => cases b <;> decide
private theorem virtual_pending_action (s : Option Bool) : machine.step qVirtualPending s =
    (qVirtualPending, s, .stay) := by
  cases s with | none => decide | some b => cases b <;> decide

/-- Exact local pending outcome when the next physical payload bit is true. -/
theorem pending_true_tail_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true)
    (c : Config stateCount (pairLength a m) B) (hc : RoundInvariant B x w zeros k c) :
    let d := machine.run (roundCost zeros) c
    d.state = qOnePending ∧ d.head.val = 9 + zeros + k ∧
      d.tape = pendingTape B x w k := by
  have hp : 9 + zeros + k < a + m := by
    unfold FixedContentTagGate.physicalSymbol at htrue
    split at htrue
    · assumption
    · contradiction
  have hpre := pending_pre_read_exact x w hg hk hkz hprefix c hc
  have hread : pendingTape B x w k ⟨9 + zeros + k, by
      unfold tapeLength pairLength; omega⟩ = some true := by
    have hct := content_at (B := B) x w hp
    simp [pendingTape, hct, show 9 + zeros + k ≠ 7 by omega]
    simpa [FixedContentTagGate.physicalSymbol, hp] using htrue
  dsimp only
  rw [show roundCost zeros = (2 * zeros + 3) + 1 by simp [roundCost],
    machine.run_add, hpre]
  simp only [UniformTM.run]
  rw [step_keep qRead qOnePending _ (pendingTape B x w k) (some true) .stay hread
    read_true_action]
  refine ⟨rfl, ?_, rfl⟩
  simp [cfg, moveHead]

/-- Exact local pending outcome when the read cell is the physical boundary. -/
theorem pending_virtual_tail_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m)
    (c : Config stateCount (pairLength a m) B) (hc : RoundInvariant B x w zeros k c) :
    let d := machine.run (roundCost zeros) c
    d.state = qVirtualPending ∧ d.head.val = 9 + zeros + k ∧
      d.tape = pendingTape B x w k := by
  have hpre := pending_pre_read_exact x w hg hk hkz hprefix c hc
  have hread : pendingTape B x w k ⟨9 + zeros + k, by
      unfold tapeLength pairLength; omega⟩ = none := by
    simp [pendingTape, FixedPairContentMarkerErase.contentTape, hvirtual]
  dsimp only
  rw [show roundCost zeros = (2 * zeros + 3) + 1 by simp [roundCost],
    machine.run_add, hpre]
  simp only [UniformTM.run]
  rw [step_keep qRead qVirtualPending _ (pendingTape B x w k) none .stay hread
    read_virtual_action]
  refine ⟨rfl, ?_, rfl⟩
  simp [cfg, moveHead]

/-- Either pending outcome fixes the entire configuration forever. -/
theorem pending_absorbing {N B : Nat} (c : Config stateCount N B)
    (hc : c.state = qOnePending ∨ c.state = qVirtualPending) (s : Nat) :
    machine.run s c = c := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [UniformTM.run, ih]
      rcases hc with hone | hvirtual
      · rw [step_eq c qOnePending (c.tape c.head) .stay (by
          simpa [hone] using one_pending_action (c.tape c.head))]
        apply config_ext
        · exact hone.symm
        · apply Fin.ext; simp [moveHead]
        · funext i
          by_cases hi : i = c.head <;> simp [hi]
      · rw [step_eq c qVirtualPending (c.tape c.head) .stay (by
          simpa [hvirtual] using virtual_pending_action (c.tape c.head))]
        apply config_ext
        · exact hvirtual.symm
        · apply Fin.ext; simp [moveHead]
        · funext i
          by_cases hi : i = c.head <;> simp [hi]

/-- Neither pending tag occurs before the exact end of a nonfinal local round. -/
theorem pending_strict {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B) (hc : RoundInvariant B x w zeros k c)
    (s : Nat) (hs : s < roundCost zeros) :
    (machine.run s c).state ≠ qOnePending ∧
      (machine.run s c).state ≠ qVirtualPending := by
  have hpre := pending_pre_read_exact x w hg hk hkz hprefix c hc
  have hs' : s ≤ 2 * zeros + 3 := by simp [roundCost] at hs; omega
  have hdecomp : machine.run (2 * zeros + 3) c =
      machine.run (2 * zeros + 3 - s) (machine.run s c) := by
    rw [← machine.run_add]
    congr 1
    omega
  constructor <;> intro hbad
  · have hfix := pending_absorbing (machine.run s c) (Or.inl hbad)
        (2 * zeros + 3 - s)
    have hstate := congrArg Config.state (hdecomp.trans hfix)
    rw [hpre] at hstate
    rw [hbad] at hstate
    exact (by decide : qRead ≠ qOnePending) hstate
  · have hfix := pending_absorbing (machine.run s c) (Or.inr hbad)
        (2 * zeros + 3 - s)
    have hstate := congrArg Config.state (hdecomp.trans hfix)
    rw [hpre] at hstate
    rw [hbad] at hstate
    exact (by decide : qRead ≠ qVirtualPending) hstate

/-- Driver-composed exact physical-true pending outcome. -/
theorem pending_true_reachable {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (pendingClock zeros k) (startConfig B x w zeros)
    d.state = qOnePending ∧ d.head.val = 9 + zeros + k ∧
      d.tape = pendingTape B x w k := by
  have hb := boundary_reachable (B := B) x w htag hg hk (by omega) hprefix
  rw [pendingClock, machine.run_add]
  exact pending_true_tail_exact x w hg hk hkz hprefix htrue _ hb

/-- Driver-composed exact virtual pending outcome at the physical boundary. -/
theorem pending_virtual_reachable {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := machine.run (pendingClock zeros k) (startConfig B x w zeros)
    d.state = qVirtualPending ∧ d.head.val = 9 + zeros + k ∧
      d.tape = pendingTape B x w k := by
  have hb := boundary_reachable (B := B) x w htag hg hk (by omega) hprefix
  rw [pendingClock, machine.run_add]
  exact pending_virtual_tail_exact x w hg hk hkz hprefix hvirtual _ hb

/-- Globally within the successor run, the pending tags are first possible at
`pendingClock`; earlier false rounds cannot hide an absorbed pending result. -/
theorem pending_first_arrival {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (s : Nat) (hs : s < pendingClock zeros k) :
    (machine.run s (startConfig B x w zeros)).state ≠ qOnePending ∧
      (machine.run s (startConfig B x w zeros)).state ≠ qVirtualPending := by
  have hb := boundary_reachable (B := B) x w htag hg hk (by omega) hprefix
  by_cases hearly : s < boundaryClock zeros k
  · have hdecomp : machine.run (boundaryClock zeros k) (startConfig B x w zeros) =
        machine.run (boundaryClock zeros k - s)
          (machine.run s (startConfig B x w zeros)) := by
      rw [← machine.run_add]
      congr 1
      omega
    constructor <;> intro hbad
    · have hfix := pending_absorbing _ (Or.inl hbad) (boundaryClock zeros k - s)
      have hstate := congrArg Config.state (hdecomp.trans hfix)
      rw [hb.1] at hstate
      rw [hbad] at hstate
      exact (by decide : qStart ≠ qOnePending) hstate
    · have hfix := pending_absorbing _ (Or.inr hbad) (boundaryClock zeros k - s)
      have hstate := congrArg Config.state (hdecomp.trans hfix)
      rw [hb.1] at hstate
      rw [hbad] at hstate
      exact (by decide : qStart ≠ qVirtualPending) hstate
  · have hsLocal : s - boundaryClock zeros k < roundCost zeros := by
      simp [pendingClock] at hs
      omega
    have hlocal := pending_strict x w hg hk hkz hprefix _ hb
      (s - boundaryClock zeros k) hsLocal
    have heq : machine.run s (startConfig B x w zeros) =
        machine.run (s - boundaryClock zeros k)
          (machine.run (boundaryClock zeros k) (startConfig B x w zeros)) := by
      rw [← machine.run_add]
      congr 1
      omega
    simpa only [heq] using hlocal

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadPendingOutcomes
