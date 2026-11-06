import Complexity.Uniform.V1.FixedGammaPayloadPendingOutcomes
import Mathlib.Data.Fintype.Card

set_option linter.unusedTactic false

/-!
# Fixed gamma-payload pending cleanup (Part A G2i)

This fixed successor retags either absorbing pending endpoint without changing
the predecessor ABI.  The first tape cell dispatches the physical-true and
virtual branches; no proof is converted into branch advice.  Both branches
restore `pendingTape` to literal `contentTape` and retain distinct internal
handoff tags.  There is no semantic verdict, dispatcher claim, acceptance
meaning, or cross-machine clock in this module.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadPendingCleanup

open PairEncoding
open FixedGammaPayloadRoundStep
open FixedGammaPayloadPendingOutcomes

abbrev stateCount : Nat := 8
def qStart : Fin stateCount := ⟨0, by decide⟩
def qBackOne : Fin stateCount := ⟨1, by decide⟩
def qBackVirtual : Fin stateCount := ⟨2, by decide⟩
def qFillOne : Fin stateCount := ⟨3, by decide⟩
def qFillVirtual : Fin stateCount := ⟨4, by decide⟩
def qOne : Fin stateCount := ⟨5, by decide⟩
def qVirtual : Fin stateCount := ⟨6, by decide⟩
def qReject : Fin stateCount := ⟨7, by decide⟩

private def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some true => (qBackOne, some true, .left)
    | none => (qBackVirtual, none, .left)
    | some false => (qReject, some false, .stay)
  | 1 => match s with
    | none => (qFillOne, some false, .left)
    | some b => (qBackOne, some b, .left)
  | 2 => match s with
    | none => (qFillVirtual, some false, .left)
    | some b => (qBackVirtual, some b, .left)
  | 3 => match s with
    | none => (qFillOne, some false, .left)
    | some true => (qOne, some true, .stay)
    | some false => (qReject, some false, .stay)
  | 4 => match s with
    | none => (qFillVirtual, some false, .left)
    | some true => (qVirtual, some true, .stay)
    | some false => (qReject, some false, .stay)
  | 5 => (qOne, s, .stay)
  | 6 => (qVirtual, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qOne
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

def cleanupClock (zeros k : Nat) : Nat := zeros + k + 4

theorem cleanupClock_eq (zeros k : Nat) :
    cleanupClock zeros k = zeros + k + 4 := rfl

def retag {N B : Nat}
    (c : Config FixedGammaPayloadRoundStep.stateCount N B) : Config stateCount N B :=
  ⟨qStart, c.head, c.tape⟩

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros k : Nat) : Config stateCount (pairLength a m) B :=
  retag (FixedGammaPayloadRoundStep.machine.run (pendingClock zeros k)
    (FixedGammaPayloadRoundStep.startConfig B x w zeros))

/-- All 24 rows and all fixed resource fields. -/
theorem table_and_resource_pins :
    (machine.step qStart (some true) = (qBackOne, some true, .left)) ∧
    (machine.step qStart none = (qBackVirtual, none, .left)) ∧
    (machine.step qStart (some false) = (qReject, some false, .stay)) ∧
    (∀ s, machine.step qBackOne s = match s with
      | none => (qFillOne, some false, .left)
      | some b => (qBackOne, some b, .left)) ∧
    (∀ s, machine.step qBackVirtual s = match s with
      | none => (qFillVirtual, some false, .left)
      | some b => (qBackVirtual, some b, .left)) ∧
    (∀ s, machine.step qFillOne s = match s with
      | none => (qFillOne, some false, .left)
      | some true => (qOne, some true, .stay)
      | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qFillVirtual s = match s with
      | none => (qFillVirtual, some false, .left)
      | some true => (qVirtual, some true, .stay)
      | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qOne s = (qOne, s, .stay)) ∧
    (∀ s, machine.step qVirtual s = (qVirtual, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 8 ∧ machine.start = qStart ∧ machine.accept = qOne ∧
    machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 24 := by
  refine ⟨by decide, by decide, by decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    rfl, rfl, rfl, rfl, by decide⟩

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
    machine.stepConfig (cfg B q j hj t) =
      cfg B q' (moveHead ⟨j, hj⟩ mv).val (moveHead ⟨j, hj⟩ mv).isLt t := by
  rw [step_eq _ q' s mv (by simpa [cfg, hr] using ha)]
  apply config_ext <;> try rfl
  funext i
  by_cases hi : i = ⟨j, hj⟩ <;> simp [cfg, hi, hr]

private theorem content_at {a m B j : Nat} (x : Bitstring a) (w : Bitstring m)
    (hj : j < a + m) :
    FixedPairContentMarkerErase.contentTape B x w
      ⟨j, by unfold tapeLength pairLength; omega⟩ = some ((Fin.append x w) ⟨j, hj⟩) := by
  simp [FixedPairContentMarkerErase.contentTape, hj]

/-- Exact retagged handoff from the true pending endpoint. -/
theorem handoff_from_pending_true_reachable {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let p := FixedGammaPayloadRoundStep.machine.run (pendingClock zeros k)
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)
    let c := startConfig B x w zeros k
    p.state = qOnePending ∧ p.head.val = 9 + zeros + k ∧
      p.tape = pendingTape B x w k ∧ c = retag p := by
  dsimp [startConfig]
  exact ⟨(pending_true_reachable (B := B) x w htag hg hk hkz hprefix htrue).1,
    (pending_true_reachable (B := B) x w htag hg hk hkz hprefix htrue).2.1,
    (pending_true_reachable (B := B) x w htag hg hk hkz hprefix htrue).2.2, rfl⟩

/-- Exact retagged handoff from the virtual pending endpoint. -/
theorem handoff_from_pending_virtual_reachable {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let p := FixedGammaPayloadRoundStep.machine.run (pendingClock zeros k)
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)
    let c := startConfig B x w zeros k
    p.state = qVirtualPending ∧ p.head.val = 9 + zeros + k ∧
      p.tape = pendingTape B x w k ∧ c = retag p := by
  dsimp [startConfig]
  exact ⟨(pending_virtual_reachable (B := B) x w htag hg hk hkz hprefix hvirtual).1,
    (pending_virtual_reachable (B := B) x w htag hg hk hkz hprefix hvirtual).2.1,
    (pending_virtual_reachable (B := B) x w htag hg hk hkz hprefix hvirtual).2.2, rfl⟩

theorem cleanup_arithmetic_bounds {a m B zeros k : Nat}
    (hp : 8 + zeros + k < a + m) :
    0 < 7 ∧ 9 + zeros + k < tapeLength (pairLength a m) B := by
  unfold tapeLength pairLength
  omega

theorem initial_footprint {a m B k : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hcounter : ¬ (8 ≤ i.val ∧ i.val < 9 + k)) :
    pendingTape B x w k i = FixedPairContentMarkerErase.contentTape B x w i :=
  pendingTape_footprint x w i h7 hcounter

private theorem start_true_action : machine.step qStart (some true) =
    (qBackOne, some true, .left) := by decide
private theorem start_virtual_action : machine.step qStart none =
    (qBackVirtual, none, .left) := by decide
private theorem back_one_some_action (b : Bool) : machine.step qBackOne (some b) =
    (qBackOne, some b, .left) := by cases b <;> decide
private theorem back_virtual_some_action (b : Bool) : machine.step qBackVirtual (some b) =
    (qBackVirtual, some b, .left) := by cases b <;> decide
private theorem back_one_none_action : machine.step qBackOne none =
    (qFillOne, some false, .left) := by decide
private theorem back_virtual_none_action : machine.step qBackVirtual none =
    (qFillVirtual, some false, .left) := by decide
private theorem fill_one_none_action : machine.step qFillOne none =
    (qFillOne, some false, .left) := by decide
private theorem fill_virtual_none_action : machine.step qFillVirtual none =
    (qFillVirtual, some false, .left) := by decide
private theorem fill_one_true_action : machine.step qFillOne (some true) =
    (qOne, some true, .stay) := by decide
private theorem fill_virtual_true_action : machine.step qFillVirtual (some true) =
    (qVirtual, some true, .stay) := by decide

set_option maxHeartbeats 800000 in
private theorem cleanup_branch_exact {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hphysical : 9 + zeros + k ≤ a + m)
    (qB qF qO : Fin stateCount)
    (hstartAction : machine.step qStart
      (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k)) =
      (qB, FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k), .left))
    (hbackSome : ∀ b, machine.step qB (some b) = (qB, some b, .left))
    (hbackNone : machine.step qB none = (qF, some false, .left))
    (hfillNone : machine.step qF none = (qF, some false, .left))
    (hfillTrue : machine.step qF (some true) = (qO, some true, .stay))
    (hStartNe : qStart ≠ qO) (hBackNe : qB ≠ qO) (hFillNe : qF ≠ qO)
    (hstart : startConfig B x w zeros k =
      cfg B qStart (9 + zeros + k) (by unfold tapeLength pairLength; omega)
        (pendingTape B x w k)) :
    machine.run (cleanupClock zeros k) (startConfig B x w zeros k) =
      ⟨qO, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ ∧
    (∀ s, s < cleanupClock zeros k →
      (machine.run s (startConfig B x w zeros k)).state ≠ qO) := by
  let t0 := pendingTape B x w k
  let t2 := fun r (i : Fin (tapeLength (pairLength a m) B)) =>
    if 8 + k ≤ i.val + r ∧ i.val ≤ 8 + k then some false else t0 i
  have hlen : 9 + zeros + k < tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength; omega
  have hdispatchSymbol : t0 ⟨9 + zeros + k, hlen⟩ =
      FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) := by
    simp [t0, pendingTape, FixedPairContentMarkerErase.contentTape,
      FixedContentTagGate.physicalSymbol]
    omega
  have hdispatch : machine.run 1 (cfg B qStart (9 + zeros + k) hlen t0) =
      cfg B qB (8 + zeros + k) (by unfold tapeLength pairLength; omega) t0 := by
    simp only [UniformTM.run]
    rw [step_keep qStart qB _ t0 _ .left hdispatchSymbol hstartAction]
    apply config_ext <;> try rfl
    apply Fin.ext
    simp [cfg, moveHead]
    omega
  have hback (r : Nat) (hr : r ≤ zeros) :
      machine.run r (cfg B qB (8 + zeros + k) (by unfold tapeLength pairLength; omega) t0) =
        cfg B qB (8 + zeros + k - r) (by unfold tapeLength pairLength; omega) t0 := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by omega)]
        have hj : 8 + zeros + k - r < a + m := by omega
        have hct := content_at (B := B) x w hj
        have hread : ∃ b, t0 ⟨8 + zeros + k - r, by
            unfold tapeLength pairLength; omega⟩ = some b := by
          refine ⟨(Fin.append x w) ⟨8 + zeros + k - r, hj⟩, ?_⟩
          rw [show t0 ⟨8 + zeros + k - r, by unfold tapeLength pairLength; omega⟩ =
              FixedPairContentMarkerErase.contentTape B x w
                ⟨8 + zeros + k - r, by unfold tapeLength pairLength; omega⟩ by
            simp [t0, pendingTape]
            omega]
          exact hct
        obtain ⟨b, hb⟩ := hread
        rw [step_keep qB qB _ t0 (some b) .left hb (hbackSome b)]
        apply config_ext <;> try rfl
  have hhole : t0 ⟨8 + k, by unfold tapeLength pairLength; omega⟩ = none := by
    simp [t0, pendingTape]
  have hturn : machine.run 1
      (cfg B qB (8 + k) (by unfold tapeLength pairLength; omega) t0) =
      cfg B qF (7 + k) (by unfold tapeLength pairLength; omega) (t2 0) := by
    simp only [UniformTM.run]
    rw [step_eq _ qF (some false) .left (by simpa [cfg, hhole] using hbackNone)]
    apply config_ext
    · rfl
    · apply Fin.ext; simp [cfg, moveHead]
    · funext i
      simp only [cfg]
      by_cases hi : i.val = 8 + k
      · have he : i = ⟨8 + k, by unfold tapeLength pairLength; omega⟩ := Fin.ext hi
        rw [he]
        simp [t2]
      · have hn : i ≠ (⟨8 + k, by unfold tapeLength pairLength; omega⟩ :
            Fin (tapeLength (pairLength a m) B)) := by
          intro he; exact hi (congrArg Fin.val he)
        simp [t2, hn]
        omega
  have hfill (r : Nat) (hr : r ≤ k + 1) :
      machine.run r (cfg B qF (7 + k) (by unfold tapeLength pairLength; omega) (t2 0)) =
        cfg B qF (7 + k - r) (by unfold tapeLength pairLength; omega) (t2 r) := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by omega)]
        have hholeR : t2 r ⟨7 + k - r, by unfold tapeLength pairLength; omega⟩ = none := by
          change (if 8 + k ≤ (7 + k - r) + r ∧ 7 + k - r ≤ 8 + k
            then some false else t0 ⟨7 + k - r, _⟩) = none
          rw [if_neg (by omega)]
          simp [t0, pendingTape]
          omega
        rw [step_eq _ qF (some false) .left (by simpa [cfg, hholeR] using hfillNone)]
        apply config_ext
        · rfl
        · apply Fin.ext; simp [cfg, moveHead]; omega
        · funext i
          simp only [cfg]
          by_cases hi : i.val = 7 + k - r
          · have he : i = (⟨7 + k - r, by unfold tapeLength pairLength; omega⟩ :
                Fin (tapeLength (pairLength a m) B)) := Fin.ext hi
            rw [if_pos he]
            simp [t2]
            omega
          · have hn : i ≠ (⟨7 + k - r, by unfold tapeLength pairLength; omega⟩ :
                Fin (tapeLength (pairLength a m) B)) := by
              intro he; exact hi (congrArg Fin.val he)
            simp only [if_neg hn]
            simp only [t2]
            split_ifs with hold hnew
            · rfl
            · exfalso; omega
            · exfalso; omega
            · rfl
  have htag6 : t2 (k + 1) ⟨6, by unfold tapeLength pairLength; omega⟩ = some true := by
    rcases FixedContentTagGate.tag_contract (Fin.append x w) with
      ⟨_, _, _, _, _, _, _, _, hc, htagLen⟩
    have hL := htagLen htag
    have hb := hc.mp htag
    have hbit : (Fin.append x w) ⟨6, by omega⟩ = true := by
      simpa [FixedContentTagGate.expectedTagBit, FixedContentTagGate.physicalSymbol,
        show 6 < a + m by omega] using hb ⟨6, by decide⟩
    have hct := content_at (B := B) x w (show 6 < a + m by omega)
    simp [t2, t0, pendingTape, hct, hbit]
    omega
  have hgamma := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hfinalTape : t2 (k + 1) = FixedPairContentMarkerErase.contentTape B x w := by
    funext i
    by_cases hrepair : 7 ≤ i.val ∧ i.val ≤ 8 + k
    · have hj : i.val < a + m := by omega
      have hct := content_at (B := B) x w hj
      by_cases hi7 : i.val = 7
      · rcases FixedContentTagGate.tag_contract (Fin.append x w) with
          ⟨_, _, _, _, _, _, _, _, hc, htagLen⟩
        have hL := htagLen htag
        have hb := hc.mp htag
        have hbit : (Fin.append x w) ⟨i.val, hj⟩ = false := by
          have h := hb ⟨7, by decide⟩
          simpa [hi7, FixedContentTagGate.expectedTagBit,
            FixedContentTagGate.physicalSymbol, show 7 < a + m by omega] using h
        simp [t2, t0, hrepair, hct, hbit]
        omega
      · have hi8 : 8 ≤ i.val := by omega
        obtain ⟨r, hr, he⟩ : ∃ r, r < zeros ∧ i.val = 8 + r := by
          refine ⟨i.val - 8, by omega, by omega⟩
        have hz := hgamma.2.2 r hr
        have hbit : (Fin.append x w) ⟨i.val, hj⟩ = false := by
          have hfixed : (Fin.append x w) ⟨8 + r, by omega⟩ = false := by
            simpa [FixedContentTagGate.physicalSymbol, show 8 + r < a + m by omega] using hz
          simpa [he] using hfixed
        simp [t2, t0, hrepair, hct, hbit]
        omega
    · have ht2 : ¬ (8 + k ≤ i.val + (k + 1) ∧ i.val ≤ 8 + k) := by omega
      rw [show t2 (k + 1) i = t0 i by simp [t2, ht2]]
      exact pendingTape_footprint x w i (by omega) (by omega)
  have hsBack : machine.run (zeros + 1) (startConfig B x w zeros k) =
      cfg B qB (8 + k) (by unfold tapeLength pairLength; omega) t0 := by
    rw [hstart, show zeros + 1 = 1 + zeros by omega, machine.run_add, hdispatch, hback zeros (by omega)]
    congr 1
    omega
  have hsTurn : machine.run (zeros + 2) (startConfig B x w zeros k) =
      cfg B qF (7 + k) (by unfold tapeLength pairLength; omega) (t2 0) := by
    rw [show zeros + 2 = (zeros + 1) + 1 by omega, machine.run_add, hsBack, hturn]
  have hsFill : machine.run (zeros + k + 3) (startConfig B x w zeros k) =
      cfg B qF 6 (by unfold tapeLength pairLength; omega) (t2 (k + 1)) := by
    rw [show zeros + k + 3 = (zeros + 2) + (k + 1) by omega,
      machine.run_add, hsTurn, hfill (k + 1) (by omega)]
    congr 1
    omega
  constructor
  · rw [show cleanupClock zeros k = (zeros + k + 3) + 1 by simp [cleanupClock],
      machine.run_add, hsFill]
    simp only [UniformTM.run]
    rw [step_keep qF qO _ (t2 (k + 1)) (some true) .stay htag6 hfillTrue]
    apply config_ext
    · rfl
    · apply Fin.ext; simp [cfg, moveHead]
    · exact hfinalTape
  · intro s hs
    by_cases h1 : s = 0
    · subst s; simpa [hstart, cfg] using hStartNe
    by_cases h2 : s ≤ zeros + 1
    · obtain ⟨r, hr, he⟩ : ∃ r, r ≤ zeros ∧ s = 1 + r :=
        ⟨s - 1, by omega, by omega⟩
      subst s
      rw [hstart, machine.run_add, hdispatch, hback r hr]
      simpa [cfg] using hBackNe
    by_cases h3 : s = zeros + 2
    · subst s; rw [hsTurn]
      simpa [cfg] using hFillNe
    · obtain ⟨r, hr, he⟩ : ∃ r, r ≤ k + 1 ∧ s = zeros + 2 + r :=
        ⟨s - (zeros + 2), by simp [cleanupClock] at hs; omega, by omega⟩
      subst s
      rw [machine.run_add, hsTurn, hfill r hr]
      simpa [cfg] using hFillNe

private theorem true_start_eq {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    startConfig B x w zeros k = cfg B qStart (9 + zeros + k)
      (by unfold tapeLength pairLength
          have hp : 9 + zeros + k < a + m := by
            unfold FixedContentTagGate.physicalSymbol at htrue
            split at htrue
            · assumption
            · contradiction
          omega) (pendingTape B x w k) := by
  have hp : 9 + zeros + k < a + m := by
    unfold FixedContentTagGate.physicalSymbol at htrue
    split at htrue
    · assumption
    · contradiction
  have hc := handoff_from_pending_true_reachable (B := B) x w htag hg hk hkz hprefix htrue
  apply config_ext
  · rfl
  · apply Fin.ext; exact hc.2.1
  · exact hc.2.2.1

private theorem virtual_start_eq {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    startConfig B x w zeros k = cfg B qStart (9 + zeros + k)
      (by unfold tapeLength pairLength; omega) (pendingTape B x w k) := by
  have hc := handoff_from_pending_virtual_reachable (B := B) x w htag hg hk hkz hprefix hvirtual
  apply config_ext
  · rfl
  · apply Fin.ext; exact hc.2.1
  · exact hc.2.2.1

/-- The two internal outcome tags are definitionally distinct. -/
theorem done_tags_distinct : qOne ≠ qVirtual := by decide

/-- Either completed branch is absorbing. -/
theorem done_absorbing {N B : Nat} (c : Config stateCount N B)
    (hc : c.state = qOne ∨ c.state = qVirtual) (s : Nat) : machine.run s c = c := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [UniformTM.run, ih]
      rcases hc with h | h
      · exact machine.stepConfig_accept c (by simpa using h)
      · cases c with
        | mk state head tape =>
          change state = qVirtual at h
          subst state
          apply config_ext
          · simp [UniformTM.stepConfig, UniformTM.step, machine, qVirtual, qOne, qReject, raw]
          · simp [UniformTM.stepConfig, UniformTM.step, machine, qVirtual, qOne, qReject,
              raw, moveHead]
          · funext i
            by_cases hi : i = head <;>
              simp [UniformTM.stepConfig, UniformTM.step, machine, qVirtual, qOne, qReject,
                raw, hi]

private theorem wrong_after_endpoint {N B : Nat} (c : Config stateCount N B)
    (clock : Nat) (qGood qBad : Fin stateCount)
    (hend : (machine.run clock c).state = qGood)
    (habsorb : ∀ d : Config stateCount N B, d.state = qGood → ∀ r, machine.run r d = d)
    (hne : qGood ≠ qBad) (s : Nat) (hclock : clock ≤ s) :
    (machine.run s c).state ≠ qBad := by
  rw [show s = clock + (s - clock) by omega, machine.run_add,
    habsorb _ hend (s - clock), hend]
  exact hne

private theorem wrong_excluded_by_distinct_endpoint {N B : Nat}
    (c : Config stateCount N B) (clock : Nat) (qGood qBad : Fin stateCount)
    (hend : (machine.run clock c).state = qGood)
    (hGood : ∀ d : Config stateCount N B, d.state = qGood → ∀ r, machine.run r d = d)
    (hBad : ∀ d : Config stateCount N B, d.state = qBad → ∀ r, machine.run r d = d)
    (hne : qGood ≠ qBad) (s : Nat) : (machine.run s c).state ≠ qBad := by
  by_cases hs : s ≤ clock
  · intro hbad
    have hdecomp : machine.run clock c = machine.run (clock - s) (machine.run s c) := by
      rw [← machine.run_add]
      congr 1
      omega
    have hfix := hBad (machine.run s c) hbad (clock - s)
    have hstates := congrArg Config.state (hdecomp.trans hfix)
    rw [hend, hbad] at hstates
    exact hne hstates
  · exact wrong_after_endpoint c clock qGood qBad hend hGood hne s (by omega)

/-- Exact true-branch cleanup, strict first outcome, and virtual exclusion. -/
theorem true_cleanup_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let c := startConfig B x w zeros k
    machine.run (cleanupClock zeros k) c =
      ⟨qOne, ⟨6, by
        have hL := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
        unfold tapeLength pairLength
        omega⟩, FixedPairContentMarkerErase.contentTape B x w⟩ ∧
    (∀ s, s < cleanupClock zeros k →
      (machine.run s c).state ≠ qOne ∧ (machine.run s c).state ≠ qVirtual) ∧
    (∀ s, (machine.run s c).state ≠ qVirtual) := by
  have hp : 9 + zeros + k < a + m := by
    unfold FixedContentTagGate.physicalSymbol at htrue
    split at htrue
    · assumption
    · contradiction
  have hs : machine.step qStart
      (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k)) =
      (qBackOne, FixedContentTagGate.physicalSymbol (Fin.append x w)
        (9 + zeros + k), .left) := by
    rw [htrue]
    exact start_true_action
  have hcore := cleanup_branch_exact x w htag hg hk hkz (by omega)
    qBackOne qFillOne qOne hs back_one_some_action back_one_none_action
    fill_one_none_action fill_one_true_action (by decide) (by decide) (by decide)
    (true_start_eq (B := B) x w htag hg hk hkz hprefix htrue)
  refine ⟨hcore.1, ?_, ?_⟩
  · intro s hlt
    exact ⟨hcore.2 s hlt, wrong_excluded_by_distinct_endpoint _ _ qOne qVirtual
      (congrArg Config.state hcore.1)
      (fun d hd r => done_absorbing d (Or.inl hd) r)
      (fun d hd r => done_absorbing d (Or.inr hd) r) done_tags_distinct s⟩
  · intro s
    exact wrong_excluded_by_distinct_endpoint _ _ qOne qVirtual
      (congrArg Config.state hcore.1)
      (fun d hd r => done_absorbing d (Or.inl hd) r)
      (fun d hd r => done_absorbing d (Or.inr hd) r) done_tags_distinct s

/-- Exact virtual-branch cleanup, strict first outcome, and true exclusion. -/
theorem virtual_cleanup_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let c := startConfig B x w zeros k
    machine.run (cleanupClock zeros k) c =
      ⟨qVirtual, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ ∧
    (∀ s, s < cleanupClock zeros k →
      (machine.run s c).state ≠ qOne ∧ (machine.run s c).state ≠ qVirtual) ∧
    (∀ s, (machine.run s c).state ≠ qOne) := by
  have hs : machine.step qStart
      (FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k)) =
      (qBackVirtual, FixedContentTagGate.physicalSymbol (Fin.append x w)
        (9 + zeros + k), .left) := by
    have hv : FixedContentTagGate.physicalSymbol (Fin.append x w)
        (9 + zeros + k) = none := by
      simp [FixedContentTagGate.physicalSymbol, hvirtual]
    rw [hv]
    exact start_virtual_action
  have hcore := cleanup_branch_exact x w htag hg hk hkz (by omega)
    qBackVirtual qFillVirtual qVirtual hs back_virtual_some_action
    back_virtual_none_action fill_virtual_none_action fill_virtual_true_action
    (by decide) (by decide) (by decide)
    (virtual_start_eq (B := B) x w htag hg hk hkz hprefix hvirtual)
  refine ⟨hcore.1, ?_, ?_⟩
  · intro s hlt
    exact ⟨wrong_excluded_by_distinct_endpoint _ _ qVirtual qOne
      (congrArg Config.state hcore.1)
      (fun d hd r => done_absorbing d (Or.inr hd) r)
      (fun d hd r => done_absorbing d (Or.inl hd) r) done_tags_distinct.symm s,
      hcore.2 s hlt⟩
  · intro s
    exact wrong_excluded_by_distinct_endpoint _ _ qVirtual qOne
      (congrArg Config.state hcore.1)
      (fun d hd r => done_absorbing d (Or.inr hd) r)
      (fun d hd r => done_absorbing d (Or.inl hd) r) done_tags_distinct.symm s

theorem true_cleanup_endpoint {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (cleanupClock zeros k) (startConfig B x w zeros k)
    d.state = qOne ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  rw [(true_cleanup_exact (B := B) x w htag hg hk hkz hprefix htrue).1]
  exact ⟨rfl, rfl, rfl⟩

theorem virtual_cleanup_endpoint {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := machine.run (cleanupClock zeros k) (startConfig B x w zeros k)
    d.state = qVirtual ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  rw [(virtual_cleanup_exact (B := B) x w htag hg hk hkz hprefix hvirtual).1]
  exact ⟨rfl, rfl, rfl⟩

/-- No public transition row moves right. -/
theorem no_row_moves_right : ∀ q s, (machine.step q s).2.2 ≠ Move.right := by
  intro q s
  fin_cases q <;> cases s with
  | none => decide
  | some b => cases b <;> decide

/-- Along every trace, the head never increases. -/
theorem head_nonincreasing {N B : Nat} (c : Config stateCount N B) (s : Nat) :
    (machine.run s c).head.val ≤ c.head.val := by
  induction s with
  | zero => exact Nat.le_refl _
  | succ s ih =>
      rw [UniformTM.run]
      change (moveHead (machine.run s c).head
        (machine.step (machine.run s c).state
          ((machine.run s c).tape (machine.run s c).head)).2.2).val ≤ c.head.val
      have hmv := no_row_moves_right (machine.run s c).state
        ((machine.run s c).tape (machine.run s c).head)
      cases hm : (machine.step (machine.run s c).state
          ((machine.run s c).tape (machine.run s c).head)).2.2 with
      | left => exact Nat.le_trans (Nat.sub_le _ _) ih
      | stay => simpa [moveHead, hm] using ih
      | right => exact False.elim (hmv (by simpa using hm))

/-- A trace cannot alter a cell strictly above its initial head. -/
theorem tape_above_head_fixed {N B : Nat} (c : Config stateCount N B) (s : Nat)
    (i : Fin (tapeLength N B)) (hi : c.head.val < i.val) :
    (machine.run s c).tape i = c.tape i := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [UniformTM.run]
      change (if i = (machine.run s c).head then _ else (machine.run s c).tape i) = c.tape i
      rw [if_neg (by
        intro he
        have hle := head_nonincreasing c s
        rw [← he] at hle
        omega)]
      exact ih

/-- The fixed transition table is independent of tape budget. -/
theorem per_step_budget_independent : ∀ q s,
    machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => decide
  | some b => cases b <;> decide

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadPendingCleanup
