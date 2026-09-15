import Complexity.Uniform.V1.FixedGammaPayloadCursorCore
import Mathlib.Data.Fintype.Card

/-!
# Fixed gamma-payload arbitrary-round step (Part A G2c)

This successor preserves `FixedGammaPayloadCursorCore` and its absorbing
`qNextFalse` ABI.  It retags that handoff and executes one physical-false
round of the rolling-hole representation for arbitrary `1 ≤ k < zeros`.
The false arm returns to this machine's own start state.  The other branches
are only distinct internal exit tags.  `qOnePending` is the public accept state
as a local ABI choice only; no semantic acceptance or cleanup meaning is
claimed here, and this file contains no whole-payload induction.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadRoundStep

open PairEncoding

abbrev stateCount : Nat := 11
def qStart : Fin stateCount := ⟨0, by decide⟩
def qBackPayload : Fin stateCount := ⟨1, by decide⟩
def qBackCounter : Fin stateCount := ⟨2, by decide⟩
def qSpend : Fin stateCount := ⟨3, by decide⟩
def qSeekTerm : Fin stateCount := ⟨4, by decide⟩
def qSeekHole : Fin stateCount := ⟨5, by decide⟩
def qRead : Fin stateCount := ⟨6, by decide⟩
def qExhausted : Fin stateCount := ⟨7, by decide⟩
def qOnePending : Fin stateCount := ⟨8, by decide⟩
def qVirtualPending : Fin stateCount := ⟨9, by decide⟩
def qReject : Fin stateCount := ⟨10, by decide⟩

private def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | none => (qBackPayload, none, .left)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some false => (qBackPayload, some false, .left)
    | some true => (qBackCounter, some true, .left)
    | none => (qReject, none, .stay)
  | 2 => match s with
    | some false => (qBackCounter, some false, .left)
    | none => (qSpend, none, .right)
    | some true => (qReject, some true, .stay)
  | 3 => match s with
    | some false => (qSeekTerm, none, .right)
    | some true => (qExhausted, some true, .stay)
    | none => (qReject, none, .stay)
  | 4 => match s with
    | some false => (qSeekTerm, some false, .right)
    | some true => (qSeekHole, some true, .right)
    | none => (qReject, none, .stay)
  | 5 => match s with
    | some false => (qSeekHole, some false, .right)
    | none => (qRead, some false, .right)
    | some true => (qReject, some true, .stay)
  | 6 => match s with
    | some false => (qStart, none, .stay)
    | some true => (qOnePending, some true, .stay)
    | none => (qVirtualPending, none, .stay)
  | 7 => (qExhausted, s, .stay)
  | 8 => (qOnePending, s, .stay)
  | 9 => (qVirtualPending, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qOnePending
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

def retag {N B : Nat} (c : Config FixedGammaPayloadCursorCore.stateCount N B) :
    Config stateCount N B := ⟨qStart, c.head, c.tape⟩

def coreTime (zeros : Nat) : Nat := 2 * zeros + 4
def roundCost (zeros : Nat) : Nat := 2 * zeros + 4

/-- Exact machine-neutral rolling-hole tape after `k` false payload reads. -/
def roundTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros k : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = 7 ∨ (8 ≤ i.val ∧ i.val < 8 + k) ∨ i.val = 8 + zeros + k then none
  else FixedPairContentMarkerErase.contentTape B x w i

/-- Machine-neutral boundary geometry; only the state equality is machine-specific. -/
def RoundInvariant {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros k : Nat) (c : Config stateCount (pairLength a m) B) : Prop :=
  c.state = qStart ∧ c.head.val = 8 + zeros + k ∧ c.tape = roundTape B x w zeros k

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : Config stateCount (pairLength a m) B :=
  retag (FixedGammaPayloadCursorCore.machine.run (coreTime zeros)
    (FixedGammaPayloadCursorCore.startConfig B x w))

/-- Full fixed transition table and resource pins. -/
theorem table_and_resource_pins :
    (∀ s, machine.step qStart s = match s with
      | none => (qBackPayload, none, .left) | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.step qBackPayload s = match s with
      | some false => (qBackPayload, some false, .left)
      | some true => (qBackCounter, some true, .left) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qBackCounter s = match s with
      | some false => (qBackCounter, some false, .left)
      | none => (qSpend, none, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qSpend s = match s with
      | some false => (qSeekTerm, none, .right)
      | some true => (qExhausted, some true, .stay) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qSeekTerm s = match s with
      | some false => (qSeekTerm, some false, .right)
      | some true => (qSeekHole, some true, .right) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qSeekHole s = match s with
      | some false => (qSeekHole, some false, .right)
      | none => (qRead, some false, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qRead s = match s with
      | some false => (qStart, none, .stay)
      | some true => (qOnePending, some true, .stay)
      | none => (qVirtualPending, none, .stay)) ∧
    (∀ s, machine.step qExhausted s = (qExhausted, s, .stay)) ∧
    (∀ s, machine.step qOnePending s = (qOnePending, s, .stay)) ∧
    (∀ s, machine.step qVirtualPending s = (qVirtualPending, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 11 ∧ machine.start = qStart ∧ machine.accept = qOnePending ∧
    machine.reject = qReject ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 33 := by
  refine ⟨fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
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

/-- The core's published physical-false theorem is the real `k = 1` handoff. -/
theorem handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (hfalse : (Fin.append x w) ⟨9 + zeros, hp⟩ = false) :
    RoundInvariant B x w zeros 1 (startConfig B x w zeros) := by
  have h := FixedGammaPayloadCursorCore.first_physical_false_exact
    (B := B) x w htag hg hzero hp hfalse
  refine ⟨rfl, ?_, ?_⟩
  · exact h.2.1.trans (by omega)
  · change (FixedGammaPayloadCursorCore.machine.run (coreTime zeros)
      (FixedGammaPayloadCursorCore.startConfig B x w)).tape = _
    change (FixedGammaPayloadCursorCore.machine.run (2 * zeros + 4)
      (FixedGammaPayloadCursorCore.startConfig B x w)).tape = _
    rw [h.2.2]
    funext i
    simp only [FixedGammaPayloadCursorCore.nextTape, roundTape]
    by_cases h7 : i.val = 7 <;> by_cases h8 : i.val = 8 <;>
      by_cases hc : i.val = 9 + zeros <;> simp [h7, h8, hc] <;> omega

/-- Arithmetic bounds ensuring the round's boundary moves are physical and
unclamped. -/
theorem round_no_clamp_facts {a m B zeros k : Nat}
    (_hk : 1 ≤ k) (_hkz : k < zeros) (hp : 9 + zeros + k < a + m) :
    0 < 8 ∧ 8 + k < tapeLength (pairLength a m) B ∧
    9 + zeros + k < tapeLength (pairLength a m) B := by
  unfold tapeLength pairLength
  omega

/-- Outside marker 7, the spent counter prefix, and the current cursor hole,
the invariant tape is literally the predecessor content tape. -/
theorem roundTape_footprint {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hcounter : ¬ (8 ≤ i.val ∧ i.val < 8 + k)) (hcursor : i.val ≠ 8 + zeros + k) :
    roundTape B x w zeros k i = FixedPairContentMarkerErase.contentTape B x w i := by
  simp [roundTape, h7, hcounter, hcursor]

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
private theorem read_false_action : machine.step qRead (some false) =
    (qStart, none, .stay) := by decide

set_option maxHeartbeats 800000 in
/-- One exact physical-false round.  Its hypotheses expose all physical reads;
the fixed transition function receives neither `k` nor `zeros` as advice. -/
theorem round_false_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros) (hp : 9 + zeros + k < a + m)
    (hfalse : (Fin.append x w) ⟨9 + zeros + k, hp⟩ = false)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B)
    (hc : RoundInvariant B x w zeros k c) :
    RoundInvariant B x w zeros (k + 1) (machine.run (roundCost zeros) c) := by
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
  have hnewRead : t2 ⟨9 + zeros + k, hlen⟩ = some false := by
    have hct := content_at (B := B) x w hp
    simp [t2, t1, t0, roundTape, hct, hfalse]
    omega
  have hfinal : machine.run 1 (cfg B qRead (9 + zeros + k) hlen t2) =
      cfg B qStart (9 + zeros + k) hlen (roundTape B x w zeros (k + 1)) := by
    simp only [UniformTM.run]
    rw [step_eq _ qStart none .stay (by simpa [cfg, hnewRead] using read_false_action)]
    apply config_ext <;> try rfl
    funext i
    simp only [cfg]
    by_cases hfin : i = (⟨9 + zeros + k, hlen⟩ :
        Fin (tapeLength (pairLength a m) B))
    · rw [hfin, if_pos rfl]
      simp [roundTape, show 9 + zeros + k = 8 + zeros + (k + 1) by omega]
    · rw [if_neg hfin]
      have hi : i.val ≠ 9 + zeros + k := by
        intro h; exact hfin (Fin.ext h)
      simp only [t2, t1, t0, roundTape]
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
        by_cases hznew : 8 ≤ i.val ∧ i.val < 8 + (k + 1) <;>
        by_cases hnew : i.val = 8 + zeros + (k + 1) <;>
          simp [hsp, hold, h7, hz, hznew, hnew] <;> omega
  change RoundInvariant B x w zeros (k + 1) (machine.run (2 * zeros + 4) c)
  rw [show 2 * zeros + 4 = 1 + (k + (zeros - k + 1 + (1 + (zeros - k + (k + 1))))) by omega,
    machine.run_add, hstart,
    show k + (zeros - k + 1 + (1 + (zeros - k + (k + 1)))) =
      k + ((zeros - k + 1) + (1 + ((zeros - k) + (k + 1)))) by omega,
    machine.run_add, htoCounter, machine.run_add, htoSpend, machine.run_add, hspend,
    machine.run_add, htoHole, machine.run_add, htoRead, hfinal]
  refine ⟨rfl, ?_, rfl⟩
  simp [cfg]
  omega

/-- The first genuinely iterated consequence: core round one followed by this
successor machine's exact physical-false round reaches boundary `k = 2`. -/
theorem second_round_reachable {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hp1 : 9 + zeros < a + m)
    (hfalse1 : (Fin.append x w) ⟨9 + zeros, hp1⟩ = false)
    (hp2 : 10 + zeros < a + m)
    (hfalse2 : (Fin.append x w) ⟨10 + zeros, hp2⟩ = false) :
    RoundInvariant B x w zeros 2
      (machine.run (roundCost zeros) (startConfig B x w zeros)) := by
  apply round_false_exact x w hg (k := 1) (by omega) (by omega) (by omega) (by
      have he : (⟨10 + zeros, hp2⟩ : Fin (a + m)) = ⟨9 + zeros + 1, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      simpa only [← he] using hfalse2)
    (fun j hlo hhi => by
      have : j = 9 + zeros := by omega
      subst j
      simpa [FixedContentTagGate.physicalSymbol, hp1] using hfalse1)
  exact handoff_exact x w htag hg (by omega) hp1 hfalse1

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadRoundStep
