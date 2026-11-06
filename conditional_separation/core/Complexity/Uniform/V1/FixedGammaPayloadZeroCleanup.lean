import Complexity.Uniform.V1.FixedGammaPayloadExhausted
import Mathlib.Data.Fintype.Card

set_option linter.unusedTactic false

/-!
# Fixed gamma-payload physical zero cleanup (Part A G2f)

This five-state successor retags the exact absorbing `qExhausted` endpoint; it
does not alter that predecessor row.  It restores the cursor and counter holes
of the last rolling-hole tape, then stops at fixed tag cell 6.  The endpoint is
an internal control handoff only: no all-zero or acceptance semantics, and no
cross-machine total clock, are claimed here.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadZeroCleanup

open PairEncoding
open FixedGammaPayloadRoundStep

abbrev stateCount : Nat := 5
def qScanRight : Fin stateCount := ⟨0, by decide⟩
def qBackTerm : Fin stateCount := ⟨1, by decide⟩
def qFillCounter : Fin stateCount := ⟨2, by decide⟩
def qDone : Fin stateCount := ⟨3, by decide⟩
def qReject : Fin stateCount := ⟨4, by decide⟩

private def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | none => (qBackTerm, some false, .left)
    | some b => (qScanRight, some b, .right)
  | 1 => match s with
    | none => (qFillCounter, some false, .left)
    | some b => (qBackTerm, some b, .left)
  | 2 => match s with
    | none => (qFillCounter, some false, .left)
    | some true => (qDone, some true, .stay)
    | some false => (qReject, some false, .stay)
  | 3 => (qDone, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qScanRight
  accept := qDone
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

def cleanupClock (zeros : Nat) : Nat := 3 * zeros + 3

def retag {N B : Nat}
    (c : Config FixedGammaPayloadRoundStep.stateCount N B) : Config stateCount N B :=
  ⟨qScanRight, c.head, c.tape⟩

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : Config stateCount (pairLength a m) B :=
  retag (FixedGammaPayloadRoundStep.machine.run
    (FixedGammaPayloadExhausted.exhaustedClock zeros)
    (FixedGammaPayloadRoundStep.startConfig B x w zeros))

/-- All 15 state/symbol rows and the fixed resource pins. -/
theorem table_and_resource_pins :
    (∀ s, machine.step qScanRight s = match s with
      | none => (qBackTerm, some false, .left)
      | some b => (qScanRight, some b, .right)) ∧
    (∀ s, machine.step qBackTerm s = match s with
      | none => (qFillCounter, some false, .left)
      | some b => (qBackTerm, some b, .left)) ∧
    (∀ s, machine.step qFillCounter s = match s with
      | none => (qFillCounter, some false, .left)
      | some true => (qDone, some true, .stay)
      | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qDone s = (qDone, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 5 ∧ machine.start = qScanRight ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 15 := by
  refine ⟨fun s => by cases s with | none => decide | some b => cases b <;> decide,
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

private theorem scan_some_action (b : Bool) : machine.step qScanRight (some b) =
    (qScanRight, some b, .right) := by cases b <;> decide
private theorem scan_none_action : machine.step qScanRight none =
    (qBackTerm, some false, .left) := by decide
private theorem back_some_action (b : Bool) : machine.step qBackTerm (some b) =
    (qBackTerm, some b, .left) := by cases b <;> decide
private theorem back_none_action : machine.step qBackTerm none =
    (qFillCounter, some false, .left) := by decide
private theorem fill_none_action : machine.step qFillCounter none =
    (qFillCounter, some false, .left) := by decide
private theorem fill_true_action : machine.step qFillCounter (some true) =
    (qDone, some true, .stay) := by decide

private theorem content_at {a m B j : Nat} (x : Bitstring a) (w : Bitstring m)
    (hj : j < a + m) :
    FixedPairContentMarkerErase.contentTape B x w
      ⟨j, by (try unfold tapeLength pairLength); omega⟩ = some ((Fin.append x w) ⟨j, hj⟩) := by
  simp [FixedPairContentMarkerErase.contentTape, hj]

/-- Retagging is an exact handoff from the predecessor's absorbing endpoint. -/
theorem handoff_from_exhausted_reachable {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let p := FixedGammaPayloadRoundStep.machine.run
      (FixedGammaPayloadExhausted.exhaustedClock zeros)
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)
    let c := startConfig B x w zeros
    p.state = FixedGammaPayloadRoundStep.qExhausted ∧ p.head.val = 8 + zeros ∧
      p.tape = roundTape B x w zeros zeros ∧ c = retag p := by
  dsimp [startConfig]
  exact ⟨(FixedGammaPayloadExhausted.exhausted_reachable x w htag hg hzero hprefix).1,
    (FixedGammaPayloadExhausted.exhausted_reachable x w htag hg hzero hprefix).2.1,
    (FixedGammaPayloadExhausted.exhausted_reachable x w htag hg hzero hprefix).2.2, rfl⟩

/-- Arithmetic bounds used to type the cleanup phase configurations. -/
theorem cleanup_arithmetic_bounds {a m B zeros : Nat}
    (hp : 8 + 2 * zeros < a + m) :
    0 < 6 ∧ 8 + 2 * zeros < tapeLength (pairLength a m) B := by
  unfold tapeLength pairLength
  omega

/-- The only initial differences from literal content are the rolling holes. -/
theorem initial_footprint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hcounter : ¬ (8 ≤ i.val ∧ i.val < 8 + zeros))
    (hcursor : i.val ≠ 8 + 2 * zeros) :
    roundTape B x w zeros zeros i = FixedPairContentMarkerErase.contentTape B x w i :=
  roundTape_footprint x w i h7 hcounter (by (try unfold tapeLength pairLength); omega)

set_option maxHeartbeats 800000 in
/-- Exact local execution, strict first `qDone`, and literal tape restoration. -/
theorem cleanup_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let c := startConfig B x w zeros
    machine.run (cleanupClock zeros) c =
      ⟨qDone, ⟨6, by
        rcases FixedContentTagGate.tag_contract (Fin.append x w) with
          ⟨_, _, _, _, _, _, _, _, _, hlenTag⟩
        have hL := hlenTag htag
        unfold tapeLength pairLength
        omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ ∧
    (∀ s, s < cleanupClock zeros → (machine.run s c).state ≠ qDone) := by
  let base := FixedPairContentMarkerErase.contentTape B x w
  let t0 := roundTape B x w zeros zeros
  let t1 := fun i : Fin (tapeLength (pairLength a m) B) =>
    if i.val = 8 + 2 * zeros then some false else t0 i
  let t2 := fun r (i : Fin (tapeLength (pairLength a m) B)) =>
    if 7 + zeros - r ≤ i.val ∧ i.val ≤ 7 + zeros then some false else t1 i
  have hp0 := hprefix (9 + zeros) (by (try unfold tapeLength pairLength); omega) (by (try unfold tapeLength pairLength); omega)
  have hphysical : 9 + zeros < a + m := by
    unfold FixedContentTagGate.physicalSymbol at hp0
    split at hp0
    · assumption
    · contradiction
  have hplast := hprefix (8 + 2 * zeros) (by (try unfold tapeLength pairLength); omega) (by (try unfold tapeLength pairLength); omega)
  have hlast : 8 + 2 * zeros < a + m := by
    unfold FixedContentTagGate.physicalSymbol at hplast
    split at hplast
    · assumption
    · contradiction
  have hlen : 8 + 2 * zeros < tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength
    omega
  have hstart : startConfig B x w zeros =
      cfg B qScanRight (8 + zeros) (by (try unfold tapeLength pairLength); omega) t0 := by
    have hc0 := handoff_from_exhausted_reachable (B := B) x w htag hg hzero hprefix
    apply config_ext
    · rfl
    · apply Fin.ext
      exact hc0.2.1
    · simpa [t0] using hc0.2.2.1
  have hgamma := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hscan (r : Nat) (hr : r ≤ zeros) :
      machine.run r (cfg B qScanRight (8 + zeros) (by (try unfold tapeLength pairLength); omega) t0) =
        cfg B qScanRight (8 + zeros + r) (by (try unfold tapeLength pairLength); omega) t0 := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by (try unfold tapeLength pairLength); omega)]
        have hj : 8 + zeros + r < a + m := by (try unfold tapeLength pairLength); omega
        have hct := content_at (B := B) x w hj
        have hread : ∃ b, t0 ⟨8 + zeros + r, by (try unfold tapeLength pairLength); omega⟩ = some b := by
          refine ⟨(Fin.append x w) ⟨8 + zeros + r, hj⟩, ?_⟩
          rw [show t0 ⟨8 + zeros + r, by (try unfold tapeLength pairLength); omega⟩ =
              FixedPairContentMarkerErase.contentTape B x w
                ⟨8 + zeros + r, by (try unfold tapeLength pairLength); omega⟩ by
            simp [t0, roundTape]; omega]
          exact hct
        obtain ⟨b, hb⟩ := hread
        rw [step_keep qScanRight qScanRight _ t0 (some b) .right hb
          (scan_some_action b)]
        apply config_ext <;> try rfl
        apply Fin.ext
        simp [cfg, moveHead, show 8 + zeros + r + 1 <
          tapeLength (pairLength a m) B by (try unfold tapeLength pairLength); omega]
        omega
  have hcursor : t0 ⟨8 + 2 * zeros, hlen⟩ = none := by
    simp [t0, roundTape]
    omega
  have hturn : machine.run 1 (cfg B qScanRight (8 + 2 * zeros) hlen t0) =
      cfg B qBackTerm (7 + 2 * zeros) (by (try unfold tapeLength pairLength); omega) t1 := by
    simp only [UniformTM.run]
    rw [step_eq _ qBackTerm (some false) .left (by
      simpa [cfg, hcursor] using scan_none_action)]
    apply config_ext
    · rfl
    · apply Fin.ext; simp [cfg, moveHead]
    · funext i
      simp only [cfg]
      by_cases hi : i.val = 8 + 2 * zeros
      · have he : i = ⟨8 + 2 * zeros, hlen⟩ := Fin.ext hi
        subst i
        simp [t1]
      · have hn : i ≠ (⟨8 + 2 * zeros, hlen⟩ :
            Fin (tapeLength (pairLength a m) B)) := by
          intro he; exact hi (congrArg Fin.val he)
        simp [t1, hi, hn]
  have hback (r : Nat) (hr : r ≤ zeros) :
      machine.run r (cfg B qBackTerm (7 + 2 * zeros) (by (try unfold tapeLength pairLength); omega) t1) =
        cfg B qBackTerm (7 + 2 * zeros - r) (by (try unfold tapeLength pairLength); omega) t1 := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by (try unfold tapeLength pairLength); omega)]
        have hj : 7 + 2 * zeros - r < a + m := by (try unfold tapeLength pairLength); omega
        have hct := content_at (B := B) x w hj
        have hread : ∃ b, t1 ⟨7 + 2 * zeros - r, by (try unfold tapeLength pairLength); omega⟩ = some b := by
          refine ⟨(Fin.append x w) ⟨7 + 2 * zeros - r, hj⟩, ?_⟩
          rw [show t1 ⟨7 + 2 * zeros - r, by (try unfold tapeLength pairLength); omega⟩ =
              FixedPairContentMarkerErase.contentTape B x w
                ⟨7 + 2 * zeros - r, by (try unfold tapeLength pairLength); omega⟩ by
            simp [t1, t0, roundTape,
              show 7 + 2 * zeros - r ≠ 8 + 2 * zeros by omega,
              show 7 + 2 * zeros - r ≠ 7 by omega,
              show ¬(8 ≤ 7 + 2 * zeros - r ∧
                7 + 2 * zeros - r < 8 + zeros) by omega,
              show 7 + 2 * zeros - r ≠ 8 + zeros + zeros by omega]]
          exact hct
        obtain ⟨b, hb⟩ := hread
        rw [step_keep qBackTerm qBackTerm _ t1 (some b) .left hb (back_some_action b)]
        apply config_ext <;> try rfl
  have hcounterHole : t1 ⟨7 + zeros, by (try unfold tapeLength pairLength); omega⟩ = none := by
    simp [t1, t0, roundTape, show 7 + zeros ≠ 8 + 2 * zeros by omega,
      show 8 ≤ 7 + zeros by omega, show 7 + zeros < 8 + zeros by omega]
  have hcounterStart : machine.run 1 (cfg B qBackTerm (7 + zeros) (by (try unfold tapeLength pairLength); omega) t1) =
      cfg B qFillCounter (6 + zeros) (by (try unfold tapeLength pairLength); omega) (t2 0) := by
    simp only [UniformTM.run]
    rw [step_eq _ qFillCounter (some false) .left (by
      simpa [cfg, hcounterHole] using back_none_action)]
    apply config_ext
    · rfl
    · apply Fin.ext; simp [cfg, moveHead]
    · funext i
      simp only [cfg]
      by_cases hi : i.val = 7 + zeros
      · have he : i = (⟨7 + zeros, by (try unfold tapeLength pairLength); omega⟩ :
            Fin (tapeLength (pairLength a m) B)) := Fin.ext hi
        simp [t2, he]
      · have hn : i ≠ (⟨7 + zeros, by (try unfold tapeLength pairLength); omega⟩ :
            Fin (tapeLength (pairLength a m) B)) := by
          intro he; exact hi (congrArg Fin.val he)
        simp [t2, hn]
        omega
  have hfill (r : Nat) (hr : r ≤ zeros) :
      machine.run r (cfg B qFillCounter (6 + zeros) (by (try unfold tapeLength pairLength); omega) (t2 0)) =
        cfg B qFillCounter (6 + zeros - r) (by (try unfold tapeLength pairLength); omega) (t2 r) := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by (try unfold tapeLength pairLength); omega)]
        have hhole : t2 r ⟨6 + zeros - r, by (try unfold tapeLength pairLength); omega⟩ = none := by
          have hout : ¬(7 + zeros - r ≤ 6 + zeros - r ∧
              6 + zeros - r ≤ 7 + zeros) := by omega
          change (if 7 + zeros - r ≤ 6 + zeros - r ∧ 6 + zeros - r ≤ 7 + zeros
            then some false else t1 ⟨6 + zeros - r, _⟩) = none
          rw [if_neg hout]
          simp [t1, t0, show 6 + zeros - r ≠ 8 + 2 * zeros by omega]
          by_cases h7 : 6 + zeros - r = 7
          · simp [roundTape, h7]
          · have h8 : 8 ≤ 6 + zeros - r := by omega
            have hh : 6 + zeros - r < 8 + zeros := by omega
            simp [roundTape, h7, h8, hh]
        rw [step_eq _ qFillCounter (some false) .left (by
          simpa [cfg, hhole] using fill_none_action)]
        apply config_ext
        · rfl
        · apply Fin.ext; simp [cfg, moveHead]; omega
        · funext i
          simp only [cfg]
          by_cases hi : i.val = 6 + zeros - r
          · have he : i = (⟨6 + zeros - r, by (try unfold tapeLength pairLength); omega⟩ :
                Fin (tapeLength (pairLength a m) B)) := Fin.ext hi
            rw [if_pos he]
            simp [t2]
            omega
          · have hn : i ≠ (⟨6 + zeros - r, by (try unfold tapeLength pairLength); omega⟩ :
                Fin (tapeLength (pairLength a m) B)) := by
              intro he; exact hi (congrArg Fin.val he)
            simp only [if_neg hn]
            simp only [t2]
            split_ifs with hold hnew
            · rfl
            · exfalso; omega
            · exfalso; omega
            · rfl
  have htag6 : t2 zeros ⟨6, by (try unfold tapeLength pairLength); omega⟩ = some true := by
    rcases FixedContentTagGate.tag_contract (Fin.append x w) with
      ⟨_, _, _, _, _, _, _, _, hc, htagLen⟩
    have hlenContent := htagLen htag
    have hb := hc.mp htag
    have hbit : (Fin.append x w) ⟨6, by (try unfold tapeLength pairLength); omega⟩ = true := by
      simpa [FixedContentTagGate.expectedTagBit, FixedContentTagGate.physicalSymbol,
        show 6 < a + m by (try unfold tapeLength pairLength); omega] using hb ⟨6, by decide⟩
    have hct := content_at (B := B) x w (show 6 < a + m by (try unfold tapeLength pairLength); omega)
    simp [t2, t1, t0, roundTape, hct, hbit,
      show 6 ≠ 8 + 2 * zeros by omega, show 6 ≠ 8 + zeros + zeros by omega,
      show 6 ≠ 7 by omega]
  have hfinalTape : t2 zeros = base := by
    funext i
    by_cases hrepair : 7 ≤ i.val ∧ i.val ≤ 7 + zeros
    · have hj : i.val < a + m := by (try unfold tapeLength pairLength); omega
      have hct := content_at (B := B) x w hj
      by_cases hi7 : i.val = 7
      · rcases FixedContentTagGate.tag_contract (Fin.append x w) with
          ⟨_, _, _, _, _, _, _, _, hc7, htagLen⟩
        have hlenContent := htagLen htag
        have hb := hc7.mp htag
        have hbit : (Fin.append x w) ⟨i.val, hj⟩ = false := by
          have h := hb ⟨7, by decide⟩
          have hfixed : (Fin.append x w) ⟨7, by (try unfold tapeLength pairLength); omega⟩ = false := by
            simpa [FixedContentTagGate.expectedTagBit,
              FixedContentTagGate.physicalSymbol, show 7 < a + m by (try unfold tapeLength pairLength); omega] using h
          simpa [hi7] using hfixed
        simp [t2, base, hrepair, hct, hbit]
      · have hi8 : 8 ≤ i.val := by (try unfold tapeLength pairLength); omega
        obtain ⟨k, hk, he⟩ : ∃ k, k < zeros ∧ i.val = 8 + k := by
          refine ⟨i.val - 8, by (try unfold tapeLength pairLength); omega, by (try unfold tapeLength pairLength); omega⟩
        have hz := hgamma.2.2 k hk
        have hbit : (Fin.append x w) ⟨i.val, hj⟩ = false := by
          have hfixed : (Fin.append x w) ⟨8 + k, by (try unfold tapeLength pairLength); omega⟩ = false := by
            simpa [FixedContentTagGate.physicalSymbol,
              show 8 + k < a + m by (try unfold tapeLength pairLength); omega] using hz
          simpa [he] using hfixed
        simp [t2, base, hrepair, hct, hbit]
    · by_cases hcur : i.val = 8 + 2 * zeros
      · have hj : i.val < a + m := by (try unfold tapeLength pairLength); omega
        have hct := content_at (B := B) x w hj
        have hp := hprefix i.val (by (try unfold tapeLength pairLength); omega) (by (try unfold tapeLength pairLength); omega)
        have hb : (Fin.append x w) ⟨i.val, hj⟩ = false := by
          simpa [FixedContentTagGate.physicalSymbol, hj] using hp
        have hbcur : (Fin.append x w) ⟨8 + 2 * zeros, by (try unfold tapeLength pairLength); omega⟩ = false := by
          simpa [hcur] using hb
        simp [t2, t1, base, hcur, hct, hbcur]
      · simp [t2, t1, t0, roundTape, base, hrepair, hcur]
        omega
  have hsStage : machine.run (zeros + 1) (startConfig B x w zeros) =
      cfg B qBackTerm (7 + 2 * zeros) (by (try unfold tapeLength pairLength); omega) t1 := by
    rw [machine.run_add, hstart, hscan zeros (by omega)]
    have heq : cfg B qScanRight (8 + zeros + zeros) (by omega) t0 =
        cfg B qScanRight (8 + 2 * zeros) hlen t0 := by
      apply config_ext <;> try rfl
      apply Fin.ext; simp [cfg]; omega
    rw [heq, hturn]
  have hbStage : machine.run (2 * zeros + 2) (startConfig B x w zeros) =
      cfg B qFillCounter (6 + zeros) (by (try unfold tapeLength pairLength); omega) (t2 0) := by
    rw [show 2 * zeros + 2 = (zeros + 1) + (zeros + 1) by omega,
      machine.run_add, hsStage, machine.run_add, hback zeros (by omega)]
    have heq : cfg B qBackTerm (7 + 2 * zeros - zeros) (by omega) t1 =
        cfg B qBackTerm (7 + zeros) (by omega) t1 := by
      apply config_ext <;> try rfl
      apply Fin.ext; simp [cfg]; omega
    rw [heq, hcounterStart]
  have hend : machine.run (cleanupClock zeros) (startConfig B x w zeros) =
      cfg B qDone 6 (by (try unfold tapeLength pairLength); omega) base := by
    have hf : machine.run (3 * zeros + 2) (startConfig B x w zeros) =
        cfg B qFillCounter 6 (by (try unfold tapeLength pairLength); omega) (t2 zeros) := by
      rw [show 3 * zeros + 2 = (2 * zeros + 2) + zeros by (try unfold tapeLength pairLength); omega,
        machine.run_add, hbStage, hfill zeros (by omega)]
      apply config_ext <;> try rfl
      apply Fin.ext
      simp [cfg]
    rw [cleanupClock, show 3 * zeros + 3 = (3 * zeros + 2) + 1 by (try unfold tapeLength pairLength); omega,
      machine.run_add, hf]
    simp only [UniformTM.run]
    rw [step_keep qFillCounter qDone _ (t2 zeros) (some true) .stay htag6 fill_true_action]
    apply config_ext <;> try rfl
    exact hfinalTape
  refine ⟨?_, ?_⟩
  · simpa [cfg, base] using hend
  · intro s hs
    by_cases h1 : s ≤ zeros
    · rw [hstart, hscan s h1]
      change qScanRight ≠ qDone
      decide
    by_cases h2 : s ≤ 2 * zeros + 1
    · obtain ⟨r, hr, he⟩ : ∃ r, r ≤ zeros ∧ s = zeros + 1 + r :=
        ⟨s - (zeros + 1), by (try unfold tapeLength pairLength); omega, by (try unfold tapeLength pairLength); omega⟩
      subst s
      rw [machine.run_add, hsStage, hback r hr]
      change qBackTerm ≠ qDone
      decide
    by_cases h3 : s = 2 * zeros + 2
    · subst s
      rw [hbStage]
      change qFillCounter ≠ qDone
      decide
    · obtain ⟨r, hr, he⟩ : ∃ r, r ≤ zeros ∧ s = 2 * zeros + 2 + r :=
        ⟨s - (2 * zeros + 2), by simp [cleanupClock] at hs; omega, by (try unfold tapeLength pairLength); omega⟩
      subst s
      rw [machine.run_add, hbStage, hfill r hr]
      change qFillCounter ≠ qDone
      decide

/-- Typed endpoint projection. -/
theorem cleanup_endpoint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (cleanupClock zeros) (startConfig B x w zeros)
    d.state = qDone ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have h := (cleanup_exact (B := B) x w htag hg hzero hprefix).1
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-- The fixed transition table is independent of tape budget. -/
theorem per_step_budget_independent : ∀ q s,
    machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => decide
  | some b => cases b <;> decide

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadZeroCleanup
