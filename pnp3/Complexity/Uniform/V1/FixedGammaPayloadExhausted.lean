import Complexity.Uniform.V1.FixedGammaPayloadRoundDriver

/-!
# Fixed gamma-payload exhausted branch (Part A G2e)

This proof-only module executes the final boundary of
`FixedGammaPayloadRoundDriver`.  All clocks here are local to the fixed
successor machine: no predecessor-machine time is folded into them.

The endpoint `qExhausted` is an absorbing internal control tag only.  The
rolling-hole tape is left exactly as it was at the last boundary; in
particular, this module proves neither cleanup nor a semantic all-zero verdict.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadExhausted

open PairEncoding
open FixedGammaPayloadRoundStep
open FixedGammaPayloadRoundDriver

/-- Exact successor-local tail from the last false boundary to `qExhausted`. -/
def exhaustedTail (zeros : Nat) : Nat := zeros + 3

/-- Successor-local time from this successor's start configuration. -/
def exhaustedClock (zeros : Nat) : Nat :=
  boundaryClock zeros zeros + exhaustedTail zeros

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
      (moveHead ⟨j, hj⟩ mv).isLt t := by
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
private theorem backCounter_none_action : machine.step qBackCounter none =
    (qSpend, none, .right) := by decide
private theorem spend_true_action : machine.step qSpend (some true) =
    (qExhausted, some true, .stay) := by decide
private theorem exhausted_action (s : Option Bool) : machine.step qExhausted s =
    (qExhausted, s, .stay) := by
  cases s with
  | none => decide
  | some b => cases b <;> decide

/-- The exact phase trace of the exhausted tail.  This pins every control state
needed both for the endpoint and for strict first-arrival timing. -/
theorem exhausted_tail_trace {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B)
    (hc : RoundInvariant B x w zeros zeros c) :
    (∀ r, r ≤ zeros - 1 → (machine.run (1 + r) c).state = qBackPayload) ∧
    (machine.run (zeros + 1) c).state = qBackCounter ∧
    (machine.run (zeros + 2) c).state = qSpend ∧
    let d := machine.run (exhaustedTail zeros) c
    d.state = qExhausted ∧ d.head.val = 8 + zeros ∧
      d.tape = roundTape B x w zeros zeros := by
  let t := roundTape B x w zeros zeros
  have hp0 := hprefix (9 + zeros) (by omega) (by omega)
  have hphys : 9 + zeros < a + m := by
    unfold FixedContentTagGate.physicalSymbol at hp0
    split at hp0
    · assumption
    · contradiction
  have hplast := hprefix (8 + 2 * zeros) (by omega) (by omega)
  have hphysicalLast : 8 + 2 * zeros < a + m := by
    unfold FixedContentTagGate.physicalSymbol at hplast
    split at hplast
    · assumption
    · contradiction
  have hlen : 8 + 2 * zeros < tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength
    omega
  have hstart : machine.run 1 c = cfg B qBackPayload (7 + 2 * zeros) (by omega) t := by
    rcases hc with ⟨hs, hh, ht⟩
    have heq : c = cfg B qStart (8 + 2 * zeros) (by omega) t := by
      apply config_ext
      · simpa [cfg] using hs
      · apply Fin.ext
        change c.head.val = 8 + 2 * zeros
        omega
      · simpa [t, cfg] using ht
    rw [heq]
    simp only [UniformTM.run]
    rw [step_keep qStart qBackPayload _ t none .left (by
      simp [t, roundTape, show 8 + 2 * zeros = 8 + zeros + zeros by omega])
      start_none_action]
    apply config_ext <;> try rfl
    apply Fin.ext
    simp [cfg, moveHead]
  have hback (r : Nat) (hr : r ≤ zeros - 1) :
      machine.run r (cfg B qBackPayload (7 + 2 * zeros) (by omega) t) =
        cfg B qBackPayload (7 + 2 * zeros - r) (by omega) t := by
    induction r with
    | zero => rfl
    | succ r ih =>
        have hr' : r + 2 ≤ zeros := by omega
        rw [UniformTM.run, ih (by omega)]
        have hp := hprefix (7 + 2 * zeros - r) (by omega) (by omega)
        have hb : (Fin.append x w) ⟨7 + 2 * zeros - r, by omega⟩ = false := by
          simpa [FixedContentTagGate.physicalSymbol,
            show 7 + 2 * zeros - r < a + m by omega] using hp
        have hct := content_at (B := B) x w
          (show 7 + 2 * zeros - r < a + m by omega)
        have hread : t ⟨7 + 2 * zeros - r, by omega⟩ = some false := by
          simp [t, roundTape, show 7 + 2 * zeros - r ≠ 7 by omega,
            show ¬(8 ≤ 7 + 2 * zeros - r ∧ 7 + 2 * zeros - r < 8 + zeros) by omega,
            show 7 + 2 * zeros - r ≠ 8 + zeros + zeros by omega, hct, hb]
        rw [step_keep qBackPayload qBackPayload _ t (some false) .left hread
          backPayload_false_action]
        apply config_ext <;> try rfl
  have hterm : t ⟨8 + zeros, by omega⟩ = some true := by
    have hgamma := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
    have hct := content_at (B := B) x w hgamma.1
    have hb : (Fin.append x w) ⟨8 + zeros, hgamma.1⟩ = true := by
      simpa [FixedContentTagGate.physicalSymbol, hgamma.1] using hgamma.2.1
    simp [t, roundTape, hct, hb]
    omega
  have htoCounter : machine.run zeros
      (cfg B qBackPayload (7 + 2 * zeros) (by omega) t) =
      cfg B qBackCounter (7 + zeros) (by omega) t := by
    calc
      machine.run zeros _ = machine.run 1 (machine.run (zeros - 1) _) := by
        rw [← machine.run_add]
        congr 1
        omega
      _ = machine.run 1 (cfg B qBackPayload (7 + 2 * zeros - (zeros - 1))
          (by omega) t) := by rw [hback (zeros - 1) (by omega)]
      _ = _ := by
        simp only [UniformTM.run]
        rw [step_keep qBackPayload qBackCounter _ t (some true) .left (by
          have he : (⟨7 + 2 * zeros - (zeros - 1), by omega⟩ :
              Fin (tapeLength (pairLength a m) B)) = ⟨8 + zeros, by omega⟩ := by
            apply Fin.ext; simp; omega
          simpa only [he] using hterm) backPayload_true_action]
        apply config_ext <;> try rfl
        apply Fin.ext
        simp [cfg, moveHead]
        omega
  have hhole : t ⟨7 + zeros, by omega⟩ = none := by
    simp [t, roundTape]
    omega
  have htoSpend : machine.run 1 (cfg B qBackCounter (7 + zeros) (by omega) t) =
      cfg B qSpend (8 + zeros) (by omega) t := by
    simp only [UniformTM.run]
    rw [step_keep qBackCounter qSpend _ t none .right hhole backCounter_none_action]
    apply config_ext <;> try rfl
    apply Fin.ext
    simp [cfg, moveHead, show 7 + zeros + 1 < tapeLength (pairLength a m) B by omega]
    omega
  have hexhausted : machine.run 1 (cfg B qSpend (8 + zeros) (by omega) t) =
      cfg B qExhausted (8 + zeros) (by omega) t := by
    simp only [UniformTM.run]
    rw [step_keep qSpend qExhausted _ t (some true) .stay hterm spend_true_action]
    apply config_ext <;> try rfl
  have hcounterC : machine.run (zeros + 1) c =
      cfg B qBackCounter (7 + zeros) (by omega) t := by
    calc
      machine.run (zeros + 1) c = machine.run zeros (machine.run 1 c) := by
        rw [← machine.run_add]
        congr 1
        omega
      _ = _ := by rw [hstart, htoCounter]
  have hspendC : machine.run (zeros + 2) c =
      cfg B qSpend (8 + zeros) (by omega) t := by
    calc
      machine.run (zeros + 2) c = machine.run 1 (machine.run (zeros + 1) c) := by
        rw [← machine.run_add]
      _ = _ := by rw [hcounterC, htoSpend]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [machine.run_add, hstart, hback r hr]
    rfl
  · rw [hcounterC]
    rfl
  · rw [hspendC]
    rfl
  · have hend : machine.run (exhaustedTail zeros) c =
        cfg B qExhausted (8 + zeros) (by omega) t := by
      rw [exhaustedTail, show zeros + 3 = (zeros + 2) + 1 by omega,
        machine.run_add, hspendC, hexhausted]
    simpa [cfg, t] using congrArg (fun d => (d.state, d.head.val, d.tape)) hend

/-- Exact exhausted endpoint from an arbitrary last-boundary configuration. -/
theorem exhausted_tail_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B)
    (hc : RoundInvariant B x w zeros zeros c) :
    let d := machine.run (exhaustedTail zeros) c
    d.state = qExhausted ∧ d.head.val = 8 + zeros ∧
      d.tape = roundTape B x w zeros zeros := by
  exact (exhausted_tail_trace x w hg hzero hprefix c hc).2.2.2

/-- `qExhausted` is not visited at any earlier local tail time. -/
theorem exhausted_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B)
    (hc : RoundInvariant B x w zeros zeros c) (s : Nat) (hs : s < exhaustedTail zeros) :
    (machine.run s c).state ≠ qExhausted := by
  have ht := exhausted_tail_trace x w hg hzero hprefix c hc
  by_cases hs0 : s = 0
  · subst s
    simp only [UniformTM.run]
    intro hbad
    have := hc.1.symm.trans hbad
    exact (by decide : qStart ≠ qExhausted) this
  by_cases hs1 : s ≤ zeros
  · obtain ⟨r, hr⟩ : ∃ r, s = 1 + r := ⟨s - 1, by omega⟩
    subst s
    rw [ht.1 r (by omega)]
    decide
  have hsmax : s = zeros + 1 ∨ s = zeros + 2 := by
    simp [exhaustedTail] at hs
    omega
  rcases hsmax with rfl | rfl
  · rw [ht.2.1]; decide
  · rw [ht.2.2.1]; decide

/-- The exhausted internal tag is absorbing, with the entire configuration fixed. -/
theorem exhausted_absorbing {N B : Nat} (c : Config stateCount N B)
    (hc : c.state = qExhausted) (s : Nat) : machine.run s c = c := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [UniformTM.run, ih]
      rw [step_eq c qExhausted (c.tape c.head) .stay (by
        simpa [hc] using exhausted_action (c.tape c.head))]
      apply config_ext
      · exact hc.symm
      · apply Fin.ext; simp [moveHead]
      · funext i
        by_cases hi : i = c.head <;> simp [hi]

/-- End-to-end successor-local reachability, composed with the last-boundary driver. -/
theorem exhausted_reachable {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (exhaustedClock zeros) (startConfig B x w zeros)
    d.state = qExhausted ∧ d.head.val = 8 + zeros ∧
      d.tape = roundTape B x w zeros zeros := by
  have hb := last_boundary_reachable (B := B) x w htag hg hzero hprefix
  rw [exhaustedClock, machine.run_add]
  exact exhausted_tail_exact x w hg hzero hprefix _ hb

/-- Physical head bounds used by the tail; in particular neither endpoint move clamps. -/
theorem exhausted_no_clamp_facts {a m B zeros : Nat}
    (hp : 8 + 2 * zeros < a + m) :
    0 < 7 + zeros ∧ 8 + 2 * zeros < tapeLength (pairLength a m) B := by
  unfold tapeLength pairLength
  omega

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadExhausted
