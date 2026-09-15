import Complexity.Uniform.V1.FixedGammaPayloadDispatcherRounds
import Mathlib.Tactic

/-! A common length-only deadline and total physical classifier for G2k/G2l. -/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline

set_option maxHeartbeats 800000

open PairEncoding
open FixedGammaPayloadDispatcher
open FixedGammaPayloadDispatcherRounds

def deadline (N : Nat) : Nat := 2 * N * N

theorem deadline_eq (N : Nat) : deadline N = 2 * N * N := rfl

private theorem first_index_from {L : Nat} (z : Bitstring L) :
    ∀ offset remaining, offset ≤ L →
      ∃ k, k ≤ remaining ∧
        (∀ t, t < k → FixedContentTagGate.physicalSymbol z (offset + t) = some false) ∧
        (k = remaining ∨
          (k < remaining ∧ FixedContentTagGate.physicalSymbol z (offset + k) = some true) ∨
          (k < remaining ∧ offset + k = L)) := by
  intro offset remaining
  induction remaining generalizing offset with
  | zero => intro _; exact ⟨0, by omega, by simp, Or.inl rfl⟩
  | succ n ih =>
      intro hoff
      cases hs : FixedContentTagGate.physicalSymbol z offset with
      | none =>
          have heq : offset = L := by
            unfold FixedContentTagGate.physicalSymbol at hs
            split at hs
            · contradiction
            · omega
          exact ⟨0, by omega, by simp, Or.inr (Or.inr ⟨by omega, by simpa⟩)⟩
      | some b =>
          cases b with
          | true =>
              exact ⟨0, by omega, by simp, Or.inr (Or.inl ⟨by omega, by simpa⟩)⟩
          | false =>
              have hlt : offset < L := by
                unfold FixedContentTagGate.physicalSymbol at hs
                split at hs
                · assumption
                · contradiction
              obtain ⟨k, hk, hp, he⟩ := ih (offset + 1) (by omega)
              refine ⟨k + 1, by omega, ?_, ?_⟩
              · intro t ht
                cases t with
                | zero => simpa using hs
                | succ t =>
                    have heq : offset + (t + 1) = (offset + 1) + t := by omega
                    rw [heq]
                    exact hp t (by omega)
              · rcases he with he | he | he
                · exact Or.inl (by omega)
                · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
                  have heq : offset + (k + 1) = (offset + 1) + k := by omega
                  rw [heq]
                  exact he.2
                · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem gamma_payload_first_index {L zeros : Nat} (z : Bitstring L)
    (hg : FixedContentGammaTerminator.gammaZeros? z = some zeros) :
    ∃ k, k ≤ zeros ∧
      (∀ t, t < k → FixedContentTagGate.physicalSymbol z (9 + zeros + t) = some false) ∧
      (k = zeros ∨
        (k < zeros ∧ FixedContentTagGate.physicalSymbol z (9 + zeros + k) = some true) ∨
        (k < zeros ∧ 9 + zeros + k = L)) := by
  have ht := ((FixedContentGammaTerminator.gamma_contract z).1 zeros hg).1
  have hf : 9 + zeros ≤ L := by omega
  exact first_index_from z (9 + zeros) zeros hf

private theorem gamma_fit {L zeros : Nat} (z : Bitstring L)
    (hg : FixedContentGammaTerminator.gammaZeros? z = some zeros) : 9 + zeros ≤ L := by
  have ht := ((FixedContentGammaTerminator.gamma_contract z).1 zeros hg).1
  omega

theorem malformedClock_le_deadline {N : Nat} (hN : 8 ≤ N) : 1 ≤ deadline N := by
  simp [deadline]; nlinarith

theorem zeroWidthClock_le_deadline {N : Nat} (hN : 8 ≤ N) : 2 ≤ deadline N := by
  simp [deadline]; nlinarith

theorem firstEndClock_le_deadline {N zeros : Nat} (hf : 9 + zeros ≤ N) :
    3 * zeros + 6 ≤ deadline N := by
  simp [deadline]; nlinarith

theorem pendingEndClock_le_deadline {N zeros k : Nat} (hf : 9 + zeros ≤ N)
    (hk : 1 ≤ k) (hkz : k < zeros) : pendingEndClock zeros k ≤ deadline N := by
  rw [pendingEndClock_eq hk]
  simp [deadline]
  nlinarith

theorem zeroEndClock_le_deadline {N zeros : Nat} (hf : 9 + zeros ≤ N)
    (hz : 0 < zeros) : zeroEndClock zeros ≤ deadline N := by
  rw [zeroEndClock_eq hz]
  simp [deadline]
  nlinarith

private theorem lift_endpoint {N B clock D : Nat} (c : Config stateCount N B)
    (hclock : clock ≤ deadline D) (q : Fin stateCount)
    (hq : (machine.run clock c).state = q)
    (ha : ∀ d : Config stateCount N B, d.state = q → ∀ r, machine.run r d = d) :
    machine.run (deadline D) c = machine.run clock c := by
  rw [show deadline D = clock + (deadline D - clock) by omega, machine.run_add]
  exact ha _ hq _

private theorem lift_allZero {N B clock D : Nat} (c : Config stateCount N B)
    (hc : clock ≤ deadline D) (hs : (machine.run clock c).state = qAllZero) :
    machine.run (deadline D) c = machine.run clock c :=
  lift_endpoint c hc qAllZero hs (fun d h => (endpoints_absorb d).1 h)

private theorem lift_hasOne {N B clock D : Nat} (c : Config stateCount N B)
    (hc : clock ≤ deadline D) (hs : (machine.run clock c).state = qHasOne) :
    machine.run (deadline D) c = machine.run clock c :=
  lift_endpoint c hc qHasOne hs (fun d h => (endpoints_absorb d).2.1 h)

private theorem lift_reject {N B clock D : Nat} (c : Config stateCount N B)
    (hc : clock ≤ deadline D) (hs : (machine.run clock c).state = qReject) :
    machine.run (deadline D) c = machine.run clock c :=
  lift_endpoint c hc qReject hs (fun d h => (endpoints_absorb d).2.2 h)

private theorem prefix_absolute {L zeros k : Nat} (z : Bitstring L)
    (hp : ∀ t, t < k →
      FixedContentTagGate.physicalSymbol z (9 + zeros + t) = some false) :
    ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol z j = some false := by
  intro j hj0 hj1
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj0
  simpa [Nat.add_assoc] using hp t (by omega)

theorem malformed_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have he := malformed_exact (B := B) x w htag hg
  have hN := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
  dsimp
  rw [lift_reject (startConfig B x w) (malformedClock_le_deadline (by omega)) he.1]
  exact he

theorem zero_width_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 7 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have he := zero_width_exact (B := B) x w htag hg
  have hf := gamma_fit (Fin.append x w) hg
  dsimp
  rw [lift_allZero (startConfig B x w) (zeroWidthClock_le_deadline (by omega)) (by rw [he])]
  rw [he]
  exact ⟨rfl, rfl, rfl⟩

theorem true_at_deadline {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : k < zeros)
    (hp : ∀ t, t < k → FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + t) = some false)
    (ht : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qHasOne ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have hf := gamma_fit (Fin.append x w) hg
  by_cases hk0 : k = 0
  · subst k
    have hpos : 9 + zeros < a + m := by
      unfold FixedContentTagGate.physicalSymbol at ht
      split at ht
      · assumption
      · contradiction
    have he := first_true_exact (B := B) x w htag hg (by omega) hpos (by
      simpa [FixedContentTagGate.physicalSymbol, hpos] using ht)
    dsimp
    rw [lift_hasOne (startConfig B x w) (firstEndClock_le_deadline hf) (by rw [he]), he]
    exact ⟨rfl, rfl, rfl⟩
  · have hk1 : 1 ≤ k := by omega
    have he := FixedGammaPayloadDispatcherRounds.true_exact (B := B) x w htag hg
      hk1 hk (prefix_absolute _ hp) ht
    dsimp
    rw [lift_hasOne (startConfig B x w) (pendingEndClock_le_deadline hf hk1 hk) he.1]
    exact ⟨he.1, he.2.1, he.2.2.1⟩

theorem virtual_at_deadline {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : k < zeros)
    (hp : ∀ t, t < k → FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + t) = some false) (hv : 9 + zeros + k = a + m) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have hf := gamma_fit (Fin.append x w) hg
  by_cases hk0 : k = 0
  · subst k
    have he := first_virtual_exact (B := B) x w htag hg (by omega) (by simpa using hv)
    dsimp
    rw [lift_allZero (startConfig B x w) (firstEndClock_le_deadline hf) (by rw [he]), he]
    exact ⟨rfl, rfl, rfl⟩
  · have hk1 : 1 ≤ k := by omega
    have he := FixedGammaPayloadDispatcherRounds.virtual_exact (B := B) x w htag hg
      hk1 hk (prefix_absolute _ hp) hv
    dsimp
    rw [lift_allZero (startConfig B x w) (pendingEndClock_le_deadline hf hk1 hk) he.1]
    exact ⟨he.1, he.2.1, he.2.2.1⟩

theorem exhausted_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 0 < zeros)
    (hp : ∀ t, t < zeros → FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + t) = some false) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have hf := gamma_fit (Fin.append x w) hg
  have he := FixedGammaPayloadDispatcherRounds.zero_exact (B := B) x w htag hg hz
    (by
      intro j hj0 hj1
      apply prefix_absolute (Fin.append x w) hp j hj0
      omega)
  dsimp
  rw [lift_allZero (startConfig B x w) (zeroEndClock_le_deadline hf hz) he.1]
  exact ⟨he.1, he.2.1, he.2.2.1⟩

theorem tagged_endpoint_classification {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    ((d.state = qReject ∧ d.head.val = a + m ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) ∨
      (d.state = qAllZero ∧ d.head.val = 7 ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) ∨
      (∃ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        0 < zeros ∧ d.head.val = 6 ∧
        ((d.state = qHasOne ∧ ∃ k, k < zeros ∧
            FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true) ∨
          (d.state = qAllZero ∧ ¬ ∃ k, k < zeros ∧
            FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true)))) := by
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | none =>
      have he := malformed_at_deadline (B := B) x w htag hg
      exact ⟨he.2.2, Or.inl ⟨he.1, he.2.1, rfl⟩⟩
  | some zeros =>
      cases zeros with
      | zero =>
          have he := zero_width_at_deadline (B := B) x w htag hg
          exact ⟨he.2.2, Or.inr (Or.inl ⟨he.1, he.2.1, rfl⟩)⟩
      | succ zeros =>
          obtain ⟨k, _, hp, he⟩ := gamma_payload_first_index (Fin.append x w) hg
          rcases he with he | he | he
          · subst k
            have hd := exhausted_at_deadline (B := B) x w htag hg (by omega) hp
            refine ⟨hd.2.2, Or.inr (Or.inr ⟨zeros + 1, rfl, by omega, hd.2.1,
              Or.inr ⟨hd.1, ?_⟩⟩)⟩
            intro h
            obtain ⟨k, hk, ht⟩ := h
            rw [hp k hk] at ht
            contradiction
          · have hd := true_at_deadline (B := B) x w htag hg he.1 hp he.2
            exact ⟨hd.2.2, Or.inr (Or.inr ⟨zeros + 1, rfl, by omega, hd.2.1,
              Or.inl ⟨hd.1, k, he.1, he.2⟩⟩)⟩
          · have hd := virtual_at_deadline (B := B) x w htag hg he.1 hp he.2
            refine ⟨hd.2.2, Or.inr (Or.inr ⟨zeros + 1, rfl, by omega, hd.2.1,
              Or.inr ⟨hd.1, ?_⟩⟩)⟩
            intro h
            obtain ⟨j, hj, ht⟩ := h
            by_cases hjk : j < k
            · rw [hp j hjk] at ht; contradiction
            · have hout : a + m ≤ 9 + (zeros + 1) + j := by omega
              unfold FixedContentTagGate.physicalSymbol at ht
              split at ht
              · omega
              · contradiction

theorem qHasOne_iff {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (machine.run (deadline (a + m)) (startConfig B x w)).state = qHasOne ↔
      ∃ k, k < zeros ∧ FixedContentTagGate.physicalSymbol (Fin.append x w)
        (9 + zeros + k) = some true := by
  have hc := (tagged_endpoint_classification (B := B) x w htag).2
  rw [hg] at hc
  constructor
  · intro hs
    rcases hc with h | h | ⟨z, hgz, _, _, ho⟩
    · cases h.2.2
    · have hz : zeros = 0 := Option.some.inj h.2.2
      subst zeros
      have hn : qAllZero ≠ qHasOne := by decide
      exact (hn (h.1.symm.trans hs)).elim
    · have hz : zeros = z := Option.some.inj hgz
      subst z
      rcases ho with ho | ho
      · exact ho.2
      · have hn : qAllZero ≠ qHasOne := by decide
        exact (hn (ho.1.symm.trans hs)).elim
  · intro hex
    rcases hc with h | h | ⟨z, hgz, _, _, ho⟩
    · cases h.2.2
    · have hz : zeros = 0 := Option.some.inj h.2.2
      subst zeros
      obtain ⟨k, hk, _⟩ := hex
      omega
    · have hz : zeros = z := Option.some.inj hgz
      subst z
      rcases ho with ho | ho
      · exact ho.1
      · exact (ho.2 hex).elim

theorem qAllZero_iff {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (machine.run (deadline (a + m)) (startConfig B x w)).state = qAllZero ↔
      ¬ ∃ k, k < zeros ∧ FixedContentTagGate.physicalSymbol (Fin.append x w)
        (9 + zeros + k) = some true := by
  have hc := (tagged_endpoint_classification (B := B) x w htag).2
  rw [hg] at hc
  constructor
  · intro hs hex
    have hh := (qHasOne_iff (B := B) x w htag hg).2 hex
    exact (show qAllZero ≠ qHasOne by decide) (hs.symm.trans hh)
  · intro hn
    rcases hc with h | h | ⟨z, hgz, _, _, ho⟩
    · cases h.2.2
    · exact h.1
    · have hz : zeros = z := Option.some.inj hgz
      subst z
      rcases ho with ho | ho
      · exact (hn ho.2).elim
      · exact ho.1

theorem qReject_iff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (machine.run (deadline (a + m)) (startConfig B x w)).state = qReject ↔
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none := by
  have hc := (tagged_endpoint_classification (B := B) x w htag).2
  constructor
  · intro hs
    rcases hc with h | h | ⟨z, hgz, _, _, ho⟩
    · exact h.2.2
    · exact False.elim ((show qReject ≠ qAllZero by decide) (hs.symm.trans h.1))
    · rcases ho with h | h
      · exact False.elim ((show qReject ≠ qHasOne by decide) (hs.symm.trans h.1))
      · exact False.elim ((show qReject ≠ qAllZero by decide) (hs.symm.trans h.1))
  · intro hg
    rw [hg] at hc
    rcases hc with h | h | ⟨z, hgz, _, _, ho⟩
    · exact h.1
    · cases h.2.2
    · cases hgz

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline
