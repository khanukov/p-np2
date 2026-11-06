import Complexity.Uniform.V1.FixedGammaPayloadRoundStep

/-!
# Fixed gamma-payload false-round driver (Part A G2d)

This proof-only module iterates the exact physical-false round theorem of
`FixedGammaPayloadRoundStep`.  Its clock is local to that successor machine:
the real core handoff is already boundary one, at local clock zero.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadRoundDriver

open PairEncoding
open FixedGammaPayloadRoundStep

/-- Successor-local clock for boundary `k`; boundary one is the start configuration. -/
def boundaryClock (zeros k : Nat) : Nat := (k - 1) * roundCost zeros

theorem boundaryClock_one (zeros : Nat) : boundaryClock zeros 1 = 0 := by
  simp [boundaryClock]

theorem boundaryClock_succ {zeros k : Nat} (hk : 1 ≤ k) :
    boundaryClock zeros (k + 1) = boundaryClock zeros k + roundCost zeros := by
  cases k with
  | zero => omega
  | succ k =>
      simp only [boundaryClock, Nat.succ_sub_one]
      rw [Nat.succ_mul]

theorem boundaryClock_two (zeros : Nat) :
    boundaryClock zeros 2 = roundCost zeros := by
  simp [boundaryClock]

/-- A physical-symbol prefix supplies the physical bound for its last cell. -/
theorem prefix_physical_bound {a m zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hk : 1 ≤ k)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    8 + zeros + k < a + m := by
  have hp := hprefix (8 + zeros + k) (by omega) (by omega)
  unfold FixedContentTagGate.physicalSymbol at hp
  split at hp
  · assumption
  · contradiction

/-- After `r` successor rounds, the run is exactly at boundary `r + 1`. -/
theorem rounds_false_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (r : Nat) (hr : r < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 10 + zeros + r →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    RoundInvariant B x w zeros (r + 1)
      (machine.run (r * roundCost zeros) (startConfig B x w zeros)) := by
  induction r with
  | zero =>
      have hp' := prefix_physical_bound x w (k := 1) (by omega) (by
          intro j hlo hhi
          exact hprefix j hlo (by omega))
      have hp : 9 + zeros < a + m := by omega
      have hf := hprefix (9 + zeros) (by omega) (by omega)
      have hfalse : (Fin.append x w) ⟨9 + zeros, hp⟩ = false := by
        simpa [FixedContentTagGate.physicalSymbol, hp] using hf
      simpa using handoff_exact x w htag hg (by omega) hp hfalse
  | succ r ih =>
      have hp' := prefix_physical_bound x w (k := r + 2) (by omega) (by
          intro j hlo hhi
          exact hprefix j hlo (by omega))
      have hp : 9 + zeros + (r + 1) < a + m := by omega
      have hf := hprefix (10 + zeros + r) (by omega) (by omega)
      have hfalse : (Fin.append x w) ⟨9 + zeros + (r + 1), hp⟩ = false := by
        unfold FixedContentTagGate.physicalSymbol at hf
        rw [dif_pos (show 10 + zeros + r < a + m by omega)] at hf
        have he : (⟨10 + zeros + r, by omega⟩ : Fin (a + m)) =
            ⟨9 + zeros + (r + 1), hp⟩ := by
          apply Fin.ext
          simp
          omega
        simpa only [he] using Option.some.inj hf
      rw [Nat.succ_mul, machine.run_add]
      apply round_false_exact x w hg (k := r + 1) (by omega) hr hp hfalse
        (fun j hlo hhi => hprefix j hlo (by omega))
      exact ih (by omega) (fun j hlo hhi => hprefix j hlo (by omega))

/-- Every false-prefix boundary from one through `zeros` is reachable. -/
theorem boundary_reachable {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k ≤ zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    RoundInvariant B x w zeros k
      (machine.run (boundaryClock zeros k) (startConfig B x w zeros)) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hclock : boundaryClock zeros (r + 1) = r * roundCost zeros := by
    simp [boundaryClock]
  rw [hclock]
  exact rounds_false_exact x w htag hg r (by omega) (by
    intro j hlo hhi
    exact hprefix j hlo (by omega))

/-- The last false-prefix boundary, immediately after all `zeros` rounds. -/
theorem last_boundary_reachable {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    RoundInvariant B x w zeros zeros
      (machine.run (boundaryClock zeros zeros) (startConfig B x w zeros)) := by
  apply boundary_reachable x w htag hg (k := zeros) (by omega) (by omega)
  intro j hlo hhi
  exact hprefix j hlo (by omega)

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadRoundDriver
