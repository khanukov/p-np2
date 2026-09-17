import Complexity.Uniform.V1.FixedGammaTargetFirstPayload
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTerminatorScratchBootstrapBridge

/-!
# Header meaning of the first gamma payload bit (Part A G2p-b)

The fixed machine `FixedGammaTargetFirstPayload` extends the G2p-a scratch
register at cell `a + m + 1` by one cell.  On a matching tag this bridge
identifies the stored bits with the parsed content header
`contentHeader? z = some (n, consumed)`, at the machine's length-only deadline
`3 * (a + m)`:

* `firstPayload_positive_register`: if `0 < n` and cell `a + m + 2` is allocated,
  then for some `zeros` with `0 < zeros`, `consumed = 2 * zeros + 1`, and
  `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the endpoint is `qDone` at head `7` with
  `firstPayloadTape` carrying `(n + 1).testBit (zeros - 1)`.  Cells `a + m + 1`
  and `a + m + 2` hold `(n + 1).testBit zeros` and `(n + 1).testBit (zeros - 1)`,
  the two leading binary digits of `n + 1`.
* `firstPayload_zero_width_register`: for the header `(0, 1)` the endpoint is
  `qDone` at head `7` on the unchanged bootstrap scratch tape; the register is
  the single digit `(0 + 1).testBit 0` at `a + m + 1`, blank afterwards.

The second digit comes from the header decoder's own payload read, whose virtual
zero tail makes a payload cell at the boundary `a + m` the digit `0`.  A positive
`n` forces a positive gamma width; the room premise is not implied by the header
(it fails at `a = B = 0`).  Nothing here stores further digits or `n`, or claims
parser execution, content acceptance, untagged behavior, clock composition,
`ContentVerifierBridge`, or P-vs-NP mainline progress.
-/

namespace Pnp4.Frontier.ContractExpansion

open Pnp3.Complexity.Uniform.V1

/-- A positive decoded header has positive gamma width, and its first payload
cell, read with the virtual zero tail, is digit `zeros - 1` of `n + 1`. -/
private theorem header_second_digit {N n consumed : Nat} (z : PrefixBitVec N)
    (hheader : contentHeader? z = some (n, consumed)) (hn : 0 < n) :
    ∃ zeros, FixedContentGammaTerminator.gammaZeros? z = some zeros ∧ 0 < zeros ∧
      consumed = 2 * zeros + 1 ∧ 2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      (n + 1).testBit zeros = true ∧
      (FixedContentTagGate.physicalSymbol z (9 + zeros)).getD false =
        (n + 1).testBit (zeros - 1) := by
  obtain ⟨zeros, payload, hg, hpayload, hvalue, hconsumed⟩ :=
    (contentHeader?_eq_some_iff_gammaZeros_payload z).1 hheader
  have hlt : payload < 2 ^ zeros := by
    rw [VirtualZeroTailReader.readNatBE_eq_padWord] at hpayload
    exact readNatBE_lt_two_pow _ _ _ hpayload
  have hfit := ((FixedContentGammaTerminator.gamma_contract z).1 zeros hg).1
  obtain ⟨k, rfl⟩ : ∃ k, zeros = k + 1 := by
    cases zeros with
    | zero => rw [Nat.pow_zero] at hlt hvalue; omega
    | succ k => exact ⟨k, rfl⟩
  have hbit : VirtualZeroTailReader.readBit? z (2 * N + 1) (9 + (k + 1)) =
      some (padRead z (9 + (k + 1))) := by
    rw [VirtualZeroTailReader.readBit?, dif_pos (show 9 + (k + 1) < 2 * N + 1 by omega)]
  cases hrest : VirtualZeroTailReader.readNatBE z (2 * N + 1) (9 + (k + 1) + 1) k with
  | none =>
      rw [VirtualZeroTailReader.readNatBE, hbit, hrest] at hpayload
      cases hpayload
  | some rest =>
      rw [VirtualZeroTailReader.readNatBE, hbit, hrest] at hpayload
      have hpay : (if padRead z (9 + (k + 1)) then 2 ^ k else 0) + rest = payload :=
        Option.some.inj hpayload
      have hrestlt : rest < 2 ^ k := by
        rw [VirtualZeroTailReader.readNatBE_eq_padWord] at hrest
        exact readNatBE_lt_two_pow _ _ _ hrest
      have hpow : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      refine ⟨k + 1, hg, by omega, hconsumed, by omega, by omega, ?_, ?_⟩
      · rw [hvalue, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · have hread : (FixedContentTagGate.physicalSymbol z (9 + (k + 1))).getD false =
            padRead z (9 + (k + 1)) := by
          unfold FixedContentTagGate.physicalSymbol padRead
          split <;> rfl
        rw [hread, Nat.add_sub_cancel, hvalue, Nat.testBit_two_pow_add_gt (by omega), ← hpay]
        cases padRead z (9 + (k + 1)) with
        | false => rw [if_neg Bool.false_ne_true, Nat.zero_add, Nat.testBit_lt_two_pow hrestlt]
        | true =>
            rw [if_pos rfl, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hrestlt]
            rfl

/-- On a matching tag with positive header target `n` and an allocated first
payload cell, the deadline register holds the two leading digits of `n + 1`. -/
theorem firstPayload_positive_register {a m B n consumed : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) (hn : 0 < n)
    (hroom : a + m + 2 < tapeLength (PairEncoding.pairLength a m) B) :
    ∃ zeros, 0 < zeros ∧ consumed = 2 * zeros + 1 ∧
      2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      let d := FixedGammaTargetFirstPayload.machine.run
        (FixedGammaTargetFirstPayload.deadline (a + m))
        (FixedGammaTargetFirstPayload.startConfig B x w)
      d.state = FixedGammaTargetFirstPayload.qDone ∧ d.head.val = 7 ∧
        d.tape = FixedGammaTargetFirstPayload.firstPayloadTape B x w
          ((n + 1).testBit (zeros - 1)) ∧
        d.tape ⟨a + m + 1, by unfold tapeLength PairEncoding.pairLength; omega⟩ =
          some ((n + 1).testBit zeros) ∧
        d.tape ⟨a + m + 2, hroom⟩ = some ((n + 1).testBit (zeros - 1)) := by
  obtain ⟨zeros, hg, hz, hconsumed, hlo, hhi, htop, hdigit⟩ :=
    header_second_digit (Fin.append x w) hheader hn
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTargetFirstPayload.first_payload_at_deadline (B := B) x w htag hg hz hroom
  rw [hdigit] at ht
  obtain ⟨-, -, h1, h2, -⟩ := FixedGammaTargetFirstPayload.firstPayloadTape_layout (B := B) x w
    ((n + 1).testBit (zeros - 1)) hroom
  refine ⟨zeros, hz, hconsumed, hlo, hhi, hq, hh, ht, ?_, ?_⟩
  · rw [ht, h1, htop]
  · rw [ht, h2]

/-- On a matching tag with header `(0, 1)`, the deadline endpoint keeps the
bootstrap register: the single digit of `0 + 1`, with no room premise. -/
theorem firstPayload_zero_width_register {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (0, 1)) :
    let d := FixedGammaTargetFirstPayload.machine.run
      (FixedGammaTargetFirstPayload.deadline (a + m))
      (FixedGammaTargetFirstPayload.startConfig B x w)
    d.state = FixedGammaTargetFirstPayload.qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w ∧
      d.tape ⟨a + m + 1, by unfold tapeLength PairEncoding.pairLength; omega⟩ =
        some ((0 + 1).testBit 0) ∧
      ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 1 < i.val →
        d.tape i = none := by
  obtain ⟨zeros, payload, hg, -, -, hconsumed⟩ :=
    (contentHeader?_eq_some_iff_gammaZeros_payload _).1 hheader
  obtain rfl : zeros = 0 := by omega
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTargetFirstPayload.zero_width_at_deadline (B := B) x w htag hg
  obtain ⟨-, -, h1, h2⟩ := FixedGammaTerminatorScratchBootstrap.scratchTape_layout (B := B) x w
  exact ⟨hq, hh, ht, by rw [ht, h1]; rfl, fun i hi => by rw [ht]; exact h2 i hi⟩

end Pnp4.Frontier.ContractExpansion
