import Complexity.Uniform.V1.FixedGammaTargetSecondPayload
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetFirstPayloadBridge

/-!
# Header meaning of the second gamma payload digit (Part A G2p-c)

The fixed machine `FixedGammaTargetSecondPayload` extends the G2p-b target
register by one cell on a decoded gamma width `2 ≤ zeros`, and hands back the
incoming tape unchanged on the two smaller decoded widths.  This bridge reads
the resulting register against the parsed content header
`contentHeader? z = some (n, consumed)`, at the machine's length-only deadline
`FixedGammaTargetSecondPayload.deadline (a + m) = 2 * (a + m)`.  Write
`N = a + m`.

* `header_digits` (one hypothesis, no machine and no tag): a decoded header fixes
  the physical gamma width (`gammaZeros? z = some zeros`), with
  `consumed = 2 * zeros + 1` and
  `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, its digit `zeros` is the leading `true`
  of `n + 1`, and for every `t < zeros` the payload cell `9 + zeros + t` reads —
  through the decoder's *own* virtual zero tail, which is why the statement is
  about `Option.getD false` of the physical symbol and not about a physical cell
  — as `(n + 1).testBit (zeros - 1 - t)`.
* `secondPayload_positive_register` (four hypotheses): matching tag, decoded
  header, `3 ≤ n`, and the exact room `N + 3 < tapeLength (pairLength a m) B`.
  Then for some `zeros` with `2 ≤ zeros` the deadline endpoint is `qDone` at head
  `7` on `secondPayloadTape` with both digits taken from that same header, and
  cells `N + 1`, `N + 2`, `N + 3` hold `(n + 1).testBit zeros`,
  `(n + 1).testBit (zeros - 1)`, `(n + 1).testBit (zeros - 2)`: the three leading
  binary digits of `n + 1`.
* `secondPayload_width_one_register` (three hypotheses): a header with
  `consumed = 3`, that is gamma width one, and the G2p-b room `N + 2`.  The
  endpoint keeps exactly the two-digit G2p-b register `firstPayloadTape`, and
  every *allocated* cell past `N + 2` — including the target cell `N + 3` when it
  exists — stays blank: no third digit is written.
* `secondPayload_zero_width_register` (two hypotheses): the header `(0, 1)` keeps
  the one-digit G2p-a scratch register, with no room premise.

`3 ≤ n` is exactly the width-two condition, in this sense: the conjuncts
`2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)` of `header_digits` make `zeros` the index
of the leading binary digit of `n + 1`, so on a decoded header `2 ≤ zeros` holds
if and only if `4 ≤ n + 1`.  Both directions of that equivalence are derivable
from the exported conjuncts, and neither is stated as an equivalence theorem: the
bridge theorems themselves only ever run
`contentHeader? = some …  →  machine conclusion`.  There is deliberately **no
converse**: nothing here derives a valid header, a width, or `2 ≤ zeros` from
`qDone`, from the endpoint tape, or from a digit found at `N + 3`.

Room is not implied by the header: `FixedGammaTargetSecondPayload.room_iff` makes
`N + 3 < tapeLength (pairLength a m) B` equivalent to `2 ≤ a + B`, a condition on
the `x` side and the budget that a decoded header does not constrain, so `hroom`
is carried explicitly and this bridge states no room-free `qReject`
classification.

`FixedGammaTargetSecondPayload.deadline` and `exactClock` are **phase-local**:
`startConfig` is a retagging of the *actual* G2p-b endpoint configuration and
embeds every step of the earlier phases, which neither clock accounts for.
Nothing here is a `UniformP` execution, a runtime, or a clock for the composed
pipeline.  Nothing here claims parser execution, `contentInput?`,
`ContentAccepts`, language acceptance from `qDone`, clock composition, the
remaining `zeros - 2` payload digits, the decrement of the stored `n + 1` to `n`,
`ContentVerifierBridge`, advice-freedom, `NP` membership, or P-vs-NP mainline
progress.  It is infrastructure.
-/

namespace Pnp4.Frontier.ContractExpansion

open Pnp3.Complexity.Uniform.V1

/-- Digit `t` of a successful virtual-zero-tail big-endian read is the padded
cell `offset + t`, counting digits from the most significant end.  This is the
generic reader induction behind `header_digits`; the `t < width` guard is what
keeps it inside the field that was actually read. -/
private theorem readNatBE_digit {N T : Nat} (z : PrefixBitVec N) :
    ∀ width offset value t : Nat,
      VirtualZeroTailReader.readNatBE z T offset width = some value → t < width →
        value.testBit (width - 1 - t) = padRead z (offset + t) := by
  intro width
  induction width with
  | zero => exact fun _ _ t _ ht => (Nat.not_lt_zero t ht).elim
  | succ k ih =>
      intro offset value t hread ht
      rw [VirtualZeroTailReader.readNatBE] at hread
      cases hbit : VirtualZeroTailReader.readBit? z T offset with
      | none => rw [hbit] at hread; cases hread
      | some b =>
          cases hrest : VirtualZeroTailReader.readNatBE z T (offset + 1) k with
          | none => rw [hbit, hrest] at hread; cases hread
          | some rest =>
              rw [hbit, hrest] at hread
              have hv : (if b then 2 ^ k else 0) + rest = value := Option.some.inj hread
              have hlt : rest < 2 ^ k := by
                rw [VirtualZeroTailReader.readNatBE_eq_padWord] at hrest
                exact readNatBE_lt_two_pow _ _ _ hrest
              rcases Nat.eq_zero_or_pos t with rfl | hpos
              · have hb : padRead z offset = b := by
                  unfold VirtualZeroTailReader.readBit? at hbit
                  split at hbit
                  · exact Option.some.inj hbit
                  · cases hbit
                rw [← hv, show k + 1 - 1 - 0 = k from rfl, Nat.add_zero, hb]
                cases b with
                | false =>
                    rw [if_neg Bool.false_ne_true, Nat.zero_add,
                      Nat.testBit_lt_two_pow hlt]
                | true =>
                    rw [if_pos rfl, Nat.testBit_two_pow_add_eq,
                      Nat.testBit_lt_two_pow hlt]
                    rfl
              · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
                have hrec := ih (offset + 1) rest t' hrest (by omega)
                rw [← hv, show k + 1 - 1 - (t' + 1) = k - 1 - t' by omega]
                have hlow : ((if b then 2 ^ k else 0) + rest).testBit (k - 1 - t') =
                    rest.testBit (k - 1 - t') := by
                  cases b with
                  | false => rw [if_neg Bool.false_ne_true, Nat.zero_add]
                  | true =>
                      rw [if_pos rfl]
                      exact Nat.testBit_two_pow_add_gt (by omega) rest
                rw [hlow, hrec, show offset + 1 + t' = offset + (t' + 1) by omega]

/-- The generic parser fact of this slice, with no machine and no tag in it: a
decoded header fixes the gamma width, the bit length of `n + 1`, its leading
digit, and *every* payload cell as a binary digit of `n + 1`, read with the
decoder's own virtual zero tail.  The guard `t < zeros` keeps the claim inside
the payload block `[9 + zeros, 9 + 2 * zeros)`; outside it the truncated index
`zeros - 1 - t` would repeat digit `0` while the cell address has already left
the block. -/
theorem header_digits {N n consumed : Nat} (z : PrefixBitVec N)
    (hheader : contentHeader? z = some (n, consumed)) :
    ∃ zeros, FixedContentGammaTerminator.gammaZeros? z = some zeros ∧
      consumed = 2 * zeros + 1 ∧ 2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      (n + 1).testBit zeros = true ∧
      ∀ t, t < zeros →
        (FixedContentTagGate.physicalSymbol z (9 + zeros + t)).getD false =
          (n + 1).testBit (zeros - 1 - t) := by
  obtain ⟨zeros, payload, hg, hpayload, hvalue, hconsumed⟩ :=
    (contentHeader?_eq_some_iff_gammaZeros_payload z).1 hheader
  have hlt : payload < 2 ^ zeros := by
    rw [VirtualZeroTailReader.readNatBE_eq_padWord] at hpayload
    exact readNatBE_lt_two_pow _ _ _ hpayload
  have hpow : 2 ^ (zeros + 1) = 2 * 2 ^ zeros := by rw [Nat.pow_succ]; omega
  refine ⟨zeros, hg, hconsumed, by omega, by omega, ?_, fun t ht => ?_⟩
  · rw [hvalue, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
    rfl
  · have hread : (FixedContentTagGate.physicalSymbol z (9 + zeros + t)).getD false =
        padRead z (9 + zeros + t) := by
      unfold FixedContentTagGate.physicalSymbol padRead
      split <;> rfl
    rw [hread, hvalue, Nat.testBit_two_pow_add_gt (by omega),
      ← readNatBE_digit z zeros (9 + zeros) payload t hpayload ht]

/-- On a matching tag, a decoded header with `3 ≤ n`, and the exact room for the
target cell `a + m + 3`, the deadline endpoint of this phase holds the three
leading binary digits of `n + 1` in cells `a + m + 1`, `a + m + 2`, `a + m + 3`.
Both tape arguments of `secondPayloadTape` are the digits of *this* header, not
free parameters: they are the padded content symbols the endpoint theorem reads
at `9 + zeros` and `10 + zeros`.  The room premise is carried explicitly because
the header does not imply it (`room_iff`), and `deadline` is phase-local. -/
theorem secondPayload_positive_register {a m B n consumed : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) (hn : 3 ≤ n)
    (hroom : a + m + 3 < tapeLength (PairEncoding.pairLength a m) B) :
    ∃ zeros, 2 ≤ zeros ∧ consumed = 2 * zeros + 1 ∧
      2 ^ zeros ≤ n + 1 ∧ n + 1 < 2 ^ (zeros + 1) ∧
      let d := FixedGammaTargetSecondPayload.machine.run
        (FixedGammaTargetSecondPayload.deadline (a + m))
        (FixedGammaTargetSecondPayload.startConfig B x w)
      d.state = FixedGammaTargetSecondPayload.qDone ∧ d.head.val = 7 ∧
        d.tape = FixedGammaTargetSecondPayload.secondPayloadTape B x w
          ((n + 1).testBit (zeros - 1)) ((n + 1).testBit (zeros - 2)) ∧
        d.tape ⟨a + m + 1, by unfold tapeLength PairEncoding.pairLength; omega⟩ =
          some ((n + 1).testBit zeros) ∧
        d.tape ⟨a + m + 2, by omega⟩ = some ((n + 1).testBit (zeros - 1)) ∧
        d.tape ⟨a + m + 3, hroom⟩ = some ((n + 1).testBit (zeros - 2)) := by
  obtain ⟨zeros, hg, hconsumed, hlo, hhi, htop, hdigit⟩ :=
    header_digits (Fin.append x w) hheader
  have hz : 2 ≤ zeros := by
    rcases (show zeros = 0 ∨ zeros = 1 ∨ 2 ≤ zeros by omega) with rfl | rfl | h
    · rw [show (2 : Nat) ^ (0 + 1) = 2 from rfl] at hhi
      omega
    · rw [show (2 : Nat) ^ (1 + 1) = 4 from rfl] at hhi
      omega
    · exact h
  have h0 := hdigit 0 (by omega)
  have h1 := hdigit 1 (by omega)
  rw [Nat.add_zero, Nat.sub_zero] at h0
  rw [show 9 + zeros + 1 = 10 + zeros by omega,
    show zeros - 1 - 1 = zeros - 2 by omega] at h1
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTargetSecondPayload.second_payload_at_deadline (B := B) x w htag hg hz hroom
  rw [h0, h1] at ht
  obtain ⟨-, -, hr1, hr2, hr3, -⟩ :=
    FixedGammaTargetSecondPayload.secondPayloadTape_layout (B := B) x w
      ((n + 1).testBit (zeros - 1)) ((n + 1).testBit (zeros - 2)) hroom
  exact ⟨zeros, hz, hconsumed, hlo, hhi, hq, hh, ht, by rw [ht, hr1, htop],
    by rw [ht, hr2], by rw [ht, hr3]⟩

/-- On a matching tag with `consumed = 3` — gamma width one — the register keeps
exactly the two digits of `n + 1` that G2p-b already stored, and every allocated
cell past `a + m + 2` stays blank, so no third digit is written.  Only the G2p-b
room premise is used, and it does not allocate `a + m + 3`, so the blank suffix
claim is vacuous exactly when the target cell does not exist. -/
theorem secondPayload_width_one_register {a m B n : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, 3))
    (hroom : a + m + 2 < tapeLength (PairEncoding.pairLength a m) B) :
    let d := FixedGammaTargetSecondPayload.machine.run
      (FixedGammaTargetSecondPayload.deadline (a + m))
      (FixedGammaTargetSecondPayload.startConfig B x w)
    d.state = FixedGammaTargetSecondPayload.qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTargetFirstPayload.firstPayloadTape B x w ((n + 1).testBit 0) ∧
      d.tape ⟨a + m + 1, by unfold tapeLength PairEncoding.pairLength; omega⟩ =
        some ((n + 1).testBit 1) ∧
      d.tape ⟨a + m + 2, hroom⟩ = some ((n + 1).testBit 0) ∧
      ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 2 < i.val →
        d.tape i = none := by
  obtain ⟨zeros, hg, hconsumed, -, -, htop, hdigit⟩ :=
    header_digits (Fin.append x w) hheader
  obtain rfl : zeros = 1 := by omega
  have h0 := hdigit 0 (by omega)
  rw [show 9 + 1 + 0 = 10 from rfl, show 1 - 1 - 0 = 0 from rfl] at h0
  obtain ⟨hq, hh, ht, hblank⟩ :=
    FixedGammaTargetSecondPayload.width_one_at_deadline (B := B) x w htag hg hroom
  rw [h0] at ht
  obtain ⟨-, -, hr1, hr2, -⟩ :=
    FixedGammaTargetFirstPayload.firstPayloadTape_layout (B := B) x w ((n + 1).testBit 0) hroom
  exact ⟨hq, hh, ht, by rw [ht, hr1, htop], by rw [ht, hr2], hblank⟩

/-- On a matching tag with the header `(0, 1)` the endpoint keeps the G2p-a
scratch register: the single digit of `0 + 1` at `a + m + 1`, blank afterwards,
with no room premise. -/
theorem secondPayload_zero_width_register {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (0, 1)) :
    let d := FixedGammaTargetSecondPayload.machine.run
      (FixedGammaTargetSecondPayload.deadline (a + m))
      (FixedGammaTargetSecondPayload.startConfig B x w)
    d.state = FixedGammaTargetSecondPayload.qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w ∧
      d.tape ⟨a + m + 1, by unfold tapeLength PairEncoding.pairLength; omega⟩ =
        some ((0 + 1).testBit 0) ∧
      ∀ i : Fin (tapeLength (PairEncoding.pairLength a m) B), a + m + 1 < i.val →
        d.tape i = none := by
  obtain ⟨zeros, hg, hconsumed, -, -, -, -⟩ := header_digits (Fin.append x w) hheader
  obtain rfl : zeros = 0 := by omega
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTargetSecondPayload.zero_width_at_deadline (B := B) x w htag hg
  obtain ⟨-, -, h1, h2⟩ := FixedGammaTerminatorScratchBootstrap.scratchTape_layout (B := B) x w
  exact ⟨hq, hh, ht, by rw [ht, h1]; rfl, fun i hi => by rw [ht]; exact h2 i hi⟩

end Pnp4.Frontier.ContractExpansion
