import Complexity.Uniform.V1.FixedGammaTerminatorScratchBootstrap
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaPayloadDispatcherHeaderValueBridge

/-!
# Header meaning of the gamma terminator scratch bootstrap (Part A G2p-a)

The fixed bootstrap `FixedGammaTerminatorScratchBootstrap` writes the literal
bit `true` at scratch cell `a + m + 1`.  On a matching tag this bridge
identifies that bit with the content header:

* at the bootstrap's length-only deadline, `qReject` holds exactly when
  `contentHeader? = none`;
* if `contentHeader? z = some (n, consumed)`, then for some `zeros` with
  `consumed = 2 * zeros + 1` and `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)` the
  deadline endpoint is `qTerm` at head `8 + zeros` with the scratch tape, and
  the scratch cell holds `(n + 1).testBit zeros`, the leading binary digit of
  `n + 1`.

Only that one digit reaches the tape.  The shuttle crosses the cells holding the
remaining `zeros` digits of `n + 1` (the gamma payload), but neither decodes nor
copies their digits, and nothing here claims content
acceptance, parser execution, or any lower bound; this is not P-vs-NP mainline
progress.
-/

namespace Pnp4.Frontier.ContractExpansion

open Pnp3.Complexity.Uniform.V1

/-- On matching tags, the bootstrap rejects at its deadline exactly when the
content header is absent. -/
theorem scratchBootstrap_qReject_iff_contentHeader_none {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (FixedGammaTerminatorScratchBootstrap.machine.run
      (FixedGammaTerminatorScratchBootstrap.deadline (a + m))
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w)).state =
        FixedGammaTerminatorScratchBootstrap.qReject ↔
      contentHeader? (Fin.append x w) = none := by
  rw [← Option.not_isSome_iff_eq_none, ← fixedGamma_header_contract]
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | none =>
      obtain ⟨hq, _, _⟩ :=
        FixedGammaTerminatorScratchBootstrap.malformed_at_deadline (B := B) x w htag hg
      exact ⟨fun _ => nofun, fun _ => hq⟩
  | some zeros =>
      obtain ⟨hq, _, _⟩ :=
        FixedGammaTerminatorScratchBootstrap.run_deadline (B := B) x w htag hg
      exact ⟨fun hr => absurd (hq.symm.trans hr) (by decide), fun hn => absurd rfl hn⟩

/-- On matching tags with header `(n, consumed)`, the bootstrap's deadline
endpoint stores the leading binary digit of `n + 1` in scratch cell
`a + m + 1`. -/
theorem scratchBootstrap_scratch_eq_leading_bit {a m B n consumed : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hheader : contentHeader? (Fin.append x w) = some (n, consumed)) :
    ∃ zeros, consumed = 2 * zeros + 1 ∧ 2 ^ zeros ≤ n + 1 ∧
      n + 1 < 2 ^ (zeros + 1) ∧
      let d := FixedGammaTerminatorScratchBootstrap.machine.run
        (FixedGammaTerminatorScratchBootstrap.deadline (a + m))
        (FixedGammaTerminatorScratchBootstrap.startConfig B x w)
      d.state = FixedGammaTerminatorScratchBootstrap.qTerm ∧ d.head.val = 8 + zeros ∧
        d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w ∧
        d.tape ⟨a + m + 1, by unfold tapeLength PairEncoding.pairLength; omega⟩ =
          some ((n + 1).testBit zeros) := by
  obtain ⟨zeros, payload, hg, hpayload, hn, hconsumed⟩ :=
    (contentHeader?_eq_some_iff_gammaZeros_payload _).1 hheader
  have hlt : payload < 2 ^ zeros := by
    rw [VirtualZeroTailReader.readNatBE_eq_padWord] at hpayload
    exact readNatBE_lt_two_pow _ _ _ hpayload
  have hbit : (n + 1).testBit zeros = true := by
    rw [hn, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
    rfl
  obtain ⟨hq, hh, ht⟩ :=
    FixedGammaTerminatorScratchBootstrap.run_deadline (B := B) x w htag hg
  refine ⟨zeros, hconsumed, by omega, by rw [Nat.pow_succ]; omega, hq, hh, ht, ?_⟩
  rw [ht, hbit]
  exact (FixedGammaTerminatorScratchBootstrap.scratchTape_layout (B := B) x w).2.2.1

end Pnp4.Frontier.ContractExpansion
