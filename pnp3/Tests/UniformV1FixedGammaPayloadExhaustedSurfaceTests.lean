import Complexity.Uniform.V1.FixedGammaPayloadExhausted

namespace Pnp3.Tests.UniformV1FixedGammaPayloadExhaustedSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadRoundStep
open Complexity.Uniform.V1.FixedGammaPayloadExhausted

def check_exhaustedTail : Nat → Nat := exhaustedTail
def check_exhaustedClock : Nat → Nat := exhaustedClock

theorem check_exhausted_tail_trace {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
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
      d.tape = roundTape B x w zeros zeros :=
  exhausted_tail_trace x w hg hzero hprefix c hc

theorem check_exhausted_tail_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B)
    (hc : RoundInvariant B x w zeros zeros c) :
    let d := machine.run (exhaustedTail zeros) c
    d.state = qExhausted ∧ d.head.val = 8 + zeros ∧
      d.tape = roundTape B x w zeros zeros :=
  exhausted_tail_exact x w hg hzero hprefix c hc

theorem check_exhausted_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B)
    (hc : RoundInvariant B x w zeros zeros c) (s : Nat) (hs : s < exhaustedTail zeros) :
    (machine.run s c).state ≠ qExhausted :=
  exhausted_strict x w hg hzero hprefix c hc s hs

theorem check_exhausted_absorbing {N B : Nat} (c : Config stateCount N B)
    (hc : c.state = qExhausted) (s : Nat) : machine.run s c = c :=
  exhausted_absorbing c hc s

theorem check_exhausted_reachable {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (exhaustedClock zeros) (startConfig B x w zeros)
    d.state = qExhausted ∧ d.head.val = 8 + zeros ∧
      d.tape = roundTape B x w zeros zeros :=
  exhausted_reachable x w htag hg hzero hprefix

theorem check_exhausted_no_clamp_facts {a m B zeros : Nat}
    (hp : 8 + 2 * zeros < a + m) :
    0 < 7 + zeros ∧ 8 + 2 * zeros < tapeLength (pairLength a m) B :=
  exhausted_no_clamp_facts hp

end Pnp3.Tests.UniformV1FixedGammaPayloadExhaustedSurfaceTests
