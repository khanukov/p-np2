import Complexity.Uniform.V1.FixedGammaPayloadRoundDriver

namespace Pnp3.Tests.UniformV1FixedGammaPayloadRoundDriverSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadRoundStep
open Complexity.Uniform.V1.FixedGammaPayloadRoundDriver

def check_boundaryClock : Nat → Nat → Nat := boundaryClock

theorem check_boundaryClock_one (zeros : Nat) : boundaryClock zeros 1 = 0 :=
  boundaryClock_one zeros

theorem check_boundaryClock_succ {zeros k : Nat} (hk : 1 ≤ k) :
    boundaryClock zeros (k + 1) = boundaryClock zeros k + roundCost zeros :=
  boundaryClock_succ hk

theorem check_boundaryClock_two (zeros : Nat) :
    boundaryClock zeros 2 = roundCost zeros :=
  boundaryClock_two zeros

theorem check_prefix_physical_bound {a m zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m) (hk : 1 ≤ k)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    8 + zeros + k < a + m :=
  prefix_physical_bound x w hk hprefix

theorem check_rounds_false_exact {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (r : Nat) (hr : r < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 10 + zeros + r →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    RoundInvariant B x w zeros (r + 1)
      (machine.run (r * roundCost zeros) (startConfig B x w zeros)) :=
  rounds_false_exact x w htag hg r hr hprefix

theorem check_boundary_reachable {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k ≤ zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    RoundInvariant B x w zeros k
      (machine.run (boundaryClock zeros k) (startConfig B x w zeros)) :=
  boundary_reachable x w htag hg hk hkz hprefix

theorem check_last_boundary_reachable {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    RoundInvariant B x w zeros zeros
      (machine.run (boundaryClock zeros zeros) (startConfig B x w zeros)) :=
  last_boundary_reachable x w htag hg hzero hprefix

end Pnp3.Tests.UniformV1FixedGammaPayloadRoundDriverSurfaceTests
