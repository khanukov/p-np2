import Pnp4.Frontier.SequentialMagnification.LocalHSG
import Pnp4.Frontier.SequentialMagnification.MMWMagnificationPort

/-!
# Capstone: `P ≠ NP` from a local hitting-set generator

This module composes the two halves of the sequential route into a single
statement, so that the remaining obligation can be read off one theorem.

```text
   local HSG at size parameter s,
   secure against space-B one-pass streaming tests          (open, pseudorandomness)
 + Shannon counting slack at s                              (counting, standard)
 + MMW19 Theorem 1.3                                        (published contract)
 ────────────────────────────────────────────────────────────────────────────
   P ≠ NP
```

Compare with the repository's other closure port, which requires
`NP ⊄ PpolyDAG` — a strictly stronger statement whose every known route dies to
truth-table hardwiring.

## What is actually open

Exactly one thing: `HitsStreamingTests G space` for a generator `G` that is
local at a *small* size parameter.  Everything else in the chain is either
proved here or is a faithfully recorded published theorem.

And the price of "small" is itself a theorem
(`seedLength_bound_of_injective_localGenerator`):

```text
2 ^ seedLen ≤ circuitCountBound n s
```

so lowering the size parameter `s` forces a shorter seed.  With `N = 2 ^ n` and
`s = N ^ μ`, the best known local generators against read-once devices have
`seedLen = Õ(N ^ (1/2))`, which is exactly why the published lower bound sits at
`μ ≈ 1` and cannot be pushed to the `μ = o(1)` regime that magnification needs.

## What this module does not do

It does not prove `P ≠ NP`, does not construct a generator, and does not prove
the MMW contract.  It is a reduction, and its value is that the thing it reduces
to is a concrete object with named parameters rather than an open-ended search
for a lower-bound technique.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

open Pnp4.AlgorithmsToLowerBounds

/--
**Capstone reduction.**

A local hitting-set generator at size parameter `s n`, secure against streaming
tests within the budget supplied by the published magnification contract,
together with the Shannon-counting slack at that parameter, yields `P ≠ NP`.
-/
theorem P_ne_NP_of_localHSG
    (C : MMWStreamingMagnification) (s : Nat → Nat) (n seedLen : Nat)
    (G : LocalGenerator n (s n) seedLen)
    (hHit : HitsStreamingTests G (C.spaceBudget (s n)))
    (hSlack : 2 * (Pnp3.Counting.easyFunctions n (s n)).card
      ≤ Fintype.card (TruthTable n)) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_mcsp_streaming_hardness C s n
    (MCSPStreamingHard_of_localHSG G hHit hSlack)

/--
Packaged form of the capstone hypothesis, mirroring
`SequentialResearchGapWitness` but exposing the pseudorandomness object
explicitly rather than the lower bound.
-/
structure LocalHSGWitness where
  /-- The published magnification contract. -/
  contract : MMWStreamingMagnification
  /-- The MCSP size parameter. -/
  sizeParam : Nat → Nat
  /-- The slice at which the generator is claimed. -/
  slice : Nat
  /-- Seed length of the generator. -/
  seedLen : Nat
  /-- The local generator itself. -/
  generator : LocalGenerator slice (sizeParam slice) seedLen
  /-- Hitting-set security within the contract's memory budget. -/
  hits :
    HitsStreamingTests generator (contract.spaceBudget (sizeParam slice))
  /-- Shannon-counting slack at the chosen size parameter. -/
  slack :
    2 * (Pnp3.Counting.easyFunctions slice (sizeParam slice)).card
      ≤ Fintype.card (TruthTable slice)

/-- Final consequence of a discharged local-HSG witness. -/
theorem P_ne_NP_of_localHSGWitness (w : LocalHSGWitness) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_localHSG w.contract w.sizeParam w.slice w.seedLen
    w.generator w.hits w.slack

/-- A local-HSG witness is one of the accepted closure routes. -/
def LocalHSGWitness.toSequentialWitness (w : LocalHSGWitness) :
    SequentialResearchGapWitness where
  contract := w.contract
  sizeParam := w.sizeParam
  slice := w.slice
  hardness := MCSPStreamingHard_of_localHSG w.generator w.hits w.slack

/-- …and therefore feeds the widened closure endpoint. -/
def LocalHSGWitness.toClosureRoute (w : LocalHSGWitness) : PvsNPClosureRoute :=
  PvsNPClosureRoute.sequential w.toSequentialWitness

end SequentialMagnification
end Frontier
end Pnp4
