import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding

/-!
# Machine-facing tape interface for the content verifier — D1a

This module supplies the three P0-independent outputs of `VERIFIER_RETARGET_PLAN.md` §4.4. It
identifies the initial tape with the blank-padded complete input, exposes padding invariance in the
form used by machine proofs, and names the exact-step verifier obligation without fixing its
acceptance predicate.

`ContentVerifierBridgeFor` deliberately uses the existing `TM.accepts` semantics: the machine is
observed after exactly `runTime` steps. It provides neither a halting nor a within-time variant.
The polynomial inequality constrains the numeric runtime, but the API does not formally enforce
that `runTime` avoids carrying input-length advice. Advice avoidance is therefore a documented,
unenforced construction obligation.

**Progress classification (AGENTS.md): Infrastructure.** This interface constructs no verifier,
proves no lower bound, and reduces neither mainline source obligation.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- **The start tape is the blank-padded complete word.** For every in-range cell, the
`initialConfig` tape of the concatenated input equals `padRead` of that word, including past the
support where both sides are the blank `false`. -/
theorem initialConfig_tape_eq_padRead
    (M : Pnp3.Internal.PsubsetPpoly.TM.{0}) {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n)
    (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) :
    (M.initialConfig (Pnp3.ComplexityInterfaces.concatBitstring x w)).tape j
      = padRead (Pnp3.ComplexityInterfaces.concatBitstring x w) (j : Nat) := by
  by_cases hj : (j : Nat) < n + m
  · rw [Pnp3.Internal.PsubsetPpoly.TM.initial_tape_input (M := M)
        (Pnp3.ComplexityInterfaces.concatBitstring x w) hj]
    exact (padRead_lt (Pnp3.ComplexityInterfaces.concatBitstring x w) hj).symm
  · rw [Pnp3.Internal.PsubsetPpoly.TM.initial_tape_blank (M := M)
        (Pnp3.ComplexityInterfaces.concatBitstring x w) (Nat.le_of_not_gt hj)]
    exact (padRead_ge (Pnp3.ComplexityInterfaces.concatBitstring x w)
      (Nat.le_of_not_gt hj)).symm

/-- **Tape-determined acceptance.** Any two complete words with the same blank-padded tape are
`ContentAccepts`-equivalent. -/
theorem contentAccepts_of_initialConfig_tape_eq {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N N' : Nat}
    (z : PrefixBitVec N) (z' : PrefixBitVec N')
    (h : ∀ j, padRead z j = padRead z' j) :
    ContentAccepts codec z ↔ ContentAccepts codec z' :=
  ContentAccepts_iff_of_padRead_eq codec z z' h

/-- **The exact-step verifier obligation, named.** The acceptance predicate is an explicit
parameter, keeping this interface independent of any later semantic specialization.

The structure does not enforce that `runTime` is free of input-length advice; that remains an
external construction obligation. -/
structure ContentVerifierBridgeFor
    (acc : ∀ {N : Nat}, PrefixBitVec N → Bool) where
  M : Pnp3.Internal.PsubsetPpoly.TM.{0}
  c : Nat
  runTime_poly : ∀ n,
    M.runTime (n + Pnp3.ComplexityInterfaces.certificateLength n 1)
      ≤ (n + Pnp3.ComplexityInterfaces.certificateLength n 1) ^ c + c
  accepts_eq : ∀ n (x : Pnp3.ComplexityInterfaces.Bitstring n)
      (w : Pnp3.ComplexityInterfaces.Bitstring
             (Pnp3.ComplexityInterfaces.certificateLength n 1)),
    Pnp3.Internal.PsubsetPpoly.TM.accepts
        (M := M) (n := n + Pnp3.ComplexityInterfaces.certificateLength n 1)
        (Pnp3.ComplexityInterfaces.concatBitstring x w)
      = acc (Pnp3.ComplexityInterfaces.concatBitstring x w)

end ContractExpansion
end Frontier
end Pnp4
