import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage
import Complexity.Interfaces

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# TM-witness interface for NP-membership of the prefix-extension language

Block 11a of the downstream decision→search extraction — the **NP-membership**
track (orthogonal to the `¬ PpolyDAG` extraction chain).

A `VerifiedNPDAGLowerBoundSource` needs an `inNP : NP L` field.  The canonical
`NP` in this development is `NP_TM` (`pnp3/Complexity/Interfaces.lean`):

```
NP_TM L := ∃ (M : TM) (c k : Nat),
  (∀ n, M.runTime (n + certificateLength n k) ≤ (n + certificateLength n k)^c + c) ∧
  (∀ n x, L n x = true ↔ ∃ w, TM.accepts M (concatBitstring x w) = true)
```

so a proof of `NP (PrefixExtensionLanguage parser)` is exactly: a concrete verifier
Turing machine, a polynomial runtime bound, and a certificate-correctness
equivalence.  This file packages those three obligations as an explicit structure
`PrefixExtensionNPWitness` and proves the one-line bridge to `NP`, mirroring the
established `GapPartialMCSP_TMWitness` / `gapPartialMCSP_in_NP_TM_of_witness` idiom
(`pnp3/Models/Model_PartialMCSP.lean`).

## Runtime model caveat

The machine model is `Pnp3.Internal.PsubsetPpoly.TM`
(`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`): a **deterministic
single-tape** machine over the binary alphabet, with no separate read-only input tape and
a fixed tape length `n + runTime n + 1` (`TM.tapeLength`).  Its `runTime : ℕ → ℕ` is a
**structure field**, not a derived step count, and `TM.accepts` is evaluated **at exactly
step `runTime n`** (`TM.run` iterates `stepConfig` exactly `M.runTime n` times, then
checks `state = M.accept`); there is no halting predicate and no "within `t` steps"
quantifier.

Because the declared budget is also the evaluation point, the `runTime_poly` field below
is a genuine restriction on `M` rather than a self-certification.  What is **not**
formalized anywhere is a cross-model runtime-robustness statement relating this
single-tape, exact-step model to multi-tape or read-only-input-tape models, so this
structure should be cited as an NP-membership obligation *in this model*.

This is the minimal "obligations → NP-membership" interface: it makes the genuine
constructive obligations visible to callers (a real machine + runtime + correctness)
and is **not** a duplicate of the existing bare-`Prop` enumeration records
`PrefixExtensionNPVerifierBudget` / `PrefixExtensionNPVerifierPlan` (those itemize the
sub-tasks a *future* serialization/runtime proof must discharge in order to *build*
such a witness; this structure is the assembled TM-level package that directly yields
`NP`).

Scope discipline — NP-membership obligation interface only:

* the verifier TM, its runtime bound, and the certificate correctness are **explicit
  obligations** carried as fields — **none are proved here**;
* **no** lower-bound proof, **no** `VerifiedNPDAGLowerBoundSource` packaging change,
  **no** `SearchMCSPMagnificationContract` change, **no** endpoint or `P ≠ NP`
  consequence.
-/

/--
Concrete TM-witness package for NP-membership of the prefix-extension language.

Keeping this as an explicit structure (rather than a bare `Prop`) makes the
constructive obligations visible: a concrete verifier machine `M`, a polynomial
runtime bound, and a certificate-correctness equivalence for
`PrefixExtensionLanguage parser`.  This is precisely the data the canonical `NP_TM`
existential consumes.
-/
structure PrefixExtensionNPWitness
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) where
  /-- The verifier Turing machine reading the concatenated input+certificate. -/
  M : Pnp3.Internal.PsubsetPpoly.TM.{0}
  /-- Runtime polynomial exponent. -/
  c : Nat
  /-- Certificate-length polynomial exponent. -/
  k : Nat
  /-- The verifier runs in polynomial time in the concatenated length. -/
  runTime_poly : ∀ n,
    M.runTime (n + Pnp3.ComplexityInterfaces.certificateLength n k)
      ≤ (n + Pnp3.ComplexityInterfaces.certificateLength n k) ^ c + c
  /-- Certificate correctness: membership iff some certificate is accepted. -/
  correct : ∀ n (x : Pnp3.ComplexityInterfaces.Bitstring n),
    PrefixExtensionLanguage parser n x = true ↔
      ∃ w : Pnp3.ComplexityInterfaces.Bitstring
              (Pnp3.ComplexityInterfaces.certificateLength n k),
        Pnp3.Internal.PsubsetPpoly.TM.accepts
            (M := M)
            (n := n + Pnp3.ComplexityInterfaces.certificateLength n k)
            (Pnp3.ComplexityInterfaces.concatBitstring x w) = true

/--
**NP-membership from a TM witness.**  Any concrete `PrefixExtensionNPWitness`
yields `NP (PrefixExtensionLanguage parser)`, by unpacking the witness fields into
the canonical `NP_TM` existential.  (One-line bridge, mirroring
`gapPartialMCSP_in_NP_TM_of_witness`.)
-/
theorem prefixExtensionLanguage_in_NP_of_witness
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem)
    (W : PrefixExtensionNPWitness parser) :
    Pnp3.ComplexityInterfaces.NP (PrefixExtensionLanguage parser) := by
  exact ⟨W.M, W.c, W.k, W.runTime_poly, W.correct⟩

end ContractExpansion
end Frontier
end Pnp4
