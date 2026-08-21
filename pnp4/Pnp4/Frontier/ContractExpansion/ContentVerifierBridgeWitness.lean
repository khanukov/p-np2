import Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier
import Pnp4.Frontier.ContractExpansion.ContentVerifierTapeInterface

/-!
# The bridge specialization and the witness repackaging — D1b

This module supplies the two P0-dependent outputs of `VERIFIER_RETARGET_PLAN.md` §4.5: D1a's
predicate-parameterized obligation `ContentVerifierBridgeFor` instantiated at P0's computable
acceptance predicate `contentSemanticAccepts`, and the repackaging of any such bridge into the
frozen input-(2) interface `ContentPrefixExtensionNPWitness`.

**Nothing here is an instance.** The abbreviation only names the bridge type at P0's acceptance
predicate; it requires no supplied bridge and constructs no fields. The repackaging theorem is
conditional on a supplied `ContentVerifierBridge`, which remains the whole open machine obligation
(§1.3 caveat 1). No verifier Turing machine, runtime bound, or
`TM.accepts … = contentSemanticAccepts …` proof is constructed. The repackaging consumes
`runTime_poly` verbatim (§8, G6) and derives `correct` by
rewriting `TM.accepts` through `accepts_eq` and applying P0's `contentSemanticAccepts_correct`; it
proves no premise of the bridge and therefore establishes no NP membership for `L'`.

Applicable caveats reproduced from §1.3.

* **Caveat 1.** The `(★′)` bridge is the entire remaining machine obligation; supplying it is
  hypothetical here.
* **Caveat 5.** The obligation lives in this repository's machine model only: `TM.accepts` is
  evaluated at exactly step `runTime`, `runTime` is an unrestricted structure field, and no
  cross-model runtime-robustness theorem is formalized. The inherited `accepts_eq` field keeps
  that exact-step semantics at the explicit concatenated length `n + certificateLength n 1`, with
  no halting or within-time variant.
* **Caveat 6.** `runTime_poly` bounds the clock's magnitude only, so nothing in
  `ContentVerifierBridge` prevents an instance from exploiting the length-advice channel that
  `ModelAudit/RuntimeAdviceBarrier.lean` `lengthAdviceLanguage_in_repo_P` exhibits. G6 is a review
  convention, not a machine-checked gate; the CT route must not be described as advice-free.
* **Caveat 7.** Target-size feasibility is closed, machine feasibility is not: `L'` may not be
  described as proved polynomial-time verifiable or in NP.

**Progress classification (AGENTS.md): Infrastructure.** This module builds no machine, proves no
lower bound, and reduces neither mainline source obligation. **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- **The frozen target's bridge**: D1a's `ContentVerifierBridgeFor` at
`acc := contentSemanticAccepts codec`.  Only the acceptance predicate is fixed; every field — the
machine, the exponent, the polynomial runtime bound and the exact-step acceptance equation — is
still an input, and this alias constructs none of them. -/
abbrev ContentVerifierBridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :=
  ContentVerifierBridgeFor (fun {_} z => contentSemanticAccepts codec z)

/-- **A bridge discharges the frozen input-(2) interface.**  Pure repackaging: the machine, the
exponent and the polynomial runtime bound are taken over verbatim, and `correct` is P0's
`contentSemanticAccepts_correct` composed with the bridge's `accepts_eq` rewrite under the
certificate existential.

This is a *conditional* construction and proves nothing about `L'` on its own: it assumes exactly
the `(★′)` obligation that is open everywhere in the repository (§1.3 caveat 1), and its runtime
field is inherited rather than established (§8, G6). -/
def contentPrefixExtensionNPWitness_of_bridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (B : ContentVerifierBridge codec) :
    ContentPrefixExtensionNPWitness codec where
  M := B.M
  c := B.c
  runTime_poly := B.runTime_poly
  correct := fun n x =>
    (contentSemanticAccepts_correct codec x).trans
      (exists_congr fun w => by rw [B.accepts_eq n x w])

end ContractExpansion
end Frontier
end Pnp4
