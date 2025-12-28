# To-Do
> **Status (2025-12-26)**: The active `pnp3/` pipeline is fully formalised and has **zero active
> axioms**. The only remaining conditionality comes from *external witnesses* attached to the
> AC⁰/local switching (shrinkage) lemmas. The items below list the remaining work **within
> `pnp3/`** only.

## Switching / shrinkage completion (A1/A2)

> **Status (2025-12-26)**: SAL + counting + magnification are complete; Part A still relies on
> `FamilyIsAC0`/`FamilyIsLocalCircuit` witnesses in
> `pnp3/ThirdPartyFacts/Facts_Switching.lean`. The checklist below is the only open technical work
> in the active pipeline.

- [ ] **[A1]** Import the depth-2 constructive switching lemmas from the `DEPTH2_STATUS.md` effort,
  wire them into `ThirdPartyFacts/Facts_Switching.lean`, and replace the brute-force
  `buildPDTFromSubcubes` proof in `partial_shrinkage_for_AC0` with the new constructive proof.
  - [ ] Move the proven depth-2 lemmas (e.g. `partial_shrinkage_single_clause`,
    `partial_shrinkage_small_dnf`, `depth2_dnf`, `depth2_cnf`) out of the archive and into the
    active `pnp3/ThirdPartyFacts` tree.
  - [ ] Add the missing glue lemmas to convert the depth-2 shrinkage output into a
    `PartialCertificate`, including explicit depth and error bounds.
  - [ ] Update `shrinkage_for_AC0` to rely on the new constructive proof while keeping the existing
    interface stable for downstream modules.
- [ ] **[A1 → A2]** Formalise the inductive AC⁰ switching lemma for depth `d > 2` (probabilistic or
  combinatorial proof), and expose a helper lemma that packages the shrinkage output as a
  `CommonPDT`/`Atlas` ready for SAL.
- [ ] **[A2]** Formalise the local-circuit multi-switching argument needed for
  `shrinkage_for_localCircuit` (Williams-style locality lift).
  - [ ] Fill in the proof skeleton under `Facts/LocalityLift/ProofSketch/` and implement the
    construction of the test set `T` together with the required polylog bounds.
  - [ ] Replace the placeholder one-point witness in `Facts/LocalityLift` with the real shrinkage
    witness, and re-export it through `pnp3/ThirdPartyFacts/LocalityLift.lean`.
  - [ ] Prove `shrinkage_for_localCircuit` by composing the locality lift with the proven AC⁰
    shrinkage lemma, yielding a `Shrinkage` object of depth `ℓ * (log₂(M+2) + d + 1)` (or tighter).
- [ ] **[cleanup]** Remove the residual “external witness” notes in `AXIOMS.md`,
  `AXIOM_ANALYSIS_FINAL.md`, and `FinalResult.lean` once the shrinkage lemmas are proven.

## Outstanding `sorry`s (as of 2025-12-26)

- None – the Lean sources compile without placeholders.
