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

- [x] **[A1]** Import the depth-2 constructive switching lemmas from the `DEPTH2_STATUS.md` effort,
  wire them into `ThirdPartyFacts/Facts_Switching.lean`, and replace the brute-force
  `buildPDTFromSubcubes` proof in `partial_shrinkage_for_AC0` with the new constructive proof.
  - [x] Move the proven depth-2 lemmas (e.g. `partial_shrinkage_single_clause`,
    `partial_shrinkage_small_dnf`, `depth2_dnf`, `depth2_cnf`) out of the archive and into the
    active `pnp3/ThirdPartyFacts` tree (`Depth2_Constructive.lean`,
    `Depth2_Helpers.lean`, `ConstructiveSwitching.lean`).
  - [x] Add the missing glue lemmas to convert the depth-2 shrinkage output into a
    `PartialCertificate`, including explicit depth and error bounds.
  - [x] Update `shrinkage_for_AC0` to rely on the new constructive proof while keeping the existing
    interface stable for downstream modules.
- [ ] **[A1 → A2]** Formalise the inductive AC⁰ switching lemma for depth `d > 2` (probabilistic or
  combinatorial proof), and expose a helper lemma that packages the shrinkage output as a
  `CommonPDT`/`Atlas` ready for SAL.
  - [x] Добавить вспомогательные леммы, переводящие shrinkage-свидетель AC⁰ в `CommonPDT`
    с явными оценками глубины и ошибки (готово в `pnp3/ThirdPartyFacts/Facts_Switching.lean`).
  - [x] **[A2]** Formalise the local-circuit multi-switching argument needed for
  `shrinkage_for_localCircuit` (Williams-style locality lift).
  - [x] Переписать `shrinkage_for_localCircuit` через
    `familyIsLocalCircuit_iff_shrinkage`, чтобы доказательство зависело только от
    shrinkage-сертификата, а не от внутренней структуры `LocalCircuitWitness`.
  - [x] Вынести универсальный конструктор `shrinkage_for_localCircuit_of_shrinkage`,
    который упаковывает готовый shrinkage-сертификат в требуемую тройку.
  - [x] Fill in the proof skeleton under `Facts/LocalityLift/ProofSketch/` and implement the
    construction of the test set `T` together with the required polylog bounds.
  - [x] Add helper lemmas tying `ShrinkageWitness`/`LocalityWitness` test sets to
    `testSetOfAlive`, so downstream arguments can reuse the same deterministic
    construction without unfolding summaries.
  - [x] Expose a direct lemma that the provided `localityWitness` test set respects the
    polylog budget (`testSet_card_le`), so downstream modules can use it without
    unpacking witnesses.
  - [x] Wire an external shrinkage witness provider through
    `pnp3/ThirdPartyFacts/LocalityLift.lean`, so the canonical placeholder can be
    replaced by a real witness as soon as it is supplied.
  - [x] Prove `shrinkage_for_localCircuit` by composing the locality lift with the proven AC⁰
    shrinkage lemma, yielding a `Shrinkage` object of depth `ℓ * (log₂(M+2) + d + 1)` (or tighter).
- [x] **[cleanup]** Remove the residual “external witness” notes in `AXIOMS.md`,
  `AXIOM_ANALYSIS_FINAL.md`, and `FinalResult.lean` once the shrinkage lemmas are proven.

## Outstanding `sorry`s (as of 2025-12-26)

- None – the Lean sources compile without placeholders.
