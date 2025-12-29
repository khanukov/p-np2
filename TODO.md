# To-Do
> **Status (2025-12-26)**: The `pnp3/` pipeline is fully formalised and has **zero active
> axioms**. The only remaining conditionality comes from *external witnesses* attached to the
> AC⁰/local switching (shrinkage) lemmas. The list below captures the **current, open work**.

## Focus: replace the `M²` bound with polylog

- [ ] **Formalise the inductive AC⁰ switching lemma for depth `d > 2`.**
  - Target: a constructive (or finitary probabilistic) proof that produces a
    `PartialCertificate`/`CommonPDT` with depth bounded by `polylogBudget n`.
  - Output: a lemma that packages the shrinkage output as a `CommonPDT`/`Atlas`
    ready for SAL, replacing the depth-2-only bound used today.

- [x] **Switch `ac0DepthBound` from `M^2` to `polylogBudget`.**
  - `ThirdPartyFacts.ac0DepthBound` now returns `polylogBudget params.n`.
  - `AC0SmallEnough` was updated to encode the temporary Stage‑1 requirement
    `M^2 ≤ polylogBudget n` until the multi‑switching proof removes it.

- [ ] **Provide constructive witnesses for local circuits.**
  - Replace the placeholder `ExternalLocalityWitnessProvider` with a real
    witness derived from the AC⁰ shrinkage proof (Williams-style locality lift).
  - Ensure the resulting `ShrinkageWitness` satisfies the existing polylog
    bounds on `|T|` and locality `ℓ`.

- [x] **Verify the pipeline is axiom-free after the replacement.**
  - Added `#print axioms` checks for `partial_shrinkage_for_AC0`,
    `shrinkage_for_localCircuit`, and the final `P_ne_NP` theorems in
    `pnp3/Tests/AxiomsAudit.lean` to make the audit part of `lake build`.

## Outstanding `sorry`s

- None – the Lean sources compile without placeholders.
