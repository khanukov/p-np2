# Next steps after the sunflower lemma

The classical sunflower lemma is now fully formalised via `sunflower_exists_classic`.
The remaining work involving sunflowers focuses on integrating this combinatorial
step into the broader cover construction and complexity-theoretic applications.

## Follow-up tasks

- **RSpread and cover builder:** ensure the sunflower step is properly connected to
  the `RSpread` framework and the recursive `buildCover` procedure.  Tests for
  `sunflower_step` already exist, but the surrounding proofs in `BuildCover` and
  `cover_numeric` still contain placeholders.
- **Entropy branch interaction:** the sunflower argument interacts with the
  entropy-reduction branch (`exists_coord_entropy_drop`).  The auxiliary lemma
  `exists_restrict_half_real_aux` remains axiomatic and still requires a proof;
  classical reasoning (including `Classical.choice` and `noncomputable`
  sections) is fully acceptable, while a constructive variant can be treated as
  a later refinement.
- **Complexity consequences:** later files such as `NP_separation.lean` and
  `ComplexityClasses.lean` rely on several open conjectures.  Progress on the
  sunflower side feeds into these modules once the remaining axioms are removed.

This file serves as a lightweight roadmap for the sunflower component.  See
`TODO.md` for a global list of outstanding tasks.
