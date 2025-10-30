# Next steps after the sunflower lemma
> **Status (2025-09-24)**: `sunflower_exists_classic` and its integration into `buildCover` are complete.  Remaining work concerns downstream complexity applications.

The classical sunflower lemma is fully formalised via `sunflower_exists_classic`.  The combinatorial step is now integrated with the recursive cover construction (`sunflower_step` in `cover2.lean`).

## Follow-up tasks

- **Quantitative refinements.**  The current sunflower step feeds into the coarse bound `Cover2.mBound`.  Any improvement to the combinatorial constants will immediately sharpen the numeric estimates in `cover_numeric.lean`.
- **Executable tooling.**  `sunflower_step` is used abstractly inside `buildCover`.  A constructive enumerator could reuse the same lemma but would need efficient data structures for supports.
- **Complexity consequences.**  Complexity-theoretic files (`NP_separation.lean`, `ComplexityClasses.lean`) still rely on axioms.  Progress on magnification or the constructive bridge to `MCSP` will propagate the sunflower advances to final `P ≠ NP` statements.  Constructive `P ⊆ P/poly` is now available, so the remaining axioms are `magnification_AC0_MCSP` и `FCE_implies_MCSP`.

For a global list of outstanding tasks see `TODO.md`.
