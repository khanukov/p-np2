# N-np formalization repository

This repo contains experimental Lean code attempting to formalize aspects of a hypothetical proof that `P ≠ NP`. The development is highly incomplete. Several files include placeholders (`sorry` or `admit`). In particular:

- `Boolcube.lean` defines basic structures and begins a construction for rectangle covers. The major lemmas rely on unproven assumptions.
- `family_entropy_cover.lean` and `merge_low_sens.lean` previously declared axioms. They now contain theorem statements with proof holes marked by `sorry`.

The repository is mainly a research sketch rather than a working proof. See `experiments/` for a small Python script exploring combinatorial data.
