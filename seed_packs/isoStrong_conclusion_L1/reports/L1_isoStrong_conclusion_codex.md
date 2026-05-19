# L1 iso-strong conclusion probe (codex)

## 1. Executive verdict

INCONCLUSIVE_NEEDS_L2

## 2. What landed

No new Lean theorem landed in this session.

I confirmed the existing L0 extraction in `pnp3/Tests/IsoStrongConclusionProbe.lean` is intact:
- `F_Mof`
- `canonical_isoStrong_implies_eventual_strict_slack`

## 3. Corrected pigeonhole argument

I explicitly did **not** use the false global claim

> "the YES set has cardinality ≤ m+2".

Reason: there are only `m+2` size-1 circuits, but each fixed size-1 circuit can be consistent with many partial tables, so this does **not** bound the count of YES partial tables.

The correct route is trace-diagonalisation over free value coordinates outside `D`:

1. Let `free := Finset.univ \ D` and `r := free.card`.
2. A size-1 candidate induces a single Boolean trace `free → Bool` on these free coordinates.
3. Number of size-1 candidates is `m+2`; hence number of candidate traces is at most `m+2`.
4. Number of all labels on `free` is exactly `2^r`.
5. Under slack `m+2 < 2^r`, choose a label not equal to any candidate trace.
6. Build `z` by copying `yYes` on `D` and setting free coordinates to that label (with mask true on free coordinates).
7. Then `z` is valid, agrees on `D`, and cannot be YES; otherwise a size-1 circuit would match the free trace, contradiction.

## 4. Remaining blockers

The immediate blocker for landing code in one pass is proof-engineering complexity around:

- clean finite-type packaging for traces over `(Finset.univ \ D).attach`;
- bridging the route-level slack shape to a reusable cardinality lemma without introducing brittle coercion chains;
- efficient proof of the `¬ z ∈ Yes` step through current `decideYesAt1_iff`/candidate-consistency interfaces.

A robust L2 should first isolate a small helper API for:

- candidate trace extraction,
- image-cardinality upper bound,
- existence of non-image label under strict cardinality inequality.

## 5. Next action

open_isoStrong_conclusion_L2_design
