# L1 iso-strong conclusion probe failure note (handle: codex2)

## Executive verdict
INCONCLUSIVE_NEEDS_L2

## What was attempted
- Loaded required context files and inspected the existing L0 probe.
- Inspected `CanonicalAsymptoticDecider` primitives for `size1Candidates`, `decideYesAt1_iff`, and size-1 membership lemmas.
- Inspected the forcing/iso-strong shape in `AsymptoticDAGBarrierTheorems` and encoding locality primitives in `MCSPGapLocality`.

## Why no kernel-checked L1 lemma was landed in this session
The blocker in this session is not the arithmetic pigeonhole idea itself; it is the amount of glue required to bridge all of the following simultaneously in a robust Lean proof without introducing brittle ad-hoc coercion lemmas:

1. A finite-domain function-space counting argument over `(Finset.univ \ D).attach → Bool` at exactly the needed cardinality form.
2. A compatibility bridge from size-1 *circuit syntax* (`Circuit p.n`) to free-coordinate *trace functions* on table indices (with decoding semantics and consistency obligations).
3. A constructive `z` build that preserves `ValidEncoding` and proves `AgreeOnValues` on value coordinates while fixing free coordinates as fully-masked labels.
4. A contradiction route from `z ∈ Yes` to a trace equality against one of the size-1 candidates via `decideYesAt1_iff` + consistency semantics.

The current codebase has the ingredients, but this composition requires a dedicated intermediate API layer (trace extraction, class indexing, and reusable cardinality wrappers). That layer is larger than what could be landed safely in this single pass without risking regressions or fragile proof scripts.

## Corrected pigeonhole argument (explicitly used, but not yet formalized)
I did **not** use the false shortcut “`|YES| ≤ m+2` globally.”

Correct plan remains:
- Only `m+2` size-1 candidates exist.
- Each candidate induces exactly one Boolean trace on free coordinates outside `D`.
- Free-coordinate labelings are `2^r` where `r = |free|`.
- If `m+2 < 2^r`, choose a labeling not equal to any candidate trace.
- Encode that labeling into a valid `z` agreeing with `yYes` on `D`, forcing `z ∉ YES`.

## L2 request
A focused L2 design should first land a small reusable trace API in this test probe file (or explicitly approved shared test helper), then prove:
- candidate-trace image card bound,
- existence of a non-candidate trace,
- constructive `z` contradiction lemma.

