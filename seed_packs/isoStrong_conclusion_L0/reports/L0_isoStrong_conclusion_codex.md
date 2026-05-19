# L0 iso-strong conclusion probe report (handle: codex)

## Scope and objective

- Staging Lean file: `pnp3/Tests/IsoStrongConclusionProbe.lean`.
- Attempted direction: **N** (structural negation) first, per worker prompt.
- Constraint: keep Lean file ≤300 LOC and avoid hidden payload / forbidden imports.

## What landed

A kernel-checked partial theorem was landed:

- `canonical_isoStrong_implies_eventual_strict_slack`

Statement (informal): if canonical `IsoStrongFamilyEventually` holds for a global DAG witness `W`, then for sufficiently large slices and admissible `β`, one gets:

`m + 2 < 2^(2^m - κ m β)`.

This is the exact arithmetic side needed for the proposed Direction-N pigeonhole contradiction.

## Why full Direction N did not land in this L0

The full negative theorem needs a constructive finite combinatorics bridge inside Lean:

1. Convert strict slack into a lower bound on the number of valid agreement extensions under `AgreeOnValues`.
2. Bound YES-side representable extensions by `m+2` (from canonical `sYES = 1` counting envelope).
3. Build explicit `z` (valid encoding, agrees on `D`, but not in YES) to contradict forcing.

Step (1)+(3) require a nontrivial glue lemma over:

- `ValidEncoding`, `encodePartial`, `decodePartial`,
- coordinate-set semantics in `MCSPGapLocality`,
- and subcube cardinality counting in the encoded bitstring representation.

That combinatorial bridge did not fit safely into this ≤300 LOC L0 while preserving audit hygiene.

## Audits and policy checks

- Forbidden-pattern grep on staging file: no matches.
- No forbidden imports used.
- No `axiom` / `sorry` / `admit` / `opaque` / `native_decide` introduced.

## L1 handoff (precise missing theorem)

A targeted L1 theorem is needed:

- Given `ValidEncoding p yYes`, `D : Finset (Fin (Partial.tableLen p.n))`, and strict slack bound,
  construct a valid `z` with `AgreeOnValues D yYes z` and `z ∉ Yes`.

This is the minimal theorem that should unlock full Direction N refutation.

YELLOW_PARTIAL_LANDING
