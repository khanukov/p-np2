# L1 session 2 structured failure (codex53)

## Blocker summary

Attempted to land the general diagonal and not-YES bridge in
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, but the direct port from the
canonical L1 proof pattern failed at elaboration because of a mismatch around
free-row index domain representation:

- expected domain in new lemmas is over `((Finset.univ \ D).attach)`;
- while constructing the diagonal table and proving trace-equality from
  consistency, Lean inferred a nested subtype layer that did not line up with
  the `label` domain in the drafted theorem statements.

This produced hard type mismatches in the key steps:

1. constructing `label` values at free rows in the diagonal table;
2. extensional trace-equality proof (`traceCircuitOnRows ... C = label`).

A second blocker was API mismatch in this file's import context for a
previously-used yes-membership unpacking pattern (`gapSlice_yes_iff` based),
which is not available in this probe file's current imports and required
reworking to a direct `gapSliceOfParams`/`GapPartialMCSPPromise` path.

Given the combination of (a) subtype-shape mismatch at the core trace lemma and
(b) command budget pressure after repeated full rebuild attempts, I reverted the
Lean theorem edits to keep repository state green and preserved this as a
structured failure for the next session.

## Recommended next-session unblock path

1. Introduce a local alias for free rows with an explicit type:
   `FreeRow p D := {j : Fin (Partial.tableLen p.n) // j ∈ Finset.univ \ D}`.
2. Restate all new general session-2 lemmas over `FreeRow p D` (not directly
   over `.attach`) to avoid nested subtype inference.
3. Add coercion helper lemmas from `FreeRow p D` to row index and to
   membership proofs; then replay canonical diagonal proof skeleton.
4. Keep yes-membership unpacking via `simpa [gapSliceOfParams, GapPartialMCSPPromise]`.
