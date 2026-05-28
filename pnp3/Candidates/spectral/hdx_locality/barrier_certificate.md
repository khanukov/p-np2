# Barrier certificate — hdx_locality

**Status: DRAFT.** Per Rule 7. Primary target is the **locality barrier
(B4)**, which has no dedicated `manifest.toml::[barriers]` field, so it
is documented here.

## Locality barrier (B4 — Chen et al., JACM 2022)  **(primary target — attack-succeeded)**

Status: `not-overcome — current shape is self-contradictory under B4`

Auditor verdict (May 2026): the chosen escape mechanism is reversed.
Stating usefulness against the **oracle-extended** class
(`InPpolyDAGOracle`) requires `GapMCSP ∉ InPpolyDAGOracle`, but the B4
fact recorded in `Docs/BARRIER_CATALOGUE.md` says exactly the opposite —
Gap-MCSP **does** admit oracle-extended small circuits. The conjuncts
of `SourceTheorem_hdx_locality` are therefore jointly inconsistent
under any inhabited `IsGapMCSP` slice. The honest B4 escape is to prove
usefulness against **plain** `PpolyDAG` via a technique that
**does not lift** to oracle-augmented circuits (`NonOracleRobust(P)`);
the current shape demands the opposite. Formal witness:
`hdx_locality_current_shape_impossible` in `proof.lean`.

## Relativization

Status: `unknown`

Must use specific `gapPartialMCSP` + HDX structure; if it uses only
oracle-agnostic facts it relativizes (B1). The oracle-extended usefulness
target is, however, evidence of intended non-relativizing behavior.

## Natural proofs (Razborov–Rudich)

Status: `unknown`

Not the primary mechanism. If `GlobalHardness` is constructive and large,
re-examine against RR. Likely interacts with B4 rather than B2.

## Algebrization

Status: `unknown`

HDX arguments are partly spectral/algebraic; check whether the global-
hardness step survives a multilinear-extension oracle (B3).

## Hardwiring (Probe 2)

Status: `not-checked` — priority gate

`NotHardwired P` is the Rule 5 exclusion lemma. Discharge against
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` before intake.

## Collapse-vs-contradiction (Rule 8)

Status: `genuine-contradiction` — bridge yields a direct separation.

## Formal witnesses (to be filled by engineer)

- Oracle-extended usefulness (non-locality) step: `proof.lean:<line>` (TODO)
- HDX global-hardness witness (`GlobalHardness`): `proof.lean:<line>` (TODO)
- Hardwiring exclusion lemma (`NotHardwired`): `proof.lean:<line>` (TODO)
