# Barrier certificate — hdx_locality

**Status: DRAFT.** Per Rule 7. Primary target is the **locality barrier
(B4)**, which has no dedicated `manifest.toml::[barriers]` field, so it
is documented here.

## Locality barrier (B4 — Chen et al., JACM 2022)  **(primary target)**

Status: `unknown` — **make-or-break**

The barrier: weak lower-bound techniques extend to circuits with
small-fan-in oracle gates, so they fail to magnify. Escape attempted:
the usefulness conjunct in `proof.lean` is stated against
`InPpolyDAGOracle` (the oracle-extended class), and `GlobalHardness P`
is an HDX local-to-global measure. **Auditor must adjudicate:** once the
HDX measure is made concrete, does it stay non-local (useful against
oracle-extended circuits), or does it collapse to a local measure that
B4 defeats? If the latter → `NoGoLog`.

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
