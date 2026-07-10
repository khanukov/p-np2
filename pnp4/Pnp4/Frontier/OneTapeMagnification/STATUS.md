# One-tape small-threshold status

Status: **PARAMETER BARRIER PROVED; FINITE LOCAL-HSG LAYER COMPLETE; NO SMALL-THRESHOLD LOWER BOUND OR CAPSTONE**

Primary sources:

- Cheraghchi, Hirahara, Myrisiotis, Yoshida, [*One-Tape Turing Machine and Branching Program Lower Bounds for MCSP*](https://drops.dagstuhl.de/storage/00lipics/lipics-vol187-stacs2021/LIPIcs.STACS.2021.23/LIPIcs.STACS.2021.23.pdf), STACS 2021 (CHMY).
- Viola, [*Pseudorandom Bits and Lower Bounds for Randomized Turing Machines*](https://theoryofcomputing.org/articles/v018a010/v018a010.pdf), Theory of Computing 2022.
- Chen, Jin, Williams, [*Hardness Magnification for all Sparse NP Languages*](https://eccc.weizmann.ac.il/report/2019/118/download), ECCC TR19-118 (CJW), used only for its exact quantifier order.

## Result classification

This branch proves the parameter obstruction in the published Viola-to-CHMY
route.  It does not prove a one-tape lower bound at the magnification-admissible
small threshold and does not produce a `P != NP` capstone.  Under the
repository policy it remains a restricted lower-bound side track unless an
explicit `PpolyDAG` / `VerifiedNPDAGLowerBoundSource` bridge is later proved.

## Closed operational and finite layers

The following ingredients are now formalized:

- A concrete deterministic one-tape convention with a separate one-way
  read-only input tape and a two-way read/write work tape.  End-of-input,
  left-boundary, stay-move, transition, halting, and exact step-count
  conventions are explicit.
- A randomized extension with a separate one-way finite random tape.  The
  random bits are independent of the immutable input and the work tape.
- Exact rational acceptance probabilities over finite random tapes and exact
  product averages for both the uniform-table experiment and the
  generator-seed experiment.
- `DAGLocalGenerator`, whose locality assertion is the CHMY circuit-complexity
  statement: every fixed-seed output table has a bounded standard DAG.  It is
  not a bounded-dependency claim for each output coordinate.
- The exact finite CHMY gap: completeness at least `2/3` on generator outputs
  and uniform acceptance below `1/2` force distinguishing gap strictly greater
  than `1/6`.
- Canonical-DAG-code counting.  If
  `DAGCodec.codeLength n threshold + 2 < 2^n`, the explicit easy-table
  superset occupies less than one quarter of all truth tables.
- The composed finite exclusion: a generator that fools the concrete machine
  within `1/6` rules out two-sided bounded-error MCSP behavior at that finite
  length, under the explicit code-length inequality.

These results use the exact standard-DAG MCSP target, including the
`AND`/`OR`/`NOT` basis filter.  The counting image may include a harmless
broader structural-code superset, which only strengthens its upper-bound role;
every semantic `HasCircuit` witness still satisfies the target-basis filter.

The finite exclusion is conditional on an explicit generator and an explicit
fooling hypothesis.  No small-seed generator is postulated or hidden in a
structure, instance, contract, or axiom.

## Proved published-parameter barrier

The published sufficient seed/locality bound has the form

```text
soft-O((sqrt(t) + log(1/epsilon)) * log(q * 2^ell * t)).
```

For constant error, constant query count, and no oracle-query bits, its power
contribution is `sqrt(t)`, with additional polylogarithmic factors.  At
`t(N) = N^(101/100)`, the exact power exponent is

```text
(101/100) / 2 = 101/200 = 0.505.
```

`published_viola_chmy_square_root_time_exponent` proves the rational identity,
and `published_viola_chmy_parameters_do_not_certify_small_threshold` proves
that every rational target exponent strictly below `101/200` fails even to
dominate this bare power term.  The omitted polylogarithmic factor only makes
the published sufficient bound larger once it is at least one.

This is a barrier for the **published sufficient construction and bound**.  It
is not `no_small_seed_prg_exists`, not a seed-length lower bound for arbitrary
PRGs/HSGs, and not evidence that a different generator cannot close the gap.

## Paper-level quantifier and model boundaries

CHMY's deterministic model is not the MMW random-access streaming RAM and is
not the repository's loaded-input, single-read/write-tape TM.  The randomized
experiments here always retain an independent random tape in both the uniform
and generator distributions.

Theorem 16 uses `1/2 < mu' < mu < 1`, subpolynomial query length, and time
approximately `N^(2(mu' - o(1)))`.  The later argument under `P = NP` obtains
a polynomial `p`; if `p(x) = O(x^d)`, the admissible interval must additionally
respect `d * mu <= 1/100`.  A future formalization must keep `mu` symbolic
until it extracts that actual simulation degree.

The full-version appendix contains a printed sign error after deriving the
consequence under `P = NP`: the contrapositive and surrounding argument require
membership in the one-tape time class, not the printed non-membership.  No Lean
statement should encode the inconsistent printed direction.

CJW's sparse-language consequence has quantifiers

```text
forall k, exists L_k in NP, L_k notin SIZE(n^k),
```

not one fixed language hard against every polynomial size.  It therefore does
not by itself prove `NP not_subset P/poly`.

## Exact open frontier

No one-tape lower bound at the required small threshold, no generator with the
required seed/locality exponent, and no magnification capstone has been proved.
The one research question retained by this branch is:

> Construct a local HSG for the exact CHMY one-tape class whose seed/locality exponent is at most the admissible `mu0`, improving the published square-root-in-time dependence enough to instantiate Lemma 15 at the small threshold.

This question remains prose only.  It must not be represented by an axiom,
typeclass, `Contract`, `Source`, `Provider`, structure field, or implicit
instance.

## Later-literature check (through 2026-07-09)

- The [journal version of CHMY](https://link.springer.com/article/10.1007/s00224-022-10113-9) retains the large-threshold one-tape result and the same Appendix-A magnification direction; it does not supply a small-threshold lower bound.
- [ECCC TR25-017](https://eccc.weizmann.ac.il/report/2025/017/) develops a square-root-space simulation for multitape time, not the local HSG/PRG needed here.
- [ECCC TR26-064, revision 3](https://eccc.weizmann.ac.il/report/2026/064/) improves read-once branching-program pseudorandomness parameters but does not remove the square-root-in-time exponent in the Viola-to-CHMY route.

No primary source found in this check closes the magnification-admissible
small-`mu` one-tape frontier.  This negative literature finding is not itself
a lower bound.
