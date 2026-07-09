# One-tape small-threshold audit

Status: **PARAMETER AUDIT IN PROGRESS; NO LOWER BOUND CLAIMED**

Primary sources:

- Cheraghchi, Hirahara, Myrisiotis, Yoshida, [*One-Tape Turing Machine and Branching Program Lower Bounds for MCSP*](https://drops.dagstuhl.de/storage/00lipics/lipics-vol187-stacs2021/LIPIcs.STACS.2021.23/LIPIcs.STACS.2021.23.pdf), STACS 2021 (CHMY).
- Viola, [*Pseudorandom Bits and Lower Bounds for Randomized Turing Machines*](https://theoryofcomputing.org/articles/v018a010/v018a010.pdf), Theory of Computing 2022.
- Chen, Jin, Williams, [*Hardness Magnification for all Sparse NP Languages*](https://eccc.weizmann.ac.il/report/2019/118/download), ECCC TR19-118 (CJW), used only for its exact quantifier order.

## Model boundary

CHMY's deterministic one-tape model has a separate one-way read-only input tape and a two-way read/write work tape. Its randomized variant additionally has an independent one-way random tape; its oracle variant has the usual separate oracle tape. This is not:

- the MMW random-access streaming RAM;
- the repository's `Pnp3.Internal.PsubsetPpoly.TM`, whose input initially occupies its single read/write tape; or
- an arbitrary Lean function from the whole input list to a result.

CHMY does not fully freeze low-level end-marker, stay-move, or transition-tuple conventions. A Lean implementation must choose a standard finite transition convention, state it, and prove that the measured step count is the one used by subsequent theorems.

## Local HSG probability statement

The relevant fooling statement uses finite uniform averages and an independent random tape in both experiments:

```text
| E_{x <- U_N, r <- U_t} M(x,r)
  - E_{z <- U_seed, r <- U_t} M(G(z),r) | <= epsilon.
```

CHMY Lemma 15 instantiates `epsilon = 1/6`: generator outputs are YES instances accepted with probability at least `2/3`, while a uniform table is accepted with probability at most `o(1) + 1/3 < 1/2`. A formalization must use exact finite sums/rationals and explicit cardinalities, not an informal probability oracle.

Here "local" has the paper's circuit-complexity meaning: for each fixed seed `z`, the truth-table string `G(z)` describes a Boolean function whose ordinary DAG circuit complexity is at most the locality/seed bound. It is not the cryptographic condition that every output coordinate depends on only a few seed coordinates, and it does not by itself provide one uniform circuit taking both `z` and an output index.

## Published-parameter verdict

The published local generator has seed/locality bound of the form

```text
soft-O((sqrt(t) + log(1/epsilon)) * log(q * 2^ell * t)),
```

where `t` is machine time, `q` the number of oracle queries, and `ell` their bit length. For constant error, constant `q`, and no oracle query bits this specializes to

```text
soft-O(sqrt(t) * log t).
```

At `t(N) = N^(101/100)`, the certified parameter is therefore approximately

```text
N^(101/200) * polylog(N) = N^0.505 * polylog(N).
```

This published upper bound can certify an `N^mu` threshold only when `mu > 0.505` (choose an intermediate exponent between `0.505` and `mu`). It does not reach the sufficiently small `mu` required by the magnification endpoint, and it certainly does not reach a threshold polynomial in `n = log_2 N`.

The honest theorem name is therefore along the lines of:

```text
published_viola_chmy_parameters_do_not_certify_small_threshold
```

It would be incorrect to state `no_small_seed_prg_exists`: the calculation is an obstruction for the published construction/bound, not a universal lower bound on every PRG or HSG.

## CHMY exponent interval and printed typo

Theorem 16 uses parameters `1/2 < mu' < mu < 1`, subpolynomial query length, and time approximately `N^(2(mu' - o(1)))`. The later hardness-magnification proof under `P = NP` supplies a polynomial `p`; if `p(x) = O(x^d)`, an admissible symbolic interval is obtained by requiring `d * mu <= 1/100`. A formal treatment should keep `mu0` symbolic (or rationally encode exponents) until the degree `d` has been extracted from the actual simulation.

The full-version appendix contains a sign typo after deriving the consequence under `P = NP`: it prints a non-membership where the contrapositive requires membership in the one-tape time class. The surrounding proof and the phrase "taking the contrapositive" force the membership reading. The Lean statement must encode the logically consistent direction, and this textual correction must remain documented.

## CJW quantifier audit

CJW's sparse-language consequence has the shape

```text
forall k, exists L_k in NP, L_k notin SIZE(n^k).
```

It does **not** give

```text
exists L in NP, forall k, L notin SIZE(n^k).
```

The witness language may depend on `k`; hence the result alone does not establish `NP not_subset P/poly` and is not a direct `P != NP` endpoint.

## Exact open frontier

No one-tape lower bound at the required small threshold has been proved here. The one research question retained by this branch is:

> Construct a local HSG for the exact CHMY one-tape class whose seed/locality exponent is at most the admissible `mu0`, improving the published square-root-in-time dependence enough to instantiate Lemma 15 at the small threshold.

This statement belongs in this status file until proved. It must not be encoded as an axiom, typeclass, `Contract`, `Source`, `Provider`, structure field, or implicit instance.

## Later-literature check (through 2026-07-09)

- The [journal version of CHMY](https://link.springer.com/article/10.1007/s00224-022-10113-9) retains the large-threshold one-tape result and the same Appendix-A magnification direction; it does not supply a small-threshold lower bound.
- [ECCC TR25-017](https://eccc.weizmann.ac.il/report/2025/017/) develops a square-root-space simulation for multitape time, not the local HSG/PRG needed here.
- [ECCC TR26-064, revision 3](https://eccc.weizmann.ac.il/report/2026/064/) improves read-once branching-program pseudorandomness parameters but does not remove the square-root-in-time exponent in the Viola-to-CHMY route.

No primary source found in this check closes the magnification-admissible small-`mu` one-tape frontier. This negative literature finding is not itself a lower bound.
