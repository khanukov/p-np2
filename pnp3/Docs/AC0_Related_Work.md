# AC0 Related Work for the Partial-MCSP Milestone

Updated: 2026-04-23

This note records the literature position of the in-repo theorem surface

```text
gapPartialMCSP_not_in_AC0
```

from `pnp3/LowerBounds/AC0_GapMCSP.lean`.

## Bottom Line

As a pure complexity-theory statement, the in-repo AC0 endpoint should **not**
be presented as a new lower bound for MCSP-like problems.

The literature already contains stronger unconditional lower bounds for the
standard truth-table version of `MCSP`, including:

- strong depth-`d` `AC^0` lower bounds;
- strong `AC^0[p]` lower bounds;
- hardness results for constant-depth formula variants and partial-function
  versions of MCSP.

The credible novelty of the current repository milestone is instead:

- a machine-checked Lean formalization artifact;
- a clean restricted-model theorem surface over the active
  `SmallAC0Solver_Partial` interface;
- explicit separation between the restricted-model AC0 milestone and the still
  open unconditional `P != NP` research gap.

## Prior Work Most Relevant to AC0

### 1. Strong `AC^0` lower bounds for standard MCSP

Mahdi Cheraghchi, Valentine Kabanets, Zhenjian Lu, and Dimitrios Myrisiotis,
*Circuit Lower Bounds for MCSP from Local Pseudorandom Generators*,
ICALP 2019.

This work proves substantially stronger bounds than simple non-membership in
`AC^0`.  In particular, for truth-table length `N`, it gives depth-`d` `AC^0`
lower bounds of the form

```text
2^{Omega(N^{1/(d+2.01)})}.
```

Useful sources:

- DOI / proceedings: <https://doi.org/10.4230/LIPIcs.ICALP.2019.39>
- summary page: <https://www2.cs.sfu.ca/~kabanets/Research/MCSP-LB-Formulas.html>

### 2. Strong `AC^0[p]` lower bounds for standard MCSP

Alexander Golovnev, Rahul Ilango, Russell Impagliazzo, Valentine Kabanets,
Antonina Kolokolova, and Avishay Tal,
*AC^0[p] Lower Bounds Against MCSP via the Coin Problem*,
ICALP 2019.

This gives depth-`d` `AC^0[p]` lower bounds of the form

```text
exp(N^{0.49/d}).
```

Source:

- DOI / proceedings: <https://doi.org/10.4230/LIPIcs.ICALP.2019.66>

### 3. Partial-function and constant-depth-formula hardness

Rahul Ilango,
*Constant Depth Formula and Partial Function Versions of MCSP are Hard*,
FOCS 2020 / ECCC TR20-183.

This is not the same statement as `gapPartialMCSP_not_in_AC0`, but it is
directly relevant because it studies constant-depth formula variants and
partial-function versions of MCSP.  It is the closest literature touchpoint
for the "partial" side of the active repository model.

Sources:

- ECCC: <https://eccc.weizmann.ac.il/report/2020/183/>
- FOCS DOI: <https://doi.org/10.1109/FOCS46700.2020.00047>

### 4. Older nearby work on truth-table minimization

Eric Allender, Lisa Hellerstein, Paul McCabe, Toniann Pitassi, and
Michael E. Saks,
*Minimizing DNF Formulas and AC^0 Circuits Given a Truth Table*,
SIAM Journal on Computing, 2008.

This is not an `MCSP notin AC^0` theorem, but it is historically relevant
background on truth-table minimization for restricted circuit classes.

Source:

- DOI: <https://doi.org/10.1137/060664537>

## What We Should Claim

The safe claim is:

> The repository contains a machine-checked fixed-slice AC0 lower-bound
> endpoint for the active Partial-MCSP solver interface.

The unsafe claim is:

> We proved a new AC0 lower bound for MCSP.

That second claim is not supported by the literature position above.

## Possible Novelty

A targeted search on 2026-04-23 did **not** reveal a prior Lean/Coq/Isabelle
publication specifically formalizing an MCSP or Partial-MCSP `AC^0` lower
bound as a proof-assistant artifact.

The targeted search included keyword combinations around:

- `MCSP` plus `Lean`, `Coq`, `Isabelle`, and `proof assistant`;
- `Minimum Circuit Size Problem` plus `formalization`;
- ITP/CPP-oriented searches for `MCSP` with theorem provers.

That is only a search result, not a proof of absence.  The responsible wording
is:

> We are not aware of a prior proof-assistant formalization of this specific
> restricted-model MCSP lower-bound endpoint.

## Recommended Publication Positioning

The current AC0 milestone looks publishable as one of:

1. a theorem-proving / formalization artifact;
2. a case study in formalized complexity-theory lower bounds;
3. a verified restricted-model endpoint extracted from a larger
   hardness-magnification codebase.

It should not be positioned as a new breakthrough complexity lower bound for
MCSP itself.
