# Barrier certificate — psc_gapmcsp

**Status: under_review (auditor verdict May 2026).** Per Rule 7. The
shape is correct (no oracle-target collision against plain `PpolyDAG`),
but two kernel-checked kill-gates in `proof.lean` weaken the natural-
proof escape claim — sub-largeness is decorative without a strong
`NotHardwired` (Gate A), and several natural target instantiations are
already in `PpolyDAG` by repo theorems (Gate B). See `self_attack.md`
Attacks 9 and 10.

## Relativization

Status: `unknown`

Target step: the usefulness conjunct (2) must use the **specific**
formalized structure of `gapPartialMCSP`, not generic circuit
properties. If the argument only uses oracle-agnostic circuit facts it
relativizes (B1). Auditor check: does the intended inhabitant exploit
`GapMCSP`-specific structure?

## Natural proofs (Razborov–Rudich)

Status: `natural-but-with-caveat-and-decorative` (claimed escape via
`largeness`, weakened by Gate A)

Condition nominally broken: **largeness**. The property is designed to
hold on a `2^{-ω(n)}` fraction of functions (Chow's almost-natural
route), so the RR proof does not apply. However, **Gate A**
(`psc_two_conjuncts_iff_bare_separation`) shows that the
sub-largeness conjunct is *decorative* on top of the usefulness +
accepts pair, which is already equivalent to the bare separation. So
the natural-proof escape is real only insofar as the witness `P` is
*not* the trivial `P := IsGapMCSP` (which trivially passes the two
main conjuncts and is sub-large under any natural measure). The real
escape mechanism therefore lives entirely in `NotHardwired`, not in
`IsSubLarge`.

**Auditor adjudication:** the natural-proof escape claim is downgraded
from "primary mechanism" to "compatibility condition". Engineers must
treat `NotHardwired` as the load-bearing predicate and supply a
*non-vacuous* concrete definition that excludes the trivial witness.

## Algebrization (Aaronson–Wigderson)

Status: `unknown`

Target step: same as relativization — if the usefulness argument runs
through low-degree/algebraic facts that survive a multilinear-extension
oracle, it algebrizes (B3). Note the SoS-for-MCSP prior-art barrier:
the inhabitant must NOT be a low-degree SoS/PC certificate.

## Hardwiring (Probe 2 of the falsifiability audit)

Status: `attack-succeeded-against-the-skeleton` — **highest-priority gate, escalated by Gate A**

Gate A shows that without a strong, concrete `NotHardwired`, the
trivial witness `P := IsGapMCSP` already passes the two main conjuncts
(under the bare separation), so the candidate is structurally a
re-statement of the conclusion. Therefore hardwiring is not only a
self-attack risk to check — it is the **only thing standing between
the candidate and a trivial collapse**. The Rule 5 exclusion lemma
must be supplied as a *concrete definition* (not an abstract
parameter) before any positive engineering work, and it must
demonstrably exclude:

* singleton truth-table evaluators of `L_N`,
* hash/log-width truth-table payloads,
* target-truth-table advice (extensional dependence on `tt(L_N)`).

Attack template: `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.

## Forbidden target instantiations (Gate B)

Status: `attack-succeeded-against-the-skeleton`

Formal witness: `psc_forbidden_target_collapse` in `proof.lean`.
`IsGapMCSP` must NOT be instantiated to any target the repo already
proves to lie in `InPpolyDAG`. Specifically forbidden:

* `Tests.HInDagTrivialityProbe.fixedSlice_gapPartialMCSP_in_PpolyDAG`;
* `Tests.HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`.

A valid C1 candidate requires a *new* asymptotic NP language outside
the repo's known DAG-hardwiring envelope. Designing such a language is
itself an open research precondition for any positive C1 work.

## Collapse-vs-contradiction (Rule 8)

Status: `genuine-contradiction`

The bridge deduces `GapMCSP ∉ PpolyDAG` directly (a real separation),
not "if NP ⊆ P/poly then PH collapses". No collapse appeal is used.

## Prior-art barrier (must clear before engineer time)

`Sum-of-Squares Lower Bounds for MCSP` (CCC 2023): there is **no
low-degree SoS proof** of `NP ⊄ P/poly`. Therefore a candidate whose
usefulness conjunct (2) is established by a low-degree SoS/PC certificate
is *already refuted* — auditor rejects without dispatching engineers.
Pseudo-calibration is admissible only as a sub-largeness *witness*.

## Inversion check (cheap, run first)

Pseudo-calibration natively yields *certification hardness /
indistinguishability* (no low-degree distinguisher), which is the
barrier direction, not a function lower bound. The auditor must confirm
the inhabitant proves **function hardness** (`∀ poly C, ∃ x, C(x) ≠ f(x)`)
and not merely "no low-degree distinguisher for a planted distribution".
If the latter, KILL immediately → `NoGoLog`.

## Formal witnesses (to be filled by engineer)

- Hardwiring exclusion lemma (`NotHardwired`): `proof.lean:<line>` (TODO)
- GapMCSP-specific (non-relativizing) step: `proof.lean:<line>` (TODO)
- Sub-largeness lemma (`IsSubLarge`): `proof.lean:<line>` (TODO)
