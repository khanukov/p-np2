# Barrier certificate — psc_gapmcsp

**Status: DRAFT for auditor review.** Per Rule 7, this records which
classical barriers the approach contends with and where the obstacle is
overcome. Cells marked `unknown` are the auditor/engineer's checkpoints.

## Relativization

Status: `unknown`

Target step: the usefulness conjunct (2) must use the **specific**
formalized structure of `gapPartialMCSP`, not generic circuit
properties. If the argument only uses oracle-agnostic circuit facts it
relativizes (B1). Auditor check: does the intended inhabitant exploit
`GapMCSP`-specific structure?

## Natural proofs (Razborov–Rudich)

Status: `natural-but-with-caveat` (claim: escapes via `largeness`)

Condition broken: **largeness**. The property is designed to hold on a
`2^{-ω(n)}` fraction of functions (Chow's almost-natural route), so the
RR proof does not apply. Constructivity is retained where possible.

**Auditor must adjudicate (make-or-break):** is the sub-largeness
(`IsSubLarge P`) a *proved* lemma or an assumption? RR says useful +
constructive ⇒ large (under PRGs); therefore either (a) sub-largeness is
genuinely established for this `P`, or (b) `P` collapses to large
(hits RR) or to hardwiring (hits the NoGo). Decide which.

## Algebrization (Aaronson–Wigderson)

Status: `unknown`

Target step: same as relativization — if the usefulness argument runs
through low-degree/algebraic facts that survive a multilinear-extension
oracle, it algebrizes (B3). Note the SoS-for-MCSP prior-art barrier:
the inhabitant must NOT be a low-degree SoS/PC certificate.

## Hardwiring (Probe 2 of the falsifiability audit)

Status: `not-checked` — **highest-priority gate**

Question: does a singleton truth-table evaluator satisfy
`SourceTheorem_psc_gapmcsp` while the bridge cannot use it? All nine
prior `NoGoLog` entries died here. The Rule 5 exclusion lemma is the
`NotHardwired P` conjunct in `proof.lean`. Engineer must instantiate it
and discharge it against the attack in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` BEFORE intake.

If `checked-and-excluded`, point here to the formal lemma:
`NotHardwired` instantiation at `proof.lean:<line>` (TODO).

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
