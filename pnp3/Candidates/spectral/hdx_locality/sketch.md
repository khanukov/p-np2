# Sketch — hdx_locality

**Status: DRAFT SKELETON (secondary candidate).** Targets the locality
barrier B4 — the repo's architectural blocker. Pending the same
auditor crux review that `natural_property/psc_gapmcsp` received.

## One-paragraph summary

The locality barrier (Chen et al., JACM 2022) says weak lower-bound
techniques survive augmenting circuits with small-fan-in **oracle
gates**, so they cannot drive magnification to `NP ⊄ P/poly`. High-
dimensional expanders (HDX) are precisely a *local-to-global* machine:
coboundary / agreement structure turns local constraints into global
guarantees (this is how HDX cracked c³ codes and quasi-linear PCPs).
The bet: an HDX-derived **global** hardness measure on Boolean
functions can remain useful against **oracle-extended** poly-DAG
circuits — exactly the non-local behavior B4 says local techniques
lack. If so, it yields the `PpolyDAG` separation a fortiori.

## Source theorem

`SourceTheorem_hdx_locality`: there is a property `P` with an HDX
global-hardness witness, useful against the **oracle-extended** poly-DAG
class, true on `GapMCSP`, and not hardwiring-satisfiable. The Lean shape
(`proof.lean`) states usefulness against `InPpolyDAGOracle` on purpose —
that is the B4 escape, not plain `PpolyDAG`.

## Bridge

`gap_from_hdx_locality`: usefulness against the oracle-extended class
implies usefulness against plain `PpolyDAG` (a fortiori), and with
"holds on GapMCSP" gives `NP_not_subset_PpolyDAG`. **Engineer
obligation**: retype `→ True` to `→ ResearchGapWitness` and prove it.

## The crux (auditor)

Is `GlobalHardness P` together with usefulness against
`InPpolyDAGOracle` actually *achievable*, or does the HDX measure — once
made concrete — collapse to a **local** measure that the locality
barrier then defeats (so `P` becomes useless against the oracle-extended
class)? This is the B4 analogue of the psc_gapmcsp largeness crux and is
harder to bound cheaply, which is why this candidate is ranked second.

## What the candidate is NOT

Per Rule 1, no closed `P_ne_NP_unconditional`. Likely outcome: a
characterization of *why* a given HDX measure is local (a valuable
NoGoLog/locality note); small chance of a genuinely non-local measure.

## What the candidate explicitly avoids

Refuted predicates (Rule 6); typeclass payloads (Rule 16); arbitrary
witness quantification without the Rule 5 exclusion lemma (Rule 5);
collapse-not-contradiction (Rule 8).

## Connection to prior work

HDX → PCP / codes / SoS lower bounds is established; HDX → *worst-case
P/poly lower bound as an explicit counter to the locality barrier* is
not. The structural novelty attempted: use the local-to-global
mechanism specifically to certify usefulness against oracle-extended
circuits. References in `manifest.toml::[prior_work]`.
