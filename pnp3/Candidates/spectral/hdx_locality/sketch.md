# Sketch — hdx_locality

**Status: REFUTED (auditor verdict, May 2026):
`RED_CURRENT_STATEMENT_ORACLE_TARGET_COLLISION`.**

The source theorem as stated is unconditionally `False` under the B4
fact (Gap-MCSP admits oracle-extended small circuits). The arrow was
reversed: it asks for usefulness against the oracle-extended class,
which the target itself belongs to. Formal refutation:
`hdx_locality_current_shape_impossible` in `proof.lean`. See
`self_attack.md` Attack 8 (attack-succeeded) and `barrier_certificate.md`
locality section.

This refutation IS the candidate's deliverable: a cheap, principled
no-go that caught a structural defect before any engineer time was
spent. It documents a new failure class (`oracle_target_collision`)
distinct from the existing `hardwiring` family.

The remainder of this sketch below is **historical** — preserved so
that the proposed repair (and why it is as hard as the main gap) is
legible to future readers.

---

## Proposed corrected shape (NOT scaffolded — open research)

Replace usefulness against the oracle-extended class by usefulness
against **plain** `PpolyDAG` plus an explicit `NonOracleRobust(P)`
witness that the technique does not lift to oracle-augmented circuits:

```
∃ P,
  HDXGlobal P ∧
  (∀ n f, InPpolyDAG n f → ¬ P n f) ∧
  (∀ n f, IsGapMCSP n f → P n f) ∧
  NotHardwired P ∧
  NonOracleRobust P
```

This is the *honest* B4 escape. However, the first two conjuncts already
amount to `GapMCSP ∉ PpolyDAG` — i.e. essentially the main gap — so the
corrected shape is a research goal, not an engineering scaffold. The
HDX literature (Dinur–Filmus–Harsha–Tulsiani, Hopkins–Lin) supplies
SoS / local-proof-system lower bounds, not lower bounds against
arbitrary `P/poly`; a direct HDX-cohomology-style obstruction is not
universally available because nonuniform circuits can hardwire the
fixed complex's linear algebra. See the auditor notes for the three
considered shapes (cohomology / spectral / algorithm-to-proof
extraction) and why each currently stalls.

## More promising successor (also not scaffolded)

The auditor's "Shape C" — an algorithm-to-proof extraction theorem:

```
GapMCSP ∈ PpolyDAG  ⇒  low-degree / local proof of an MCSP lower-bound
                       formula that HDX/SoS already refutes
```

would be a real bridge from arbitrary-circuit hypotheses to
proof-complexity lower bounds the HDX line CAN produce
(Austrin–Risse SoS-LB-for-MCSP, etc.). This is genuinely new research,
not in current literature, and deserves its own candidate audit cycle
under a different `method_family` (`proof_complexity`), not as a
spectral repair of this candidate.

---

## Original framing (historical)

The locality barrier (Chen et al., JACM 2022) says weak lower-bound
techniques survive augmenting circuits with small-fan-in **oracle
gates**, so they cannot drive magnification to `NP ⊄ P/poly`. High-
dimensional expanders (HDX) are precisely a *local-to-global* machine:
coboundary / agreement structure turns local constraints into global
guarantees (this is how HDX cracked c³ codes and quasi-linear PCPs).
The original bet was that an HDX-derived **global** hardness measure on
Boolean functions could remain useful against **oracle-extended**
poly-DAG circuits. The auditor showed this bet was structurally
self-contradictory: by B4 the target itself lies in the oracle-extended
class, so usefulness against that class excludes the target.

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
