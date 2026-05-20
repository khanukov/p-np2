# Barrier Catalogue

Updated: 2026-05-20.

One-stop reference for **Stage 1 (Literature Kill Audit)** and
**Stage 2 (Barrier / NoGo Audit)** of the idea-search pipeline
(`pnp3/Docs/IDEA_SEARCH_PIPELINE.md`).

This document lists published barriers and internal NoGo entries
that Role B (Literature Killer) and Role C (Repo Killer) must
check against.

## 1. Published external barriers

### B1. Relativization (Baker-Gill-Solovay 1975)

- **Paper**: Baker, T., Gill, J., Solovay, R. "Relativizations of
  the P =? NP question."  SIAM J. Comput. 4(4):431–442, 1975.
- **Statement**: Any proof technique that works uniformly under
  arbitrary oracles cannot resolve P vs NP, because there exist
  oracles A with P^A = NP^A and oracles B with P^B ≠ NP^B.
- **When applicable to pnp3 / pnp4**:
  - Routes that prove `NP ⊄ P/poly` using only oracle-agnostic
    properties of circuits.
  - Reductions that go through general circuit simulation without
    using specific circuit gate structure.
- **Stage 1 question 1 trigger**: yes.

### B2. Natural Proofs (Razborov-Rudich 1997)

- **Paper**: Razborov, A. A., Rudich, S. "Natural Proofs."  JCSS
  55(1):24–35, 1997.
- **Statement**: Conditional on existence of polynomial-time
  pseudorandom generators secure against `P/poly`, no proof of
  super-polynomial circuit lower bounds against `P/poly` can
  exhibit a property of Boolean functions that is (a) constructive
  in polynomial time on truth tables of length `2^n`, and (b)
  large — covering at least `2^{-O(n)}` fraction of all functions.
- **When applicable to pnp3 / pnp4**:
  - Support-cardinality bounds (`FormulaSupportRestrictionBoundsPartial`
    family — already internally refuted).
  - Shrinkage-under-restriction properties.
  - Constructive structural properties of `DagCircuit.support`,
    formula depth distributions, etc.
- **Stage 1 question 2 trigger**: yes.

### B3. Algebrization (Aaronson-Wigderson 2009)

- **Paper**: Aaronson, S., Wigderson, A.  "Algebrization: A new
  barrier in complexity theory."  ACM TOCT 1(1):2, 2009.
- **Statement**: Extension of relativization to algebraic oracles
  (low-degree extensions over finite fields).  Proofs that
  algebrize cannot resolve P vs NP.
- **When applicable**: routes that use algebraic / polynomial-
  method techniques without exploiting fine-grained low-degree
  structure of the specific problem.
- **Stage 1 question 3 trigger**: yes.

### B4. Locality Barrier (Chen et al. JACM 2022)

- **Paper**: Chen, L., Hirahara, S., Oliveira, I. C., Pich, J.,
  Rajgopal, N., Santhanam, R.  "Beyond Natural Proofs: Hardness
  Magnification and Locality."  JACM 69(4):25, 2022.
- **Statement**: Magnification target problems (e.g., MCSP variants
  including Search-MCSP and Gap-MCSP) admit highly-efficient
  circuits extended with small-fanin oracle gates.  Most weak
  lower-bound techniques survive such oracle extensions and
  therefore cannot deliver the required weak lower bound needed for
  magnification to succeed.
- **When applicable to pnp3 / pnp4**:
  - **`SearchMCSPWeakCircuitLowerBound`** (pnp4 frontier) — direct
    territory of the barrier.
  - Any weak lower-bound argument feeding magnification to
    `NP_not_subset_PpolyDAG` that does not explicitly evade
    oracle-gate extension.
- **Stage 1 question 4 trigger**: yes.

### B5. Magnification Threshold Gap (OPS19)

- **Paper**: Oliveira, I. C., Pich, J., Santhanam, R.  "Hardness
  Magnification near State-of-the-Art Lower Bounds."  CCC 2019.
- **Statement**: For natural magnification targets, the required
  weak lower bound is quantitatively above the regime achievable
  by current techniques.  The achievable regime is asymptotically
  below the threshold.
- **When applicable**: routes whose strength is bounded by current
  weak-LB techniques.
- **Stage 1 question 7 trigger**: yes.

### B6. Cryptographic Obstacles to NP-Hardness of MCSP

- **Papers**:
  - Allender, E., Cheraghchi, M., Myrisiotis, D., Tirumala, H.,
    Volkovich, I.  "One-way Functions and Partial MCSP."
    ECCC TR21-009, 2021.
  - Hirahara, S.  "NP-Hardness of Learning Programs and Partial
    MCSP."  FOCS 2022.
- **Statement**: Unconditional NP-hardness of MCSP / Partial-MCSP
  via deterministic reductions would have strong cryptographic
  consequences (existence of one-way functions).  Hirahara
  established NP-hardness of Partial-MCSP, but under randomized
  reductions.
- **When applicable**: routes that depend on unconditional NP-
  hardness of (Partial-)MCSP.
- **Stage 1 question 6 trigger**: partial.

## 2. Internal NoGo entries

The project maintains a NoGoLog of refuted proof templates.
Repo Killer (Role C) must compare each new idea against this
catalogue.

### Active NoGo entries (kernel-checked refutations)

| Tag | What it refutes | Source |
|---|---|---|
| **NOGO-000004** | prefixAnd hardwiring as a generic witness | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/ExcludesPrefixAnd.lean` |
| **NOGO-000006** | arbitrary `ttFormula` payload | `.../V2_A_gpt55/ExcludesArbitraryPayload.lean` |
| **NOGO-000008** | syntax-rewrite normalisation filters | (related NoGoLog entry) |
| **NOGO-000009** | normalisation as a meta-barrier | (related NoGoLog entry) |
| **Probe 13** | `FormulaCertificateProviderPartial → False` | `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` |
| **isoStrong L1 chain** | `isoStrong_conclusion_negative_for_canonical` and `isoStrong_conclusion_negative_general` | `pnp3/Tests/IsoStrongConclusionProbe.lean`, `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean` |
| **Iso-strong route closures** | three named route Props at canonical asymptotic spec | `pnp3/Tests/GeneralIsoStrongRouteClosure.lean` |
| **Support-bounds family** | `FormulaSupportRestrictionBoundsPartial → False`, `FormulaSupportBoundsFromMultiSwitchingContract → False`, `FormulaSupportBoundsPartial_fromPipeline → False` | `pnp3/Magnification/FinalResultAuditRoutes.lean` |

### Pattern matchers for Stage 2

Role C must flag the idea **likely BARRIER_RED** if it matches:

| Pattern | Matches NoGo |
|---|---|
| Support-cardinality based proof | Support-bounds family |
| Syntax filter on formula shapes | NOGO-000004/6/8, ProvenanceFilterV2 exclusion suite |
| Normalisation filter | NOGO-000008/9 |
| Universal `hWitness` over arbitrary `PpolyFormula` or DAG witness | Probe 13 |
| Formula certificate provider | Probe 13 |
| Promise-YES / iso-strong forcing | isoStrong L1 chain |
| Pigeonhole over candidate trace counting on canonical Gap-MCSP | isoStrong L1 chain |
| Restriction-shrinkage on bounded-depth formulae for MCSP-style targets | Natural proofs barrier (external) |

## 3. Pending operator-approval NoGo proposals

From `seed_packs/external_barriers_audit_D0/reports/external_barriers_audit_opus47.md`:

- **NOGO-EXT-NATURAL-PROOFS** — six `FixedSlice*Route` variants
  (support / shrinkage / restriction).
- **NOGO-EXT-LOCALITY-BARRIER-SEARCH-MCSP** — any concrete
  `SearchMCSPWeakCircuitLowerBound` instantiation.
- **NOGO-EXT-MAGNIFICATION-THRESHOLD-GAP** — OPS19 threshold gap.
- **NOGO-EXT-CRYPTO-ONE-WAY** — documentation note (not directly
  applicable to current routes).

**Status**: proposed, pending operator approval.  Until approved,
Role C should treat these as **soft NoGo** — flag them in Stage 2
reports but do not auto-reject ideas matching these patterns
without operator review.

## 4. Method-agnostic surfaces (NOT barriers)

These surfaces survive any barrier by construction — they are
abstract source-theorem ports rather than specific techniques:

- `pnp3/Magnification/UnconditionalResearchGap.lean` —
  `ResearchGapWitness` (method-agnostic).
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` —
  `VerifiedNPDAGLowerBoundSource` (method-agnostic).
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` —
  `SearchMCSPMagnificationContract` (interface, not proof; the
  concrete weak LB instantiation is subject to barrier B4).

A new idea proposing to **plug into** one of these surfaces with a
concrete proof technique must be evaluated against the barriers
above for the specific technique.  Plugging into the abstract
surface itself is not a barrier hit.

## 5. Citations

- Baker, T., Gill, J., Solovay, R.  *Relativizations of the
  P =? NP question*.  SIAM J. Comput. 4(4):431–442, 1975.
- Razborov, A. A., Rudich, S.  *Natural Proofs*.  JCSS
  55(1):24–35, 1997.
  https://mit6875.github.io/PAPERS/natural_proofs.pdf
- Aaronson, S., Wigderson, A.  *Algebrization: A new barrier in
  complexity theory*.  ACM TOCT 1(1):2, 2009.
- Oliveira, I. C., Santhanam, R.  *Hardness Magnification for
  Natural Problems*.  FOCS 2018.
- Oliveira, I. C., Pich, J., Santhanam, R.  *Hardness
  Magnification near State-of-the-Art Lower Bounds*.  CCC 2019.
- Chen, L., Hirahara, S., Oliveira, I. C., Pich, J., Rajgopal,
  N., Santhanam, R.  *Beyond Natural Proofs: Hardness
  Magnification and Locality*.  JACM 69(4):25, 2022.
- Allender, E., Cheraghchi, M., Myrisiotis, D., Tirumala, H.,
  Volkovich, I.  *One-way Functions and Partial MCSP*.
  ECCC TR21-009, 2021.
- Hirahara, S.  *NP-Hardness of Learning Programs and Partial
  MCSP*.  FOCS 2022.
- Cheraghchi, M., Kabanets, V., Lu, Z., Myrisiotis, D.  *Circuit
  Lower Bounds for MCSP from Local Pseudorandom Generators*.
  ICALP 2019.
