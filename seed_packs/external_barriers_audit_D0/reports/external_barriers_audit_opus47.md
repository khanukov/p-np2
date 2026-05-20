# External barriers audit — D0 report

Task: external barriers audit (D0)
Handle: opus47
Branch: main (HEAD `f6a6e8e`)
Scope: markdown-only; no Lean / JSONL / NoGoLog / trust-root edits.

## 1. Executive verdict

**MIXED — some live routes are already published-blocked, others survive
strict scrutiny.**

Detailed breakdown:

| Live route family | Verdict | Recommended action |
|---|---|---|
| `Asymptotic*Route` × 3 | already closed (`GeneralIsoStrongRouteClosure.lean`) | confirm closure in NoGoLog |
| `FixedSliceSupportHalfValueSupportedRoute` | **likely natural-proofs-blocked** | open NoGo proposal |
| `FixedSliceDAGStableRestrictionSlackRoute` | **likely natural-proofs-blocked** | open NoGo proposal |
| `FixedSliceShrinkageCertificateRoute` | **likely natural-proofs-blocked** | open NoGo proposal |
| `FixedSliceRestrictionDataRoute` | **likely natural-proofs-blocked** | open NoGo proposal |
| `FixedSliceSupportNumericRoute` / `Component` | **likely natural-proofs-blocked** | open NoGo proposal |
| `FixedSlicePromiseValueLocalityRoute` | partially applicable barriers; survives | keep open |
| `FixedSliceTransferQuarterRoute` | applicability unclear | keep open, request follow-up |
| `FixedSliceWitnessEasyDensityRoute` | applicability unclear | keep open, request follow-up |
| `FixedSliceWitnessUniformLowerRoute` | applicability unclear | keep open, request follow-up |
| `FixedSlicePromiseYesCertificateRoute` (fixed-slice version) | partial — survives at fixed slice | keep open |
| `SearchMCSPCompressionProblem` / `SearchMCSPWeakCircuitLowerBound` (pnp4) | **likely locality-barrier-blocked** | open NoGo proposal |
| `SearchMCSPMagnificationContract` (pnp4) | structural interface; not directly blocked | keep open |
| `VerifiedNPDAGLowerBoundSource` (pnp4) | method-agnostic; survives by design | keep open |
| `ResearchGapWitness` (pnp3) | method-agnostic; survives by design | keep open |

**Net effect**: between five and seven live `FixedSlice*Route` Props
look published-blocked by Razborov-Rudich (1997) natural-proofs in the
sense that they ask for combinatorial properties that are constructive
in polynomial time and "large".  One pnp4 surface
(`SearchMCSPWeakCircuitLowerBound`) is squarely in the territory the
Chen et al. (JACM 2022) locality barrier targets.

This audit is **D0 (markdown only)**.  It does not apply NoGoLog
entries.  Per repo governance, NoGoLog edits require operator
approval; a follow-up D0-NoGo or L0-NoGo proposal pack is the
appropriate next stage.

## 2. Methodology

Identification of live routes:

1. `grep -n "^def.*Route\\|^structure ResearchGap" pnp3/Magnification/FinalResultMainline.lean`
   plus `pnp3/Magnification/UnconditionalResearchGap.lean`.
2. `grep -rn "^def.*Source\\|^structure.*WeakLowerBound\\|^structure.*Compression" pnp4/Pnp4/`.
3. Manual inspection of `pnp3/Docs/CLOSURE_ROUTE_POLICY.md` for
   already-closed routes.

Barriers considered:

- **Razborov-Rudich (1997)** "Natural Proofs", JCSS — combinatorial
  properties on `n`-input functions that are constructive
  (decidable in polynomial time in the truth-table length `2^n`)
  and large (cover at least `2^{-O(n)}` fraction of all functions)
  cannot prove super-polynomial circuit lower bounds, conditional
  on existence of polynomial-time pseudorandom generators secure
  against `P/poly`.
- **Baker-Gill-Solovay (1975)** "Relativizations" — any proof that
  works under all oracles cannot separate P and NP.
- **Aaronson-Wigderson (2009)** "Algebrization" — extension of
  relativization to algebraic oracle extensions; proofs that
  algebrize cannot separate P and NP.
- **OPS19 (Oliveira-Pich-Santhanam 2019)** "Hardness Magnification
  near State-of-the-Art Lower Bounds", CCC — magnification
  threshold gap; the achievable lower-bound regime is
  asymptotically below the threshold required for magnification
  to give super-polynomial separations.
- **Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam (JACM 2022)**
  "Beyond Natural Proofs: Hardness Magnification and Locality" —
  **locality barrier**.  Magnification target problems admit
  highly-efficient circuits extended with small-fanin oracle gates;
  weak lower-bound techniques that survive such oracle extensions
  cannot deliver the required weak lower bound.  This is the
  closest published barrier to what pnp3 / pnp4 are attempting.
- **Allender-Cheraghchi-Myrisiotis-Tirumala-Volkovich (2021)**
  "One-way Functions and Partial MCSP", ECCC TR21-009 —
  cryptographic obstructions on NP-hardness of Partial-MCSP.
- **Hirahara (FOCS 2022)** "NP-Hardness of Learning Programs and
  Partial MCSP" — positive NP-hardness result, but under
  randomized reductions; constrains what unconditional
  NP-hardness routes can look like.
- **Cheraghchi-Kabanets-Lu-Myrisiotis (ICALP 2019)** "Circuit
  Lower Bounds for MCSP from Local Pseudorandom Generators" —
  established `AC^0` lower bounds for standard MCSP; useful
  positive reference for the pnp3 AC0 milestone.

Per-route methodology:

1. Read the route's Lean signature.
2. Identify what property of the DAG / circuit witness is being
   asked for.
3. Check whether that property is:
   (a) combinatorial — falls under natural proofs;
   (b) preserved under oracle extension — falls under locality
       barrier;
   (c) relativizing — falls under Baker-Gill-Solovay.
4. Record the verdict with citation.

## 3. Catalog of live routes

### 3.1 Asymptotic routes (already closed)

The three `Asymptotic*Route` Props in
`pnp3/Magnification/FinalResultMainline.lean` are formally closed
at the canonical instantiation via
`pnp3/Tests/GeneralIsoStrongRouteClosure.lean` (merged in
`f6a6e8e`):

- `AsymptoticIsoStrongRoute` →
  `not_AsymptoticIsoStrongRoute_canonical`.
- `AsymptoticPromiseYesCertificateRoute` →
  `not_AsymptoticPromiseYesCertificateRoute_canonical`.
- `AsymptoticPromiseYesWeakRouteEventually` →
  `not_AsymptoticPromiseYesWeakRouteEventually_canonical`.

These do not need new NoGoLog entries beyond confirming the
closure status.

**Strategic note**: the underlying counting / diagonalisation
phenomenon is folklore-equivalent to the spirit of the locality
barrier — the iso-strong forcing condition asks for selective
structural behavior that bounded-size circuits cannot satisfy by
trace counting.  This is **the in-codebase rediscovery of the
locality phenomenon at canonical parameters**.

### 3.2 FixedSlice routes (`pnp3/Magnification/FinalResultMainline.lean:1155–1330`)

Eleven `FixedSlice*Route` Props.  All have the same shape:

```lean
def FixedSlice<X>Route (p : GapPartialMCSPParams) : Prop :=
  ∀ w : InPpolyDAG (gapPartialMCSP_Language p),
    <some structural condition on w / fixedSliceSmallDAGWitness_of_inPpolyDAG w>
```

Each route asks the source-theorem author to deliver a structural
witness on the DAG side at a fixed canonical-length slice.

Per-route analysis below.

#### 3.2.1 `FixedSliceSupportHalfValueSupportedRoute` (line 1224)

Asks: `(DagCircuit.support W.C).card ≤ Partial.tableLen p.n / 2` plus
"every support coordinate corresponds to a value position".

**Analysis**: support-cardinality + structural-support condition is a
prototypical **natural property** (constructive in poly time on
truth-table; large fraction of `P/poly` functions satisfy a
half-support bound — though "value-supported" narrows the fraction).
The full constructive+large characterisation needs careful checking,
but the support-half clause alone is on the natural-proofs target
list.

**Barrier**: Razborov-Rudich (1997) natural proofs barrier likely
applies.  Already partially internalised in pnp3 as
`FormulaSupportRestrictionBoundsPartial → False` and analogues.

**Recommended NoGo**: yes, with citation to Razborov-Rudich and
in-tree reference to the existing support-bounds falsifiability
audit.

#### 3.2.2 `FixedSliceDAGStableRestrictionSlackRoute` (line 1239)

Asks: nonempty `DAGStableRestrictionSlackPackageAt` (one
encoded-coordinate restriction with direct counting slack and local
dependence).

**Analysis**: this is exactly a **shrinkage-under-restriction**
style property — historically the prototypical case where natural
proofs apply.  Shrinkage of de-Morgan formulae under restriction
was one of the technical motivations for Razborov-Rudich.

**Barrier**: natural proofs.  Also relates to OPS19 magnification
threshold gap — restriction-based weak lower bounds are exactly the
regime where the threshold gap appears.

**Recommended NoGo**: yes.

#### 3.2.3 `FixedSliceShrinkageCertificateRoute` (line 1253)

Asks: nonempty shrinkage certificate at the slice.

**Analysis**: literally a shrinkage property → natural proofs.

**Barrier**: natural proofs.

**Recommended NoGo**: yes.

#### 3.2.4 `FixedSliceRestrictionDataRoute` (line 1267)

Asks: structural restriction-data witness.

**Analysis**: restriction-based → natural proofs.

**Barrier**: natural proofs.

**Recommended NoGo**: yes.

#### 3.2.5 `FixedSliceSupportNumericRoute` (line 1280) and `FixedSliceSupportNumericComponentRoute` (line 1295)

Numeric variants of the support-half condition.

**Analysis**: same as 3.2.1 — natural proofs apply to support-
cardinality properties.

**Barrier**: natural proofs.

**Recommended NoGo**: yes.

#### 3.2.6 `FixedSlicePromiseValueLocalityRoute` (line 1170)

Asks: nonempty `PromiseValueLocalityPackageAt` — semantic forcing +
same-set counting slack.

**Analysis**: this is **semantic** (forcing on the YES set is a
property of the language, not a syntactic property of the circuit),
combined with a counting condition.  Natural proofs target
syntactic/combinatorial properties of circuits, so the **forcing
component is likely outside natural-proofs scope**.  Counting slack
on its own can still be problematic, but the route as a whole has a
semantic ingredient.

**Barrier**: partial.  Natural proofs may apply to the counting
slack part but not to the semantic forcing.  The route resembles
the iso-strong template we already closed (asymptotic version);
at fixed slice the same counting argument may apply.

**Recommended NoGo**: no, not yet.  Worth a Lean probe analogous
to our iso-strong refutation at fixed slice — likely a folklore
counting argument suffices, but should be formalised before NoGo.

#### 3.2.7 `FixedSliceTransferQuarterRoute` (line 1212)

Asks: nonempty `EasyImageTransferAt` with `epsilon ≤ 1/4`.

**Analysis**: this is an **information-theoretic transfer**
condition (`EasyImageTransferAt` — checking whether the YES side
has small image under a transfer map, with `epsilon` being a
quantitative compactness parameter).  Not obviously combinatorial,
not obviously oracle-friendly.

**Barrier**: unclear at D0.  Worth a follow-up D0 with deeper
read.

**Recommended NoGo**: no, not yet.  Request follow-up audit.

#### 3.2.8 `FixedSliceWitnessEasyDensityRoute` (line 1185)

Asks: nonempty `CanonicalWitnessEasyDensitySourceAt` — density
condition on the YES side.

**Analysis**: density-first source surface.  Density properties of
random functions are concentrated, so a "small density" property
of YES might be natural-proofs-targetable; but the route asks for
a witness, not a property of arbitrary functions, so applicability
is subtle.

**Barrier**: unclear at D0.

**Recommended NoGo**: no.  Request follow-up.

#### 3.2.9 `FixedSliceWitnessUniformLowerRoute` (line 1196)

Asks: nonempty `WitnessUniformLowerSourceAt` — uniform lower bound
on witness families.

**Analysis**: structurally similar to 3.2.8.

**Barrier**: unclear at D0.

**Recommended NoGo**: no.  Request follow-up.

#### 3.2.10 `FixedSlicePromiseYesCertificateRoute` (line 1155)

Asks: nonempty `PromiseYesSubcubeCertificateAt` at fixed slice.

**Analysis**: this is the fixed-slice analogue of the
asymptotic version we closed.  The asymptotic closure was via
counting + iso-strong reduction; at fixed slice the language is
trivially in P/poly (truth-table hardwiring) so the witness is
constructible; the certificate's structure restricts to the
canonical YES set which is tiny at `sYES=1`.

**Barrier**: at canonical `sYES=1, sNO=2` parameters, a counting
argument analogous to the iso-strong refutation likely applies.
At general parameters, the locality barrier may apply.

**Recommended NoGo**: at canonical parameters yes; worth
formalising as a small follow-up Lean theorem (similar in spirit
to our route closures, but at fixed slice).  At general parameters
keep open pending audit.

### 3.3 pnp4 SearchMCSP frontier

The pnp4 frontier in `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
contains a clean structural setup mirroring the
**Oliveira-Santhanam (FOCS 2018) and OPS19 (CCC 2019)** hardness
magnification programme:

- `SearchMCSPCompressionProblem` — search/compression instance.
- `BoundedSearchSolver` — non-uniform bounded solver (weak class).
- `SearchProblemNoBoundedSolver` — the weak lower-bound target.
- `SearchMCSPWeakCircuitLowerBoundTarget` — concrete weak lower-
  bound parameters.
- `SearchMCSPWeakCircuitLowerBound` — the witness that the weak
  lower bound holds.
- `SearchMCSPMagnificationContract` — assumes the published
  magnification theorem as an interface (`weakLB → NP_not_subset_PpolyDAG`).

**Analysis**: this is **precisely** the territory addressed by the
locality barrier (Chen et al. JACM 2022).  The published locality
barrier shows that:

- Magnification target problems (like search-MCSP and compression
  versions) admit highly-efficient circuits extended with small-
  fanin oracle gates;
- Weak lower-bound techniques that survive such oracle extensions
  cannot deliver the required weak lower bound;
- Most known weak lower-bound techniques do survive such
  extensions, hence cannot be used.

The pnp4 frontier does **not** specify which weak lower-bound
technique it intends to use, so strictly the surface itself is not
yet blocked — it is a *structural interface* that the locality
barrier would block any concrete instantiation of.

**Barrier**: locality barrier (Chen et al. JACM 2022) applies to
any concrete weak lower-bound technique fed into
`SearchMCSPWeakCircuitLowerBound`.  The OPS19 threshold gap also
applies: the achievable lower bound is asymptotically below the
required magnification threshold.

**Recommended NoGo**: structural NoGo proposal — record that this
frontier is locality-barrier-restricted; any future
`SearchMCSPWeakCircuitLowerBound` proof must explicitly identify
the weak technique and demonstrate it is locality-barrier-safe.

`VerifiedNPDAGLowerBoundSource` (in
`pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`) is
**method-agnostic** by design — it is the abstract source theorem
shape, equivalent to pnp3's `ResearchGapWitness`.  Not blocked.

### 3.4 `ResearchGapWitness` (`pnp3/Magnification/UnconditionalResearchGap.lean`)

Method-agnostic abstract gap port.  By design, accepts algebraic /
spectral / Fourier-analytic / SOS routes.

**Barrier**: not applicable.  This is the "anything that works
plugs in here" frontier.

**Recommended NoGo**: no.  This is the legitimate research-level
target.

### 3.5 AC0 milestone (`pnp3/LowerBounds/AC0_GapMCSP.lean`)

Restricted-model lower bound: `gapPartialMCSP_not_in_AC0` against
`SmallAC0Solver_Partial`.

**Barrier**: not applicable — this is a *positive* restricted-model
result, in the AC0 territory where natural proofs do not block (the
AC0 lower bounds for parity, majority, etc., are not natural in
Razborov-Rudich sense because AC0 functions are sparse).

**Recommended NoGo**: no.  This is a legitimate milestone.

## 4. Recommended NoGoLog proposals (operator approval needed)

The following are proposed NoGoLog entries.  **None are applied in
this PR**; per repository governance, NoGoLog edits require
operator approval.  If approved, a follow-up PR can add them.

### NOGO-EXT-NATURAL-PROOFS

- **Refuted predicate / route**: any `FixedSlice*Route` Prop whose
  source-theorem obligation reduces to a constructive + large
  combinatorial property of `DagCircuit.support` or of
  restriction-shrinkage data.
- **Specifically**:
  `FixedSliceSupportHalfValueSupportedRoute`,
  `FixedSliceDAGStableRestrictionSlackRoute`,
  `FixedSliceShrinkageCertificateRoute`,
  `FixedSliceRestrictionDataRoute`,
  `FixedSliceSupportNumericRoute`,
  `FixedSliceSupportNumericComponentRoute`.
- **External barrier**: Razborov-Rudich (1997) "Natural Proofs",
  JCSS.
  Conditional on existence of polynomial-time pseudorandom
  generators secure against `P/poly` — a standard cryptographic
  assumption.
- **Internal corroboration**: the pnp3 falsifiability audit already
  has `FormulaSupportRestrictionBoundsPartial → False` and
  `FormulaSupportBoundsFromMultiSwitchingContract → False` —
  internal recoveries of the same phenomenon for related
  predicates.
- **Status to record**: do not pursue support-half / shrinkage /
  restriction-based source theorems against `P/poly` without
  first formalising an exclusion argument à la the existing
  falsifiability audit.

### NOGO-EXT-LOCALITY-BARRIER-SEARCH-MCSP

- **Refuted predicate / route**: any concrete instantiation of
  `SearchMCSPWeakCircuitLowerBound` that uses a weak lower-bound
  technique surviving small-fanin oracle gate extensions.
- **External barrier**: Chen-Hirahara-Oliveira-Pich-Rajgopal-
  Santhanam (JACM 2022) "Beyond Natural Proofs: Hardness
  Magnification and Locality".  This is an *unconditional* barrier
  for techniques in the specified class.
- **Status to record**: any future
  `SearchMCSPWeakCircuitLowerBound` proof must explicitly identify
  the weak lower-bound technique used and demonstrate either (a)
  it is locality-barrier-safe (does not survive oracle gate
  extension), or (b) the magnification chain is non-standard in a
  way that avoids the barrier.

### NOGO-EXT-MAGNIFICATION-THRESHOLD-GAP

- **Refuted predicate / route**: source theorems that depend on
  weak lower bounds in the regime quantitatively achievable by
  current techniques.
- **External barrier**: OPS19 (Oliveira-Pich-Santhanam, CCC 2019)
  "Hardness Magnification near State-of-the-Art Lower Bounds".
  The achievable lower-bound regime is asymptotically below the
  magnification threshold.
- **Status to record**: source-theorem authors should explicitly
  acknowledge the threshold gap and either (a) target a regime
  above the gap, or (b) propose new magnification arithmetic that
  closes the gap.

### NOGO-EXT-CRYPTO-ONE-WAY (for completeness; not directly applicable)

- **Refuted predicate / route**: any source theorem that requires
  NP-hardness of unconditional MCSP or Partial-MCSP through
  deterministic reductions.
- **External barrier**: Allender-Cheraghchi-Myrisiotis-Tirumala-
  Volkovich (ECCC TR21-009) and follow-ups — show that
  unconditional NP-hardness of MCSP would have strong cryptographic
  consequences (existence of one-way functions, etc.).
- **Status to record**: not directly applicable to current pnp3
  / pnp4 routes since they target `NP_not_subset_P/poly` rather
  than `NP-hardness of MCSP`, but worth a documentation note for
  future readers considering MCSP-based routes.

## 5. Routes that survive the audit

Routes that do **not** appear to be directly blocked by any
published barrier (at this D0 markdown-only level):

1. **`ResearchGapWitness`** (`pnp3/Magnification/UnconditionalResearchGap.lean`):
   method-agnostic abstract gap port — by design, survives any
   barrier on specific proof methods.

2. **`VerifiedNPDAGLowerBoundSource`** (pnp4): same comment.

3. **`SearchMCSPMagnificationContract`** (pnp4): structural
   interface assuming the published magnification theorem; not
   directly blocked, but any concrete weak LB feeding into it is
   subject to NOGO-EXT-LOCALITY-BARRIER-SEARCH-MCSP above.

4. **`FixedSlicePromiseValueLocalityRoute`**, `FixedSliceTransferQuarterRoute`, `FixedSliceWitnessEasyDensityRoute`, `FixedSliceWitnessUniformLowerRoute`, `FixedSlicePromiseYesCertificateRoute` (the last only at general parameters):
   no published barrier directly applies; survive D0 audit pending
   deeper analysis.

5. **AC0 milestone** (`gapPartialMCSP_not_in_AC0` in
   `pnp3/LowerBounds/AC0_GapMCSP.lean`): not a P≠NP claim, and AC0
   territory is outside natural-proofs scope; survives.

## 6. Strategic recommendation

Three concrete next steps, in priority order:

### Step 1 (recommended, immediate)

**Apply the four NoGoLog proposals above as a follow-up D0-NoGo
PR after operator approval.**  This locks the project away from
re-attempting routes that the published literature already
forecloses, and frees future engineer-effort for the routes that
genuinely remain open.

Estimated effort: one markdown-only PR with JSONL `NoGoLog`
updates.  Subject to repository policy: requires operator
approval.

### Step 2 (recommended, medium-term)

**Close the remaining FixedSlice routes that appear folklore-
refutable** via small Lean theorems analogous to our iso-strong
chain:

- `FixedSlicePromiseValueLocalityRoute` — likely a counting
  argument at canonical parameters.
- `FixedSlicePromiseYesCertificateRoute` (fixed-slice) — same.
- `FixedSliceTransferQuarterRoute`, `FixedSliceWitnessEasyDensityRoute`,
  `FixedSliceWitnessUniformLowerRoute` — request a D0 follow-up
  audit to determine whether folklore refutation is straightforward.

Estimated effort: 2–4 small L1 sessions per route, each in the
shape of our `not_AsymptoticIsoStrongRoute_canonical` packaging.

### Step 3 (recommended, longer-term)

**Pivot active proof-engineering effort away from the `P/poly`
mainline frontier toward routes that are not literature-blocked**:

- `ResearchGapWitness` and `VerifiedNPDAGLowerBoundSource` remain
  as method-agnostic targets, but any concrete attempt must
  identify the proof technique and verify it is not
  literature-blocked.
- The AC0 milestone is a legitimate target for additional
  restricted-model results.
- Genuinely new mathematics (algebraic, spectral, Fourier-
  analytic, SOS, finite-field, or non-combinatorial) is the
  honest research-level path.

## 7. Comparison with internal pnp3 audit chain

The pnp3 audit chain (15 stages, all kernel-checked, recorded in
STATUS.md) has independently formalised:

- support-bounds / multi-switching falsifiability (Probe 7, 13,
  related);
- canonical iso-strong refutation (L1 chain);
- general iso-strong route closure (this PR's predecessor).

Read against the published barriers, this chain is a **formal
recovery** of phenomena adjacent to natural proofs (for support-
bounds) and locality barrier (for iso-strong forcing).  None of
the chain has crossed into territory not already foreseen by the
published literature.

This is **not a criticism** of the formalisation work — the
engineering is non-trivial and the Lean infrastructure
(`GapPartialMCSP`, `CorrectOnPromiseSlice`, the L0 counting
bricks, etc.) is reusable for genuinely novel future attempts.
But it does suggest the project should:

1. Stop spending engineer-effort re-discovering published
   barriers internally.
2. Use this audit as a checkpoint to identify which proof
   templates are pre-blocked and avoid them.
3. Direct future effort toward `ResearchGapWitness` /
   `VerifiedNPDAGLowerBoundSource` with a clear specification of
   the *non-literature-blocked* technique being attempted.

## 8. Citations

Primary references used in this audit:

- Razborov, A. A. and Rudich, S. *Natural Proofs*.
  JCSS 55(1):24–35, 1997.
  https://mit6875.github.io/PAPERS/natural_proofs.pdf
- Baker, T., Gill, J., and Solovay, R.
  *Relativizations of the P =? NP question*.
  SIAM J. Comput. 4(4):431–442, 1975.
- Aaronson, S. and Wigderson, A. *Algebrization: A new barrier in
  complexity theory*.  ACM TOCT 1(1):2, 2009.
- Oliveira, I. C. and Santhanam, R. *Hardness Magnification for
  Natural Problems*.  FOCS 2018.
  https://ieee-focs.org/FOCS-2018-Papers/pdfs/59f065.pdf
- Oliveira, I. C., Pich, J., and Santhanam, R. *Hardness
  Magnification near State-of-the-Art Lower Bounds*.  CCC 2019.
  https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/OPS19.pdf
- Chen, L., Hirahara, S., Oliveira, I. C., Pich, J., Rajgopal, N.,
  and Santhanam, R. *Beyond Natural Proofs: Hardness Magnification
  and Locality*.  JACM 69(4):25, 2022.
  https://dl.acm.org/doi/10.1145/3538391
- Hirahara, S. *NP-Hardness of Learning Programs and Partial
  MCSP*.  FOCS 2022.
  https://ieee-focs.org/FOCS-2022-Papers/pdfs/FOCS2022-4Bu7jGV9xIcveUWYj3oWoi/551900a968/551900a968.pdf
- Allender, E., Cheraghchi, M., Myrisiotis, D., Tirumala, H., and
  Volkovich, I.
  *One-way Functions and Partial MCSP*.  ECCC TR21-009, 2021.
  https://eccc.weizmann.ac.il/report/2021/009/download/
- Cheraghchi, M., Kabanets, V., Lu, Z., and Myrisiotis, D.
  *Circuit Lower Bounds for MCSP from Local Pseudorandom
  Generators*.  ICALP 2019.

## 9. Scope guarantees

This report is **markdown-only**.  No Lean code, no JSONL, no
NoGoLog, no `known_guards`, no `barrier_certificate_queue`, no
trust-root edits.  No `ResearchGapWitness`, `SourceTheorem`,
`gap_from`, endpoint, or `P ≠ NP` claim is asserted or modified
by this audit.  The NoGoLog proposals in Section 4 are
**proposals**, listed for operator review; they are **not
applied**.

## 10. Next action

**`open_external_barriers_nogo_proposal_D0`** —
operator-approval-pending follow-up to apply the four NoGoLog
proposals from Section 4 as actual JSONL entries.

Alternative: **`open_fixed_slice_folklore_refutation_L1`** —
formalise small Lean theorems closing the
`FixedSlice*Route` routes that look folklore-refutable, in the
same engineering style as our `not_AsymptoticIsoStrongRoute_canonical`
chain.
