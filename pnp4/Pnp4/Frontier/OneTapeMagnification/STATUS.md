# One-tape small-threshold status

Status: **LOWER-LAYER BARRIERS AND DETERMINISTIC LOCAL-HSG CAPSTONE PROVED; NO REQUIRED GENERATOR OR SMALL-THRESHOLD LOWER BOUND**

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
- An exact input-cache normalization.  After one initialization step, the
  normalized machine stores the current logical input symbol in finite
  control, keeps its physical input head one cell ahead, and simulates every
  original step exactly.  Stay transitions are proved independent of the next
  unread symbol.  The control-state count becomes exactly `1 + 3q`.
- Exact deterministic complement closure.  Swapping accept/reject outcomes
  preserves every transition and the full run at the same time bound;
  bounded acceptance of the complement is proved equivalent to bounded
  rejection of the original machine.
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
- A strictly weaker deterministic endpoint: support-only hitting of the dense
  acceptance set of the complemented machine already excludes an exact
  two-outcome MCSP decider.  No seed averaging or ordinary PRG property is
  consumed by this endpoint.
- A signed-WPRG support lemma: if a weighted approximation has error below the
  uniform accepting mass, some nonzero-weight generator output is accepting,
  regardless of negative weights.  The proof uses only that a predicate
  vanishing on the nonzero-weight support has weighted average zero.

These results use the exact standard-DAG MCSP target, including the
`AND`/`OR`/`NOT` basis filter.  The counting image may include a harmless
broader structural-code superset, which only strengthens its upper-bound role;
every semantic `HasCircuit` witness still satisfies the target-basis filter.

The finite exclusion is conditional on an explicit generator and an explicit
fooling hypothesis.  No small-seed generator is postulated or hidden in a
structure, instance, contract, or axiom.

## Fixed-bipartition communication-sparsity checkpoint

`CommunicationSparsity.lean` formalizes a finite row-count obstruction that
does not use an HSG.  If `E` is a finite subset of `A × B`, its Boolean
membership matrix has at most

```text
|E| + 1
```

distinct rows: every nonempty row consumes at least one member of `E`, and all
remaining left coordinates share the empty row.  The theorem is exposed as

```text
sparse_membership_row_count_le_card_add_one
```

The MCSP specialization keeps the semantic and coding sets separate.
`semanticEasyTables n threshold` is the exact finite set whose membership is
`HasCircuit n threshold`.  A separate theorem proves

```text
semanticEasyTables n threshold ⊆ easyTablesByCode n threshold.
```

Thus, for every fixed equivalence

```text
A × B ≃ TruthTable n,
```

the number of distinct exact-MCSP membership rows is at most

```text
2 ^ (DAGCodec.codeLength n threshold) + 1.
```

A separate power-of-two relaxation bounds this by
`2 ^ (DAGCodec.codeLength n threshold + 1)`; this relaxation is convenient
for a later row-identifier encoding but is not presented as the tight count.

There is also a version for an arbitrary finite `E` under the explicit
hypothesis `E ⊆ easyTablesByCode n threshold`.  No theorem identifies the
codec-image superset with the exact semantic YES-set.

This checkpoint is scoped to one fixed bipartition.  It does not formalize a
communication protocol, crossing-sequence simulation, information-complexity
bound, adaptive partition, many-cut argument, or one-tape time lower bound.
In particular it is not a no-go theorem for all crossing-sequence methods and
does not prove the small-threshold CHMY lower bound.  Its role is to rule out
overstating a fixed-split row-count target as a route to that lower bound.

## Deterministic support-HSG endpoint

`LocalHSGToMCSP.lean` removes an unnecessary randomized requirement from the
lower-bound endpoint.  Under the same explicit code-length inequality, tables
outside `easyTablesByCode` form a subset of semantic coMCSP containing more
than half of the truth-table cube.  If a fixed deterministic one-tape machine's
bounded acceptance predicate is exactly coMCSP and a `DAGLocalGenerator` hits
that machine's accepting set whenever it is dense, some fixed-seed output must
be both hard and certified easy.  The theorem

```text
localGenerator_denseHitting_excludes_exactCoMCSP
```

derives that contradiction without probabilities over seeds.

`DeterministicComplement.lean` proves the missing transfer to ordinary MCSP.
For the explicit two-outcome behavior `ExactMCSPDecisionBehavior`, swapping
the halt outcomes preserves the time bound and turns rejection of hard tables
into coMCSP acceptance.  Consequently

```text
localGenerator_denseHitting_excludes_exactMCSPDecision
```

directly excludes an exact MCSP decider when the same generator hits the fixed
complemented machine's dense accepting set.

`WeightedPRGSupport.lean` proves the generic signed support principle.  For
arbitrary rational weights, additive approximation error `epsilon` and uniform
accepting mass strictly above `epsilon` imply an accepting seed carrying
nonzero weight.  `WeightedPRGToHSG.lean` then completes the finite composition:

- density above one half implies that the exact Boolean acceptance indicator
  has uniform rational average above one half;
- any signed approximation with `0 <= epsilon < 1/2` yields
  `HitsDenseOneTapeAcceptance` for the fixed machine;
- `signedWeightedApproximation_excludes_exactMCSPDecision` directly rules out
  exact MCSP decision when the approximated predicate is acceptance of the
  complemented machine.

The acceptance indicator is deliberately noncomputable at this semantic
layer.  A useful WPRG still has to be explicitly constructed and its
fixed-seed outputs proved to have the required DAG complexity; neither fact is
assumed here.

## Lower-layer abstractions that do not suffice

Three additional finite checkpoints isolate what a successful construction
must use.

- `SupportAvoidance.lean`: every map `H : Seed -> Table` is defeated by the
  predicate accepting exactly the complement of its image.  If `|Seed| <
  |Table|`, that predicate is nonempty, and its exact accepted-set cardinality
  and the lower bound `|Table| - |Seed|` are proved.  Therefore an HSG theorem
  cannot quantify over an unrestricted predicate class.
- `UnambiguousFamilyBarrier.lean`: every Boolean predicate is exactly the
  disjoint union of singleton components, with one accepting component on
  each accepted input and none on rejected inputs.  Abstract unambiguity alone
  therefore restricts no predicate at all.  Any improvement must retain the
  coherent canonical-path and uniform local-transition structure of the
  one-tape simulation.
- `CanonicalBoundarySelection.lean`: split `T` boundary positions into the
  `T / b` full buckets of length `b`, deliberately leaving the `T % b` tail
  uncovered.  The leftmost minimum-crossing boundary of every full bucket is
  selected canonically.  The formal charging chain is

  ```text
  b * sum(selected crossings)
    <= sum(crossings in full buckets)
    <= sum(all crossings).
  ```

  Hence total crossing count at most `T` gives selected count sum at most
  `T / b`.  Adjacent selected boundaries are strictly ordered and less than
  `2b` positions apart.  This closes the combinatorial scale core, not the
  machine-to-ROBP simulation.
- `WorkHeadCrossings.lean` and `CanonicalBlockGaps.lean`: instantiate that
  abstract charging argument on the actual blank-start trajectory.  Stay
  moves, halted stuttering, and the clamped left move at cell zero cross no
  boundary; each other step crosses at most one, so the total is at most `T`
  and the selected total is at most `T / b`.  When a full bucket exists, the
  first cut is before `b`, every adjacent gap is below `2b`, and the final tail
  is below `2b`.  These are trajectory and metric facts only, not local
  validators or a width bound.
- `CanonicalWorkBlocks.lean`: turns the ordered cuts into an explicit rank
  classifier with `T / b + 1` consecutive block labels.  Every represented
  work cell belongs to exactly one block, any two cells in one block are less
  than `2b` apart (also when `T / b = 0`), and a legal one-step move changes
  labels exactly when it crosses a selected canonical cut.  The resulting
  actual-run classifier has the precise type needed by the input-event layer,
  but is still input-dependent.
- `CanonicalCrossingRecords.lean`: attaches the bucket index, physical cut,
  crossing direction, post-transition control state, and bounded input-head
  position to every actual selected-cut crossing.  It separately stores all
  physical cuts, including zero-crossing cuts.  The number of extracted
  records is exactly the selected crossing sum and therefore at most `T / b`.
  An ambient payload vector has exactly
  `(2 * |Q| * (T + 1))^(T / b)` possibilities, while the full ambient
  cut-plus-fixed-payload carrier has
  `T^(T / b) * (2 * |Q| * (T + 1))^(T / b)` possibilities.  These are carrier
  counts, not reachable-count bounds, and the fixed payload word is not
  identified with the variable-length extracted list.  This choice-derived
  enumeration is not chronological; the later chronological extractor fixes
  that order, while fixed-transcript validation and gluing remain unproved.
- `CanonicalCutOffsets.lean`: uses bucket membership to encode every physical
  cut by its unique `Fin b` offset and reconstructs the complete cut vector
  exactly.  The offset carrier has size `b^(T / b)`, refining the coarse
  `T^(T / b)` cut factor; paired with the fixed payload word, the ambient size
  is exactly
  `b^(T / b) * (2 * |Q| * (T + 1))^(T / b)`.  This still does not encode the
  length of the variable crossing list or assert local validity.
- `PaddedCanonicalAlpha.lean`: closes that finite-encoding gap without a
  fake default record.  A bucket-labelled crossing token is stored in an
  optional prefix slot, decoding exactly recovers every list of length at most
  `T / b`, and the physical cut is recovered from the retained offsets.  The
  complete offsets-plus-padded-word carrier has exact size
  `b^(T / b) * (1 + (T / b) * (2 * |Q| * (T + 1)))^(T / b)`.  This is now a
  faithful finite carrier for any bounded token list.  The older
  Finset-derived extractor does not by itself supply chronological order, and
  membership in this carrier is not a local-validity theorem.
- `ChronologicalCanonicalAlpha.lean`: removes that ordering caveat for the
  concrete run.  Every retained crossing time has a unique selected bucket;
  the timed entries project exactly to the strictly increasing filtered time
  list, and the resulting record/token list has length at most `T / b`.
  Physical cuts are reconstructed from the canonical offset vector, while
  prefix decoding exactly recovers the chronological tokens.  This is an
  input-dependent extraction theorem, not a local validator or
  input-independent advice construction.
- `LowRunInputOrder.lean`, `ActualRunInputOrder.lean`, and
  `StableGroupingPermutation.lean`: stable grouping by occupied work blocks
  preserves chronological order inside each block.  The concrete one-way run
  has nondecreasing raw head positions, while its advancing positions are
  strictly increasing; hence the grouped query order is a concatenation of at
  most `K + 1` strict runs.  Grouping is proved to be a permutation of the
  original events and fresh coordinates, so the complete grouped fresh order
  is globally duplicate-free, not merely duplicate-free within each run.
  Ignored stay events are removed exactly, and the cached-input transition on
  a simulated stay is independent of the next unread physical symbol.  The
  actual classifier is now supplied by `CanonicalWorkBlocks.lean`, but its
  dependence on the run does not by itself give the fixed order of one
  guessed transcript or a Viola simulation.
- `CrossingScheduleInputOrder.lean`: at the abstract schedule level, a fixed
  `alpha` with chained input-head endpoints determines each segment's
  half-open fresh interval.  Chronological concatenation is one interval;
  stable work-block grouping is a permutation of it and therefore gives one
  fixed duplicate-free order.  The actual-run modules below connect the true
  extracted schedule to machine replay.  What remains is to derive and check
  those endpoints and replay interfaces from one fixed guessed `alpha`, not a
  further combinatorial read-once argument.
- `ActualCrossingSchedule.lean`: extracts the chronological selected-crossing
  times of the concrete run and proves there are at most `T / b` of them.  It
  splits all transition times into maximal consecutive same-block runs,
  proves there are at most `T / b + 1` such runs and schedule segments,
  constructs a chained `FixedCrossingSchedule` from their actual input-head
  endpoints, and proves that its chronological query interval is exactly the
  actual advancing-position list.  Stable work-block replay merely permutes
  that list.  The schedule is still extracted from one input-dependent run;
  local validation from a fixed guessed `alpha` is not yet proved.
- `CanonicalPathTranscript.lean`: extracts a finite bounded transcript from a
  deterministic run, records optional crossed boundaries and the canonical
  cut in every full bucket, and proves both the global and selected crossing
  budgets.  The fiber defined by exact canonical extraction is a singleton,
  including on accepting runs.  This is not yet local unambiguity: the current
  snapshots expose the scanned work symbol, not enough boundary-relevant tape
  valuation to validate and glue block computations independently.
- `BoundaryTapeInterface.lean`: proves the exact coarse repair.  After `T`
  blank-start steps, every cell at index at least `T` is still blank, so the
  first `T + 1` work cells, the state, and both heads reconstruct the whole
  configuration and deterministically glue every suffix.  The tape carrier
  has exactly `2^(T+1)` elements and the full carrier has
  `|Q| * (T+1)^2 * 2^(T+1)` elements.  This is a carrier count, not a lower
  bound on reachable interfaces; it shows that the proved lossless repair is
  far too coarse for the desired small-width program.
- `LocalBlockReplay.lean`: restricts a work tape to a consecutive finite slab
  and proves exact write compatibility.  Agreement on state, heads, the
  current input observation, and the slab containing the scanned cell is
  preserved by one deterministic step; an explicit per-time inside-slab and
  input-observation invariant lifts this to a finite replay, with the final
  step allowed to exit.  This supplies the local determinism lemma consumed
  by the actual-segment replay below; by itself it does not validate guessed
  crossing records or give a complete program-width bound.
- `CanonicalBlockSlabs.lean`: supplies that spatial connection.  Every
  canonical block has explicit lower and upper-exclusive endpoints, positive
  width at most `2b`, and exact equivalence between its rank label and
  `WorkCellInSlab`.  A trajectory carrying a block label therefore satisfies
  the precise inside-slab premise of local replay.
- `ActualSegmentSlabReplay.lean`: packages each maximal same-block group as
  its exact consecutive time interval, proves its label is constant, and
  places every pre-transition work head in the corresponding canonical slab,
  including the last step before a possible exit.  Any alternative entry
  configuration agreeing with the actual entry on state, both heads, and that
  slab replays the whole group on the same immutable input and agrees again at
  the exit.  This connects actual segments to local replay, but it assumes the
  true entry interface and does not check a guessed chronological `alpha`,
  canonical-cut minimality, or consistency between different block visits.
- `LocalBlockStateCount.lean`: the finite state already justified by slab
  replay has exact size `|Q| * (T + 1) * w * 2^w`; for a canonical slab this
  is at most `|Q| * (T + 1) * (2b) * 2^(2b)`.  This is a pre-step local
  carrier, not the full program width: the final crossing may leave the slab,
  and boundary-minimality counters, schedule phase, and validator state are
  deliberately absent.
- `SeparatorScaleBarrier.lean`: for every single-scale accounting satisfying
  `time <= blockCost * transcriptCost`, one common budget that dominates both
  costs must have square at least `time`.  A budget below square-root capacity
  necessarily fails on one side.  This is only an arithmetic consequence of
  independently charging the two costs, not a lower bound against collective
  PRGs/HSGs.

Together with the fixed-split row bound, these lemmas rule out four overly
coarse targets: unrestricted predicates, bare unambiguity, independent
single-scale charging, and one fixed communication cut.  They do not rule out
a coherent aggregate HSG or an adaptive many-cut splicing argument.

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

No one-tape lower bound at the required small threshold and no generator with
the required seed/locality exponent has been proved.  The deterministic finite
capstone is now closed conditional on dense hitting; the missing mathematical
object is narrower:

> Construct a circuit-local HSG, or a signed WPRG whose support is such an HSG,
> for the **canonical coherent union of path-transcript programs** produced by
> the Viola simulation of a deterministic one-tape machine.  Its seed and
> fixed-seed DAG complexity must be at most the magnification-admissible
> `N^mu`, and its error/hitting guarantee must apply to the aggregate predicate
> directly, without an `epsilon / |A|` union bound over transcripts.

The canonical-boundary selection, its instantiation on actual runs, exact
endpoint gaps, chronological padded crossing data, maximal-run schedule, and
same-slab replay of every actual segment are now formal.  A lossless finite
suffix-gluing interface is also formal, but it carries all `T + 1` reachable
tape bits and is exponentially large.

The immediate lower-layer gap is now the **validator-and-glue theorem**.  For
one fixed chronological `alpha`, construct a finite local block validator
which:

1. starts from the blank tape and replays every visit assigned to a block in
   the order recorded by `alpha`;
2. checks every entry/exit state, input-head position, direction, and shared
   boundary observation against the neighboring crossing records;
3. certifies that every advertised cut is the leftmost minimum-crossing
   boundary of its bucket, including the required per-candidate counters;
4. accepts exactly the true canonical transcript, so the accepted local
   pieces have a unique global glue; and
5. keeps the complete live carrier, including phase and validation data,
   within `2^{O(b * log(tq))}`.

The current segment-replay theorem proves the deterministic core needed by
item 1 once the true entry interface is supplied; it proves none of items
2--5 for a guessed transcript.  Completing this machine-to-path-program
construction at block scale `b` should give approximately

```text
log(width) = O(b * log(tq)),
log(number of transcripts) = O((t / b) * log(tq)).
```

Balancing the two reproduces `sqrt(t)`.  A collective construction that pays
for the first term but not the transcript count could choose
`b = N^mu / polylog(N)` and reach the required threshold.  The
scale-parameterized validator-and-unique-glue theorem and the collective HSG
are not yet formalized.  Even a successful validator would still leave the
separate generator problem stated above: fool or hit the coherent disjoint
union directly without paying `epsilon / |A|` over transcripts.
`BoundaryTapeInterface.lean` identifies the exact lossless-but-exponential
fallback, while `SeparatorScaleBarrier.lean` proves the numerical single-scale
tradeoff.

The remaining direct alternative is an adaptive many-cut YES/NO splicing
lemma for low-circuit truth tables.  The fixed-bipartition row theorem shows
why a standard one-cut communication lower bound cannot be that lemma, but it
does not exclude adaptive crossing signatures.

This question remains prose only.  It must not be represented by an axiom,
typeclass, `Contract`, `Source`, `Provider`, structure field, or implicit
instance.

## Later-literature check (through 2026-07-10)

- The [journal version of CHMY](https://link.springer.com/article/10.1007/s00224-022-10113-9) retains the large-threshold one-tape result and the same Appendix-A magnification direction; it does not supply a small-threshold lower bound.
- [ECCC TR25-017](https://eccc.weizmann.ac.il/report/2025/017/) develops a square-root-space simulation for multitape time, not the local HSG/PRG needed here.
- [Cheng--Wu, ECCC TR25-027, Theorems 1.5 and 1.7](https://eccc.weizmann.ac.il/report/2025/027/revision/4/download)
  and [Ta-Shma--Chen, ECCC TR25-067, Theorem 1.1](https://eccc.weizmann.ac.il/report/2025/067/download)
  improve WPRGs for standard-order or regular ROBPs.  Their bounds retain a
  `log(width)` dependence and do not cover the general unknown-order CHMY
  branching programs or the required circuit-locality statement.
- [Lee--Viola, ECCC TR25-071, Theorem 5](https://eccc.weizmann.ac.il/report/2025/071/revision/1/download)
  is a genuine any-order near miss, but only for permutation ROBPs over a
  fixed `p`-group; CHMY Lemma 20 produces general exponential-width ROBPs.
- [Chen--Cohen--Doron--Khaskelberg--Ta-Shma, ECCC TR26-064, revision 3](https://eccc.weizmann.ac.il/report/2026/064/revision/3/download)
  improves WPRG error reduction while preserving the base seed and its
  `log(width)` dependence.  It is standard-order, weighted pseudorandomness
  and supplies neither a uniform-seed local HSG nor the CHMY locality needed
  here.
- [Pyne--Vadhan, *Pseudodistributions That Beat All Pseudorandom Generators*](https://theoryofcomputing.org/articles/v022a003/), Theory of Computing 2026,
  confirms that signed WPRGs can beat ordinary PRG seed length, but its main
  construction is for ordered permutation branching programs, not the general
  unknown-order coherent CHMY aggregate.
- [Doron--Goldreich, ECCC TR26-094](https://eccc.weizmann.ac.il/report/2026/094/download/)
  clarifies that nonnegative weighted generators can be deweighted, while the
  genuine WPRG advantage relies on negative weights.  Negative weights are
  compatible with the proved support endpoint, but the paper does not supply
  the missing one-tape aggregate construction or fixed-seed DAG locality.
- Targeted searches for Boolean PRGs/HSGs for unambiguous branching programs,
  disjoint rectangle unions, and unambiguous DNFs found results only for
  substantially different restrictions (bounded width, known/regular/
  permutation order, shallow DNFs, or algebraic identity testing).  None
  applies to the canonical general exponential-width one-tape aggregate.

No primary source found in this check closes the magnification-admissible
small-`mu` one-tape frontier.  This negative literature finding is not itself
a lower bound.
