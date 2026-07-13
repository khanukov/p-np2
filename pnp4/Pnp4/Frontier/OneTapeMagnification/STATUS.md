# One-tape small-threshold status

Status: **EXECUTABLE CANONICAL-TRANSCRIPT UNIQUENESS PROVED; VALIDATOR-WIDTH, GENERATOR, AND SMALL-THRESHOLD LOWER-BOUND BRIDGES OPEN**

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
- `TimedCanonicalAlpha.lean`: retains each chronological crossing's source
  time and a bounded terminal `(state, inputHead, workHead)` endpoint.  The
  timed list still has length at most `T / b`, its source times remain strictly
  increasing, and prefix decoding is exact.  The full ambient carrier has
  exact size
  `b^(T/b) * (1 + T * ((T/b) * (2*|Q|*(T+1))))^(T/b) * (|Q|*(T+1)^2)`.
  This closes the finite duration/terminal metadata gap only
  by paying the displayed transcript factor; the carrier includes invalid and
  unreachable values and supplies no slab glue or local validity.
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
- `ActualCrossingSegmentAlignment.lean`: proves the exact set-level
  correspondence between cumulative proper maximal-group stops and
  chronological selected-crossing post-times.  It handles `T = 0` and the
  terminal convention explicitly: a crossing on transition `T - 1` has
  post-time `T` but creates no following nonempty group.  Direction is
  characterized both by the two work-head endpoints and by the adjacent block
  labels; record post-state/post-input-head fields equal the aligned segment
  exit, consecutive schedule endpoints agree, and the fixed initial/terminal
  endpoints are exposed.  A literal equality of newly packaged stop lists is
  not claimed; the proved bidirectional membership theorem is the semantic
  alignment needed here.  All of it remains actual-run extraction.
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
- `WorkSlabPersistence.lean`: proves the complementary locality fact.  A slab
  is unchanged while every pre-transition work head stays outside it, even if
  the last transition enters it.  For two locally synchronized runs, equality
  of a disjoint protected slab is therefore preserved automatically while the
  visited slab is replayed.  The theorem still needs that protected-slab
  equality at entry; it does not yet construct the across-revisit invariant.
- `CanonicalSlabPersistence.lean`: instantiates that fact on the selected-cut
  geometry.  Canonical upper endpoints stay within `T + 1`, distinct block
  labels have disjoint slabs, and the no-full-bucket and zero-time cases are
  explicit.  Replaying one actual maximal group preserves an already equal
  restriction of every other canonical block, including the final exit step.
- `ActualBlockVisitPersistence.lean`: closes the corresponding actual-run
  across-revisit fact.  A consecutive slice of maximal groups is proved to be
  its exact half-open time interval; if every intervening group has a
  non-target label, the target slab restriction after the first visit equals
  its restriction at the second entry.  Empty intervening slices are
  reflexive, while `T = 0` and a terminal crossing cannot fabricate a second
  nonempty visit.  The theorem consumes the true group decomposition and does
  not validate a guessed transcript.
- `TimedAlphaWordValidity.lean`: separates syntactic transcript validation
  from actual-run extraction.  It gives an executable Boolean check that the
  padded word is exactly an encoded prefix and that decoded source times are
  strict.  The true chronological timed alpha passes this check.  This does
  not yet say that an arbitrary syntactically valid word has realizable
  crossing directions or endpoints.
- `AdvertisedCutBlockSlabs.lean`: constructs the complete consecutive slab
  partition directly from an arbitrary alpha's advertised offsets, without
  inspecting a run.  Every represented work cell has a unique owner, distinct
  slabs are disjoint, and every width is at most `2b` when `0 < b`.  The actual
  canonical offsets specialize definitionally to the earlier slabs.  An
  arbitrary advertised offset is still not certified as the leftmost minimum
  of its bucket.
- `FixedAlphaBlockVisitReplay.lean`: defines a positive-duration visit and an
  executable Boolean local replay checker for one advertised block.  It checks
  every pre-transition head, the exact exit state and both heads, carries the
  computed slab contents into the next visit, requires strict separation of
  visits, and has forward and converse concrete-run interfaces.  The checker
  is alpha-relative only through the advertised geometry; it does not by
  itself bind visits to decoded crossing tokens, directions, or cut
  minimality.
- `AdvertisedCrossingEndpoints.lean` and
  `ActualAdvertisedCrossingEndpoints.lean`: reconstruct the physical cut,
  source/destination blocks, pre/post work heads, and post endpoint from each
  timed token.  The endpoints lie in the advertised source/destination slabs,
  and every token extracted from the true run matches the corresponding
  actual cut, state, and both head positions exactly.  No theorem here equates
  a token endpoint with the full work tape.  This per-crossing bridge does not give
  list-level actual completeness; the advertised chaining relation is supplied
  by the next module.
- `TimedAlphaVisitSchedule.lean`: folds the decoded strict timed-token word
  into an advertised-only chronological visit schedule.  A cursor enforces
  source/destination block transitions and exact post-endpoint chaining; the
  two terminal cases forbid a fabricated zero-duration final visit.  Stable
  per-block filtering is proved to give the strict visit separation required
  by the replay checker.  This is a relational schedule specification rather
  than an executable schedule constructor; actual completeness is supplied by
  the next module.
- `ActualTimedAlphaVisitSchedule.lean`: upgrades the earlier set-level
  group-stop/crossing correspondence to equality of the uniquely ordered
  lists, then folds the true timed tokens through all actual maximal groups.
  The extracted timed alpha always has a valid advertised schedule.  The proof
  handles `T = 0`, a last-transition crossing token (which closes the final
  nonempty group without adding a zero visit), and the no-terminal-crossing
  case (which adds exactly one positive final visit).  This closes actual-run
  completeness of the schedule relation, not arbitrary-alpha replay soundness
  or an executable checker.
- `ActualGroupFixedAlphaVisit.lean` and
  `ActualFixedAlphaBlockVisitCarry.lean`: turn a true maximal same-block group
  into a valid fixed-alpha visit.  For two successive visits to one target
  block, actual persistence now proves exact first-output/second-entry slab
  equality, strict temporal separation, acceptance by the recursive/list
  replay checker, and equality of the final fold with the actual second-exit
  slab.  These are completeness bridges for the true decomposition, not a
  soundness theorem for arbitrary advertised visit lists.
- `ActualAllFixedAlphaBlockVisits.lean`: removes the two-visit restriction.
  One strengthened schedule witness is proved to be exactly the ordered list
  of every actual maximal group, in both terminal conventions.  For every
  advertised block, stable filtering of that same witness is chronological,
  is accepted by the carried local replay checker from one literal blank
  slab, and folds to the exact actual block slab at time `T`.  This closes
  all-visit replay completeness for the true transcript; it does not prove
  global soundness for an arbitrary advertised alpha.
- `ExecutableTimedAlphaVisitChecker.lean`: makes the advertised token fold and
  terminal finish executable, proves exact `Option`/relation reflection, and
  combines schedule validity with every stable per-block replay check from a
  literal blank slab in one Boolean predicate.  The actual extracted alpha has
  one schedule accepted by this combined checker.  No reachability premise is
  hidden in its reflection theorem.
- `ArbitraryAlphaGlobalGlue.lean` and
  `ExecutableTimedAlphaGlobalGlue.lean`: close arbitrary-alpha computation
  soundness.  The per-block carried replay folds are interleaved through one
  dependent slab store; one accepted visit updates its source slab and leaves
  every disjoint slab unchanged, including when its last transition enters the
  destination block.  Therefore simultaneous blank-start acceptance realizes
  every visit on one deterministic global run, and the advertised terminal
  endpoint is exactly the run endpoint at time `T`.  The executable corollary
  needs only the combined Boolean checker.  This theorem is about computation
  soundness for advertised geometry; it does not alone establish canonical
  cut selection or equality of the padded token word.
- `AdvertisedCutMinimalityChecker.lean`: gives exact Bool/Prop reflection for
  minimum crossing count plus the leftmost tie-break in every full bucket.
  Against the actual blank-start crossing profile, acceptance is equivalent to
  `alpha.offsets = canonicalCutOffsets`, and equivalently to equality of the
  reconstructed physical cuts with `canonicalCutDescription`.  This closes the
  semantic cut-selection property, but the present specialized checker directly
  evaluates the real run's candidate counts; it is not yet the compact
  per-block counter implementation or its complete live-width bound.
- `FixedAlphaCutCounterReplay.lean`: removes that semantic dependence on a
  precomputed global trajectory.  A recursive streaming counter follows each
  locally materialized visit; it is additive, equals the existing finite-sum
  crossing count, and is invariant under the same-on-slab replay relation.
  Interleaving all accepted visits from the blank slab store yields exactly the
  complete actual crossing profile.  Consequently a replay-based combined
  Boolean checkpoint accepts exactly a valid all-block schedule whose offsets
  are `canonicalCutOffsets`.  For one full bucket the state exposed is exactly
  `Fin b -> Nat`, and every one of its `b` counters is at most `T`.  This proves
  the information needed for a future bounded representation, but does not yet
  encode the counters as bits, build their update circuit, establish a
  read-once branching program, or prove the complete width bound.
- `CutCounterStateCount.lean`: replaces those `b` bounded natural values by
  the explicit carrier `Fin b -> Fin (T + 1)`, of exact cardinality
  `(T + 1)^b`, and pairs it with the already justified local replay state.
  The product carrier has exact size
  `(|Q| * (T + 1) * w * 2^w) * (T + 1)^b`; for a canonical slab it is bounded
  by `(|Q| * (T + 1) * (2b) * 2^(2b)) * (T + 1)^b`.  Accepted replay counters
  are embedded in this carrier and retain exact equality with the actual
  candidate counts.  This is a finite-state cardinal checkpoint, not yet a
  transition circuit, read-once program, or full validator-width theorem.
- `ExecutableTimedAlphaCanonicality.lean`: closes exact transcript
  canonicality for the lower checker.  An accepted fold accounts for every
  selected-boundary crossing and no other token; the terminal visit cannot
  hide a final crossing.  Prefix shape then recovers the whole padded word,
  global glue fixes the terminal endpoint, and the replayed leftmost-minimum
  counters fix every offset.  Hence the combined replay-only checker accepts
  only `chronologicalTimedCanonicalAlpha`, and any two accepted ambient alphas
  are equal (possibly with different exposed schedules).  Together with the
  existing completeness witness, this gives existence and uniqueness of the
  canonical run transcript, including `T = 0`.  It does not yet compile the
  checker into a bounded-width read-once branching program or prove an
  acceptance lower bound for a language.
- `LocalBlockReplayComposition.lean`: composes two same-input slab replays.
  State and both heads at the second entry follow from the first replay, while
  equality of the destination slab at the midpoint remains an explicit and
  necessary premise of the current interface.  A stronger two-slab midpoint
  hypothesis supplies it as a corollary.  This isolates the exact glue datum
  rather than hiding it in a global configuration assumption.
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
the required seed/locality exponent has been proved.  The lower certificate
layer is nevertheless substantially sharper than before: the executable
schedule/all-block/replayed-cut checker has an actual-run completeness witness,
and acceptance of any advertised `alpha` forces equality with the unique
chronological canonical transcript.  This authenticates the deterministic run;
it does not by itself require that the terminal state accepts a language.

The immediate lower-layer implementation theorem still missing is:

> Compile the combined canonical-transcript checker into one deterministic
> adaptive read-once branching program (or an equally explicit local path
> program), including schedule phase, slab replay, terminal handling, and
> leftmost-minimum counter updates, and prove that its complete live carrier is
> at most `2^{O(b * log(Tq))}`.

The present Lean checker is executable and extensionally exact, but its list
recursions, filtered per-block passes, dependent slab store, and natural-number
counter updates have not been compiled into that read-once state machine.
`CutCounterStateCount.lean` counts one justified slab/counter carrier; it does
not yet account for every phase and control component of the whole validator or
prove an exact transition/update circuit.  In particular, one cannot simply
infer the desired width bound from executability.

After that implementation theorem, the central generator object is:

> Construct a circuit-local HSG, or a signed WPRG whose support is such an HSG,
> for the **canonical coherent union of path-transcript programs** produced by
> the Viola simulation of a deterministic one-tape machine.  Its seed and
> fixed-seed DAG complexity must be at most the magnification-admissible
> `N^mu`, and its error/hitting guarantee must apply to the aggregate predicate
> directly, without an `epsilon / |A|` union bound over transcripts.

Canonical boundary selection, schedule construction, every local replay,
arbitrary-alpha global glue, streamed cut counts, leftmost tie-breaking, exact
decoded-word recovery, and full accepted-alpha uniqueness are now formal.  The
combined replay-only checker does not call the semantic actual-run profile in
its definition; the actual run appears only in its soundness/completeness
proofs.  A lossless finite suffix-gluing fallback is also formal, but carries
all `T + 1` reachable tape bits and is exponentially large.

At block scale `b`, the intended compiled bounds remain approximately

```text
log(width) = O(b * log(tq)),
log(number of transcripts) = O((t / b) * log(tq)).
```

Balancing both terms reproduces the published `sqrt(t)` loss.  Uniqueness makes
the coherent union unambiguous, but generic unambiguity does not imply a
small deterministic FBDD.  A successful route must exploit one-tape geometry
to pay for the first term without materializing the transcript-count term, or
construct a generator that hits/fools the unambiguous aggregate directly.
Only then could one choose `b = N^mu / polylog(N)` at the magnification scale.
`BoundaryTapeInterface.lean` identifies the exact lossless-but-exponential
fallback, while `SeparatorScaleBarrier.lean` proves the numerical single-scale
tradeoff.

Even a generator theorem would still need its fixed-seed output tables proved
to have standard-DAG complexity at most `N^mu`, followed by an explicit bridge
from the resulting one-tape lower bound into the repository's `PpolyDAG` /
`VerifiedNPDAGLowerBoundSource` main line.  None of these open statements is an
axiom, contract, provider, or hidden instance.

The remaining direct alternative is an adaptive many-cut YES/NO splicing
lemma for low-circuit truth tables.  The fixed-bipartition row theorem shows
why a standard one-cut communication lower bound cannot be that lemma, but it
does not exclude adaptive crossing signatures.

This alternative also remains prose only.

## Later-literature check (through 2026-07-13)

- [Viola, Theory of Computing 2022, Theorem 2.2 and Section 3](https://theoryofcomputing.org/articles/v018a010/v018a010.pdf)
  confirms that the paper-level lower validator is intended to accept exactly
  one transcript on an accepting run: block replay checks the crossing data,
  and per-boundary counters enforce the minimum count with the smallest cut on
  ties.  Thus arbitrary-alpha global glue is not a new paper-level assumption;
  the formal contribution here is its exact executable realization and edge-
  case audit in the repository's machine convention.
- [Chen--Lyu--Tal--Wu, ICALP 2023, Theorem 7](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.39)
  is the strongest directly relevant structural lead found: it fools width-`w`
  deterministic adaptive read-once branching programs with seed
  `O(log n * log^2(nw/epsilon))`.  It would avoid a transcript union bound if
  the canonical coherent union could first be compiled into one deterministic
  adaptive program at acceptable width and with the required fixed-seed
  locality.  Neither compilation is currently proved here or in that paper.
- Generic unambiguity does not supply that compilation.  [Amarilli--Capelli--
  Monet--Senellart, Theory of Computing Systems 2019, Proposition 3.1](https://pierre.senellart.com/publications/amarilli2019connecting.pdf)
  gives an exponential separation between unambiguous FBDDs and deterministic
  FBDDs.  Therefore any deterministic-adaptive reduction must exploit the
  special canonical one-tape geometry rather than invoke uniqueness alone.
- CHMY's [Theorem 23 and Lemma 27](https://eccc.weizmann.ac.il/report/2020/103/revision/1/download/)
  instead decompose a nondeterministic ROBP into rectangles and choose error
  inversely proportional to the number of components.  That is exactly the
  aggregate union-bound loss whose square-root-scale cost remains open here.
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
- [Volk, ECCC TR26-115](https://eccc.weizmann.ac.il/report/2026/115/)
  proves an improved lower bound for read-once *parity* branching programs.
  It is a model-specific lower bound, not a PRG/HSG for general unknown-order
  Boolean ROBPs, and does not provide the CHMY fixed-seed locality statement.
- [Dermer--Shaltiel, ECCC TR26-017, revision 1](https://eccc.weizmann.ac.il/report/2026/017/)
  gives strong multiplicative PRGs for nondeterministic circuits only under an
  exponential nondeterministic-circuit lower-bound assumption for `E`.  It is
  therefore a conditional hardness-vs-randomness route, not an unconditional
  way around the present aggregate-generator barrier.
- The latest checked ECCC revision,
  [Ren--Williams, TR26-118](https://eccc.weizmann.ac.il/report/2026/118/),
  proves near-maximum circuit lower bounds for exponential time with
  promise-MA queries.  It does not address one-tape MCSP, ROBP
  pseudorandomness, or the validator-and-glue construction here.
- Targeted searches for Boolean PRGs/HSGs for unambiguous branching programs,
  disjoint rectangle unions, and unambiguous DNFs found results only for
  substantially different restrictions (bounded width, known/regular/
  permutation order, shallow DNFs, or algebraic identity testing).  None
  applies to the canonical general exponential-width one-tape aggregate.

No primary source found in this check closes the magnification-admissible
small-`mu` one-tape frontier.  This negative literature finding is not itself
a lower bound.
