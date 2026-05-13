# Q3 — descriptive non-natural filters

## §1. Question

> What descriptive complexity or model-theoretic results
> characterise "natural" filter properties in the Razborov-Rudich
> sense, AND what alternative "non-natural" property classes are
> known to exist?

## §2. Cited results

* Ronald Fagin, "Generalized First-Order Spectra and Polynomial-Time Recognizable Sets," 1974, in *Complexity of Computation*, SIAM-AMS Proceedings 7, pp. 27--41.
  One-sentence summary: Fagin's theorem identifies existential second-order definability over finite structures with NP-recognisability, giving the baseline descriptive-complexity dictionary for properties of finite objects such as truth tables or formula/provenance encodings.
  Verifiable identifier: SIAM-AMS Proceedings 7, pp. 27--41; bibliographic record at https://www.scirp.org/reference/referencespapers?referenceid=3347438.

* Neil Immerman, "Relational Queries Computable in Polynomial Time," 1986, *Information and Control* 68, pp. 86--104; Moshe Y. Vardi, "The Complexity of Relational Query Languages," 1982, STOC, pp. 137--146.
  One-sentence summary: the Immerman--Vardi theorem says that least-fixed-point logic over ordered finite structures captures polynomial time, so a polynomial-time constructive Razborov--Rudich property can be rephrased as an order-sensitive FO(LFP)-definable query over a truth-table structure.
  Verifiable identifier: Immerman paper URL listed at https://michaelnielsen.org/polymath/index.php?title=Immerman-Vardi_theorem; Vardi STOC 1982 pp. 137--146 listed there as well.

* Alexander A. Razborov and Steven Rudich, "Natural Proofs," 1997, *Journal of Computer and System Sciences* 55(1), pp. 24--35.
  One-sentence summary: this is the barrier definition whose constructivity, largeness, and usefulness triad the report tries to recast in descriptive/model-theoretic terms.
  Verifiable identifier: JCSS 55(1), pp. 24--35; DOI 10.1006/jcss.1997.1494; bibliographic record at https://colab.ws/articles/10.1006/jcss.1997.1494.

* Jin-yi Cai, Martin Fürer, and Neil Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification," 1992, *Combinatorica* 12(4), pp. 389--410.
  One-sentence summary: the CFI construction gives explicit pairs of finite structures indistinguishable by bounded-variable first-order logic with counting, showing that natural-looking logical invariants can miss polynomial-time distinguishers.
  Verifiable identifier: author PDF at https://people.cs.umass.edu/~immerman/pub/opt.pdf; *Combinatorica* 12(4), pp. 389--410.

* Timothy Y. Chow, "Almost-natural proofs," 2009 version, arXiv preprint.
  One-sentence summary: Chow weakens largeness and obtains useful, constructive, "almost-natural" properties under the same pseudorandomness assumption used by Razborov--Rudich, making low-density property classes a concrete non-natural family to model.
  Verifiable identifier: arXiv:0805.1385, https://arxiv.org/abs/0805.1385.

* Ryan Williams, "Natural Proofs Versus Derandomization," 2013 STOC special-issue version / arXiv preprint.
  One-sentence summary: Williams characterises natural-property existence and nonexistence via derandomisation, warning that simply removing constructivity from a filter is not a free bypass and suggesting that an audit should record the exact derandomisation strength implicitly assumed.
  Verifiable identifier: arXiv:1212.1891, https://arxiv.org/abs/1212.1891.

* Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, and Detlef Ronneburger, "Power from Random Strings," 2006, *SIAM Journal on Computing* 35(6), pp. 1467--1493.
  One-sentence summary: high Kolmogorov-complexity string sets give nonconstructive or resource-bounded-compression property classes that are far from large constructive natural properties but still interact nontrivially with standard complexity classes.
  Verifiable identifier: DOI 10.1137/050628994; SIAM page https://epubs.siam.org/doi/10.1137/050628994.

* Valentine Kabanets and Jin-Yi Cai, "Circuit Minimization Problem," 2000, STOC, pp. 73--79.
  One-sentence summary: MCSP asks whether a truth table has a small circuit and is the canonical complexity-theoretic interface between truth-table definability, resource-bounded compression, and lower-bound consequences.
  Verifiable identifier: STOC 2000 pp. 73--79; DOI 10.1145/335305.335314; author page https://www.cs.sfu.ca/~kabanets/Research/circuit.html.

* Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, and Antonina Kolokolova, "Learning Algorithms from Natural Proofs," 2016, CCC, LIPIcs 50, article 10.
  One-sentence summary: natural proofs against sufficiently expressive circuit classes imply learning algorithms, giving a second audit dimension for any proposed constructive logical property: if it is large and useful, it may also carry learning consequences.
  Verifiable identifier: DOI 10.4230/LIPIcs.CCC.2016.10; Dagstuhl page https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2016.10.

## §3. Concrete embedding sketch

Progress classification: Infrastructure.  This report proposes no lower-bound route, no candidate, no Lean code, and no final claim; it only sketches a vocabulary that could later make `ProvenanceFilter_v2` auditable against natural-proofs-like failure modes.

The smallest useful import into this repository would be a documentation-level and later Lean-level taxonomy for property classes over encoded Boolean functions or formula families:

* `ConstructiveByLogic L P`: the property `P` is definable by a fixed finite-model logic `L` on the ordered truth-table/provenance encoding.  For `L = FO(LFP)` over ordered encodings, this is the descriptive-complexity analogue of polynomial-time constructivity.
* `LargeByMeasure μ δ P`: the property has density at least `δ n` under a chosen measure on truth tables or provenance encodings.  This field should be deliberately separate from constructivity so that Chow-style almost-large properties can be represented without silently becoming Razborov--Rudich-large.
* `UsefulAgainstModel M P`: every family satisfying `P` eventually avoids the circuit/provenance model `M`.
* `SymmetryBlind L P`: membership of `P` is invariant under a chosen class of isomorphisms/renamings or is indistinguishable by a bounded-variable/counting fragment.  CFI-style examples make this a warning flag: a property can be highly structured and still blind to semantic distinctions relevant to circuits.
* `CompressionDefined κ t P`: `P` is defined by a Kolmogorov/KT/MCSP-style compression threshold rather than by a local syntactic support statistic.

Existing audit modules touched conceptually: `pnp3/Barrier/NaturalProofs.lean` supplies the constructivity/largeness/usefulness triad; `pnp3/Barrier/Relativization.lean` and `pnp3/Barrier/Algebrization.lean` supply the oracle-invariance questions for §5; the hardwiring NoGos point to `pnp3/Magnification/AuditRoutes/` as the future home for any route-specific audit predicates.  No file under `pnp3/` should be edited by this report.

A plausible future module location, if separately approved, would be `pnp3/Magnification/AuditRoutes/DescriptiveNonNatural.lean`, but this report intentionally does not create it.  In months rather than years, the viable first milestone would be to formalise only a finite taxonomy and implications among abstract predicates, not Fagin's theorem or Immerman--Vardi.  The minimal first Lean theorem would be an abstract natural-barrier trigger such as: if a property is `ConstructiveByLogic FO_LFP`, `LargeByMeasure` at Razborov--Rudich density, and `UsefulAgainstModel Ppoly`, then it satisfies the existing `SatisfiesNaturalProofBarrier` interface.  A companion bypass theorem would require a witnessed failure of at least one field, e.g. `AlmostLargeButNotLarge` or `CompressionDefined` plus an explicit non-constructivity marker.

The concrete embedding advice for `ProvenanceFilter_v2` is negative and audit-oriented: do not ship another filter whose only semantic content is support cardinality, width, or rename-invariant locality.  Instead, require every proposed provenance predicate to declare which descriptive bucket it occupies: FO/LFP-definable constructive, almost-large-but-not-large, compression-defined, or explicitly nonconstructive.  This declaration would not prove a lower bound, but it would make future barrier review less ad hoc.

## §4. Self-attack against existing NoGos

* NOGO-000001: NO as a direct refutation, YES as a design warning.  NOGO-000001 kills `FixedParamsRoute` combined with `OverbroadUniformProvenance` because that combination reconstructs an old overbroad support-restriction route.  The descriptive/model-theoretic idea here does not assert fixed-parameter provenance and does not imply `OverbroadUniformProvenance`; it is a classification wrapper around possible properties.  However, if someone instantiated `ConstructiveByLogic` with a logic formula that merely recognises the same overbroad uniform provenance condition, the NoGo would apply immediately.  Therefore the taxonomy must record that overbroad uniform provenance is a rejected instance, not a valid example.

* NOGO-000004: NO as a direct refutation, YES for pure support-cardinality fragments.  NOGO-000004 shows that log-width prefix-AND hardwiring passes `InSupportFunctionalDiversity`, so any filter expressed purely by unbounded-but-sublinear support cardinality is dead.  A descriptive logic wrapper does not by itself depend on support cardinality; it can express, or refuse to express, much richer provenance information.  But a future FO/LFP property whose only atomic facts are support size, width, and rename-invariant support membership would be just a syntactic rebranding of the defeated class.

* NOGO-000005: NO as a new attack, YES as scope discipline.  NOGO-000005 corrected the scope of the prefix-AND obstruction and warned that excluding only that special family is insufficient.  The Q3 idea is compatible with that warning: it treats prefix-AND as a test case for a too-coarse descriptive signature, not as the whole obstruction.  The embedding must therefore include arbitrary payload sensitivity as an audit requirement rather than claiming that a logical description excluding prefix-AND has solved hardwiring.

* NOGO-000006: NO only if the future predicate inspects something beyond all-essential log-width truth-table support; YES for any property reducible to support cardinality.  NOGO-000006 supersedes the prefix-only warning by allowing arbitrary all-essential log-width `ttFormula` payloads injected into ambient variables.  A descriptive/model-theoretic property is not killed merely because it is definable; it is killed if its vocabulary cannot distinguish arbitrary truth-table payload hardwiring from genuine provenance structure.  The proposed escape hatch is to make `CompressionDefined` or semantic-circuit predicates talk about the payload's truth table, generation history, or compression threshold, not just the number of touched coordinates.  This is not a proof that such a predicate works; it is the precise reason the report is only a survivor for audit vocabulary, not a candidate lower-bound route.

## §5. Self-attack against classical barriers

* Relativization: the proposal does not currently satisfy a relativizing-proof hypothesis because it is not a proof scheme for a lower bound; it is a classification scheme for properties.  If later instantiated as an oracle-parametric statement saying that a given logical property separates a language from `PpolyDAG` for every oracle, the existing `Relativizing` interface would demand an oracle-bypass witness.  Descriptive definability over ordered finite structures is usually machine-model-independent, but lower-bound usefulness is not automatically nonrelativizing.  Any future seed pack must therefore mark relativization status as unknown until it gives two oracle worlds or explicitly avoids making oracle-invariant claims.

* Natural Proofs: this is the central barrier.  FO(LFP)-definable plus large plus useful is exactly the danger zone: by Immerman--Vardi, an ordered finite-structure FO(LFP) definition is a descriptive version of polynomial-time constructivity, so adding Razborov--Rudich largeness and usefulness would satisfy the triad represented in `NaturalProofs.lean`.  The only acceptable non-natural classes in this report are those with an explicit failed field: not-large/almost-large Chow-style density, nonconstructive Kolmogorov-style definitions, or compression/MCSP thresholds whose constructivity is recorded rather than assumed.  Thus the barrier is not bypassed; it is turned into a required typeclass-like checklist.

* Algebrization: the proposal does not use arithmetisation or algebraic oracle access, so it does not by itself algebrize.  That said, finite-model definability can be insensitive to algebraic extensions unless the encoding includes field operations or low-degree extension data.  Any future compression-defined predicate imported into a magnification route would need an `AlgebrizationBypassWitness`-style argument or an explicit statement that it is only a barrier-audit predicate.  At the report stage, the safe answer is that algebrization neither kills nor validates the idea.

## §6. Verdict

`survivor`

Reason: the literature does not provide a ready-made lower-bound move, and it must not be reported as P-vs-NP mainline progress.  It does provide a useful, verifiable audit vocabulary: natural properties can be represented as constructive logical definability plus largeness plus usefulness, while non-natural alternatives split into at least three sharply different buckets: almost-large but not large, nonconstructive/high-Kolmogorov, and compression/MCSP-defined.  The idea survives only as infrastructure for `ProvenanceFilter_v2` review and future barrier audit.

## §7. Follow-up seed pack outline (only if `survivor`)

* Proposed seed pack id: `fp3b5_descriptive_nonnatural_audit`.
* Goal: design a purely audit-level taxonomy for future provenance filters that records whether a proposed property is FO/LFP-definable constructive, Razborov--Rudich-large, useful against a stated model, almost-large but not large, nonconstructive, or compression-defined.  The pack should not prove or promote any lower-bound route; its deliverable is a barrier checklist preventing support-cardinality hardwiring failures from being hidden behind new terminology.
* Suggested slot decomposition:
  1. Bibliography verification slot: re-check the nine references above and reduce them to a short operator-approved citation set.
  2. Vocabulary slot: draft names and informal semantics for constructivity, largeness, usefulness, symmetry blindness, and compression-defined predicates.
  3. NoGo regression slot: map NOGO-000001, NOGO-000004, NOGO-000005, and NOGO-000006 into negative examples for the vocabulary.
  4. Barrier-interface slot: specify how each vocabulary field would connect to `NaturalProofConditions`, `Relativizing`, and `Algebrizing` without adding mathematical strength.
  5. Surface-test slot: if Lean is later approved, add only abstract tests that prevent a filter from claiming natural-proof bypass without a failed triad field.
* Inherited forbidden scope from this seed pack: no Lean code unless a separate operator-approved seed pack explicitly asks for it; no trust-root edits; no JSONL edits; no candidate; no `gap_from_*`, `SourceTheorem_*`, FP-4, or final endpoint claim; no unconditional final separation claim; no description of this infrastructure as mainline lower-bound progress.
