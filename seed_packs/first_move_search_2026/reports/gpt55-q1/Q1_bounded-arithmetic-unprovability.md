# Q1 — bounded-arithmetic unprovability meta-theorems for provenance filters

## 1. Question

> What proof-complexity / bounded-arithmetic meta-theorems after 2010 imply that some classes of formula provenance filters cannot be proven valid in subsystems of PA / EF?

## 2. Cited results

* Jan Bydžovský, Jan Krajíček, and Igor C. Oliveira, "Circuit lower bounds in bounded arithmetics," 2015, *Annals of Pure and Applied Logic* 166(1):29-45.
  One-sentence summary: this paper formalizes polynomial circuit lower-bound statements in bounded arithmetic and proves conditional or unconditional unprovability results for weak feasible theories, including an unconditional result for `V^0` and quasi-polynomial SAT circuit lower bounds.
  Verifiable identifier: DOI `10.1016/j.apal.2014.08.004`; ECCC TR13-077; publisher page `https://www.sciencedirect.com/science/article/pii/S0168007214000888`.

* Moritz Müller and Ján Pich, "Feasibly constructive proofs of succinct weak circuit lower bounds," 2020, *Annals of Pure and Applied Logic* 171(2):102735.
  One-sentence summary: the paper asks which known circuit lower bounds have feasible bounded-arithmetic formalizations, proves several positive formalizations in `APC_1`, and explicitly formalizes the natural-proofs barrier in this bounded-arithmetic setting.
  Verifiable identifier: DOI `10.1016/j.apal.2019.102735`; publisher page `https://www.sciencedirect.com/science/article/pii/S0168007219300983`.

* Ján Pich and Rahul Santhanam, "Why are Proof Complexity Lower Bounds Hard?," 2019, IEEE *FOCS*, pp. 1305-1324.
  One-sentence summary: this work gives a proof-complexity analogue of natural-proofs-style obstruction, showing that strong enough propositional proof systems cannot efficiently prove certain average-case proof-complexity lower-bound statements under the paper's hypotheses.
  Verifiable identifier: DOI `10.1109/FOCS.2019.00080`; IEEE/FOCS page `https://ieee-focs.org/FOCS-2019-Papers/`.

* Ján Pich and Rahul Santhanam, "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly," 2021, ACM *STOC*, pp. 223-233.
  One-sentence summary: the paper unconditionally proves that Cook-style feasible arithmetic cannot prove, for any nondeterministic polynomial-time machine, strong inapproximability by subexponential-size co-nondeterministic circuits, and extends the statement to a fragment related to approximate counting.
  Verifiable identifier: DOI `10.1145/3406325.3451117`; Oxford repository page `https://ora.ox.ac.uk/objects/uuid:4bb0ed7a-1983-4d95-8296-ab973094292e`.

* Marco Carmosino, Valentine Kabanets, Antonina Kolokolova, and Igor C. Oliveira, "LEARN-Uniform Circuit Lower Bounds and Provability in Bounded Arithmetic," 2021/2022, IEEE *FOCS 2021*, pp. 770-780.
  One-sentence summary: this work connects proof extraction in bounded arithmetic to LEARN-uniform circuit generation and uses lower bounds against such generators to derive robust unprovability results for non-uniform circuit upper-bound statements in theories including `PV` and variants using approximate counting.
  Verifiable identifier: DOI `10.1109/FOCS52979.2021.00080`; ECCC TR21-095; project page `https://www2.cs.sfu.ca/~kabanets/Research/LEARN-BA.html`.

* Jiatu Li and Igor C. Oliveira, "Unprovability of Strong Complexity Lower Bounds in Bounded Arithmetic," 2023, ACM *STOC*, pp. 1051-1057.
  One-sentence summary: this paper extends bounded-arithmetic unprovability to stronger theories and more natural high-quantifier-complexity lower-bound sentences, including unconditional unprovability for `APC_1`-level strong complexity lower bounds.
  Verifiable identifier: DOI `10.1145/3564246.3585144`; arXiv `2305.15235`; Warwick repository page `https://wrap.warwick.ac.uk/id/eprint/174718/`.

* Lijie Chen, Jiatu Li, and Igor C. Oliveira, "On the Unprovability of Circuit Size Bounds in Intuitionistic `S^1_2`," 2025, *Logical Methods in Computer Science* 21(3:26).
  One-sentence summary: this paper gives an unconditional unprovability result for fixed-polynomial worst-case circuit-size lower bounds in an intuitionistic bounded-arithmetic theory, showing that even statements close to ordinary fixed-polynomial lower bounds can be outside certain feasible proof frameworks.
  Verifiable identifier: DOI `10.46298/lmcs-21(3:26)2025`; arXiv `2404.11841`; LMCS page `https://lmcs.episciences.org/16491`.

## 3. Concrete embedding sketch

**Proposed idea.**  Add a documentation-only audit track, not Lean code in this report, for a bounded-arithmetic/proof-complexity obstruction to provenance filters.  The intended mathematical shape is not "this provenance filter is false."  It is weaker and more meta-level: for a class of provenance-filter validation statements `ValidPF(Π)`, if a weak feasible theory `T` proves `ValidPF(Π)` with the strength needed to exclude hardwired formula families, then standard witnessing/KPT/game extraction should produce an efficient refuter, learner, or Student-Teacher strategy of a kind ruled out by the cited unprovability theorems.

**Existing audit modules it would touch conceptually.**

* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`: the relevant precedent is that an overbroad uniform-provenance condition can reconstruct an already refuted fixed-parameter route.  A bounded-arithmetic audit would ask whether a proposed validation proof for a provenance predicate is so constructive that it yields the same forbidden extractor.
* `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean`: this is the closest concrete analogue because it exhibits a support-cardinality-only filter accepting a log-width hardwiring family.  The bounded-arithmetic version would classify proofs of exclusion of such families by their extractable witnesses.
* `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean`: this is the decisive stress test, because arbitrary all-essential log-width truth-table payloads prevent a mere support-cardinality proof from being meaningful.  Any proposed proof-theoretic obstruction must be checked against this more general payload, not just prefix-AND.
* `pnp3/Barrier/NaturalProofs.lean`: the cited Müller-Pich and Pich-Santhanam work suggests that a feasible-proof obstruction is best represented as a fourth barrier-style interface adjacent to natural proofs, not as a mathematical lower-bound route.

**Suggested new `def` / `Prop` shape, if a later approved implementation were opened.**

No Lean is added here.  A later audit-only design could introduce a proposition with a name such as `ProvablyValidInFeasibleTheory T FilterClass`, meaning: every proof in theory `T` of the filter's validation statement has a bounded witnessing extraction of a specified kind.  A companion obstruction proposition could be named `WitnessingExtractionContradictsLogWidthPayload`, meaning: the extracted learner/refuter/Student-Teacher strategy would solve the arbitrary log-width payload family excluded by NOGO-000006.  The important feature is that this is a proof-system limitation predicate, not a lower-bound assertion and not a bridge to `PpolyDAG`.

**Could it be formalized in months, not years?**

Only a very weak interface could be formalized in months.  The following are plausible within months: definitions of an abstract feasible theory, a proof-validation predicate, an abstract extraction contract, and a theorem saying that if the extraction contract exists then a named hardwiring audit obstruction is triggered.  Formalizing the actual bounded-arithmetic metatheorems of KPT witnessing, `APC_1`, or `S^1_2` inside Lean would be a multi-year effort and is not recommended as a first move.

**Minimal first Lean theorem for viability, for a later separate effort.**

A minimal first theorem would be an abstract implication only: from an assumed extraction contract for `ValidPF(Π)` derive that the extracted procedure distinguishes or rejects an arbitrary all-essential log-width truth-table payload.  This theorem would intentionally import no real bounded arithmetic at first; it would test whether the repo's audit vocabulary can even express the required witness-extraction consequence without smuggling in a support-cardinality-only assumption.

## 4. Self-attack against existing NoGos

**NOGO-000001 — fixed-parameter route plus overbroad uniform provenance.**  The idea does not directly fall to this NoGo because it is not proposing a stronger uniform provenance predicate.  It is a meta-audit asking whether proofs of such predicates in weak theories are too constructive.  However, NOGO-000001 is a serious warning: if the proposed bounded-arithmetic statement is instantiated with a validation principle that implies overbroad uniform provenance, then the report's idea becomes irrelevant because the object-level filter is already dead by hardwiring.  Therefore the proof-theoretic obstruction can only be useful as a negative screen on proposed filters, not as a way to rehabilitate an overbroad one.

**NOGO-000004 — log-width prefix-AND hardwiring against support-cardinality diversity.**  The idea does not directly fall to this NoGo, because it does not classify filters by the support-cardinality function alone.  In fact, NOGO-000004 is one of the test cases the proof-theoretic screen would have to reproduce: a theory proving validity of a support-cardinality-only provenance filter should yield an extractable check that fails on the prefix-AND log-width family.  If the proposed bounded-arithmetic screen cannot even explain this special case, it should be discarded immediately.

**NOGO-000005 — scope correction: prefix-AND is only a special case.**  The idea survives this scope correction only if it treats NOGO-000004 as a warm-up and not as the target.  A report or later audit that says "proof-theoretic independence blocks the prefix-AND issue" would be overclaiming.  The meaningful target is whether feasible proofs of provenance-filter validity imply extractors robust enough to confront arbitrary all-essential payloads, which is exactly the gap NOGO-000005 points toward.

**NOGO-000006 — arbitrary all-essential log-width truth-table payload hardwiring.**  This is the main reason for the `interesting_but_blocked` verdict.  The cited literature shows real unprovability phenomena for circuit lower-bound statements and proof-complexity lower-bound statements, but it does not by itself imply that validation statements for this repo's formula-provenance filters are unprovable.  To avoid NOGO-000006, a proof-theoretic screen must use the full arbitrary-payload family as its witness-extraction adversary.  At present the embedding sketch has no verified theorem showing that a proof of `ValidPF(Π)` would extract a learner/refuter contradicted by the arbitrary-payload construction.  Thus NOGO-000006 does not kill the idea as a literature archive item, but it blocks any claim that it is a working filter design principle.

## 5. Self-attack against classical barriers

**Relativization.**  The proposed idea is not a relativizing lower-bound proof.  It is a metamathematical statement about what weak theories or propositional proof systems can prove, using proof extraction and witnessing.  Still, if translated into the existing barrier interface as a statement scheme over oracles, it would likely not be oracle-invariant: proof systems and bounded-arithmetic theories can encode specific feasible functions, and the witnessing consequences depend on those encodings.  Therefore the relativization interface does not kill it, but a later formal version would need an explicit non-relativizing/bypass witness if someone tried to use it as more than an audit screen.

**Natural Proofs.**  This idea is closest to the natural-proofs barrier, and part of the cited literature explicitly connects feasible proofs of lower bounds with natural-proofs-style obstructions.  The idea should therefore be treated as barrier-aware rather than barrier-bypassing.  It does not assert a large constructive useful property against `P/poly`; instead it asks whether the existence of a feasible proof of a provenance-filter validation principle would itself be too constructive.  If a later version tried to extract a large, decidable property of hard truth tables from the validation principle, it would satisfy the natural-proofs danger pattern and should be rejected unless it also proves a standard cryptographic/non-largeness escape.

**Algebrization.**  The cited bounded-arithmetic results are not algebraic-oracle lower-bound proofs, so the current repo's algebrization interface does not directly apply.  However, proof-complexity lower bounds often interact with algebraic proof systems, polynomial identity testing, and IPS-style systems.  A later implementation must avoid claiming that proof-system unprovability alone bypasses algebrization; at most it supplies a separate metatheoretic obstruction.  If the proposed extraction theorem relativized to algebraic oracles, the algebrization barrier would remain a live objection.

## 6. Verdict

`interesting_but_blocked`

**Reason.**  The literature is real and highly relevant as a possible fourth barrier-style audit: feasible proof systems and bounded-arithmetic theories demonstrably fail to prove several strong complexity lower-bound statements, and these failures are mediated by witnessing, learning, and Student-Teacher extraction phenomena.  But the embedding into this repository is not yet strong enough.  The missing step is a precise theorem connecting a proof of validity for a concrete provenance-filter class to an extracted procedure contradicted by NOGO-000006's arbitrary all-essential log-width truth-table payload.  Without that step, the idea is useful only as a warning label and as a possible design constraint for future audit interfaces.

**Top 3 references for follow-up reading.**

1. Pich and Santhanam, "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly," STOC 2021.
2. Li and Oliveira, "Unprovability of Strong Complexity Lower Bounds in Bounded Arithmetic," STOC 2023.
3. Müller and Pich, "Feasibly constructive proofs of succinct weak circuit lower bounds," APAL 2020.

**Why not killed by NOGO-000006.**  It is not a support-cardinality filter and does not claim to exclude the arbitrary-payload family.  It is a meta-level proof-audit proposal whose first serious test would be to derive an extraction consequence that fails on that family.  Since this consequence is not yet proved, NOGO-000006 blocks promotion but does not make the literature report false.

**Recommended next move.**  Archive as `interesting_but_blocked`; if revisited, run a tiny paper-design pass whose only goal is to state the exact extraction contract from "feasible proof of provenance-filter validity" to "procedure refuted by arbitrary log-width payload."  Do not implement bounded arithmetic itself before that contract is written and reviewed.

**Scope violations.**  None intended: this report adds no Lean code, edits no JSONL ledger, touches no trust root, creates no lower-bound route, and makes no unconditional P-vs-NP claim.
