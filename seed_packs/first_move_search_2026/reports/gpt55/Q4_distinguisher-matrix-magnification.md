# §1. Question

**Question:** Q4 — magnification follow-ups post-Oliveira-Pich-Santhanam 2019+

**Handle:** gpt55

**Report path:** `seed_packs/first_move_search_2026/reports/gpt55/Q4_distinguisher-matrix-magnification.md`

**Chosen Q, verbatim:** **Q4** — magnification follow-ups (post-Oliveira-Pich-Santhanam 2019+).

**Scope classification:** Infrastructure / literature scan only.  This report proposes no code, no trust-root change, no promoted route, and no endpoint claim.

# §2. Cited results

Top references:

* Albert Atserias and Moritz Müller, "Simple general magnification of circuit lower bounds," 2025, arXiv preprint.
  * Summary: Introduces sparse matrix "distinguishers" that retain code-like distance properties and yield general magnification theorems, including fixed-polynomial formula lower bounds from slightly superlinear formula lower bounds for approximating sparse NP problems, plus a uniform MCSP magnification statement that the authors say appears to sidestep the localization barrier.
  * Verifiable identifier: arXiv:2503.24061, https://arxiv.org/abs/2503.24061.

* Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Ján Pich, Ninad Rajgopal, and Rahul Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality," ITCS 2020.
  * Summary: Studies whether magnification avoids the natural-proofs barrier, proves that some MCSP-based magnification instances would rule out natural proofs, and identifies a locality barrier explaining why known lower-bound methods do not combine directly with magnification.
  * Verifiable identifier: DOI 10.4230/LIPIcs.ITCS.2020.70; arXiv:1911.08297, https://arxiv.org/abs/1911.08297.

* Igor C. Oliveira, Ján Pich, and Rahul Santhanam, "Hardness Magnification Near State-of-the-Art Lower Bounds," Theory of Computing 17(11), 2021; special issue for CCC 2019.
  * Summary: Develops Gap-MCSP/Gap-MKtP magnification near known lower-bound frontiers, including an NP lower-bound implication from weak Gap-MCSP circuit lower bounds and discussion of why model-specific thresholds matter.
  * Verifiable identifier: Theory of Computing 17(11), 2021, https://theoryofcomputing.org/articles/v017a011/.

* Lijie Chen, Ce Jin, and R. Ryan Williams, "Hardness Magnification for all Sparse NP Languages," FOCS 2019.
  * Summary: Shows that the sparsity feature of MCSP/MKtP variants is enough to support broad magnification statements for all sufficiently sparse NP languages, shifting attention from meta-complexity specificity to sparse-language structure.
  * Verifiable identifier: DOI 10.1109/FOCS.2019.00077; ECCC TR19-118, https://eccc.weizmann.ac.il/report/2019/118/.

* Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, and Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP," STACS 2021; journal version Theory of Computing Systems 68(4), 2024.
  * Summary: Gives non-trivial lower bounds for MCSP/MKTP against one-tape Turing machines and nondeterministic/parity branching programs, nearly matching best known explicit-function lower bounds in those models and locating concrete restricted-model progress around magnification thresholds.
  * Verifiable identifier: DOI 10.4230/LIPIcs.STACS.2021.23; journal DOI 10.1007/s00224-022-10113-9, https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2021.23.

# §3. Concrete embedding sketch

Recommended embedding target: a **distinguisher-matrix audit route** inspired primarily by Atserias--Müller, with Chen--Hirahara--Oliveira--Pich--Rajgopal--Santhanam used as the barrier checklist.

The key move is to avoid a provenance predicate that only inspects the number of input coordinates touched by a formula family.  Instead, the audit object should be a small structured matrix `D` together with two semantic contracts:

1. **Sparse computability of fingerprints:** each output bit of the fingerprint map `x ↦ xD` depends on few coordinates and is itself computed by a restricted formula/circuit of controlled size;
2. **Distance/separation preservation:** for the relevant sparse language or promise problem, the fingerprints of positive objects remain separated from far negative objects with the parameters required by the magnification theorem.

Existing audit modules touched: conceptually, the route would sit next to `pnp3/Magnification/AuditRoutes/` because it is an audit-route shape; it should read the hardwiring lessons from `FixedParamsProbe`, `LogWidthAdversary`, and `ArbitraryLogWidthTT` but not edit them in this report.  Classical-barrier documentation in `pnp3/Barrier/Relativization.lean`, `pnp3/Barrier/NaturalProofs.lean`, and `pnp3/Barrier/Algebrization.lean` supplies the explicit self-attack interface.

New predicates suggested for a future audit route, in prose only:

* `SparseDistinguisherMatrix`: matrix has bounded row/column support, constructible indexing, and controlled fingerprint output length;
* `FingerprintSeparation`: the matrix separates the sparse YES set from strings far from that set at the approximation radius used by the magnification theorem;
* `FingerprintFormulaCost`: the fingerprint bits compose with the target weak model within the needed near-threshold size bound;
* `NonLocalPayloadGuard`: the acceptance condition is not invariant under replacing a small support window by an arbitrary all-essential truth-table formula; it must mention the global fingerprint/separation contract, not only support size.

Could it be formalised in months?  A small audit skeleton could plausibly be formalised in months if it restricts itself to finite Boolean matrices, Hamming distance, support of rows, and a toy fingerprint-separation lemma.  Fully formalising Atserias--Müller magnification would be years, not months.  The viable first milestone is only an anti-hardwiring audit: prove that arbitrary log-width truth-table payloads do not automatically satisfy the proposed `FingerprintSeparation` predicate unless they also meet a genuine code-like separation hypothesis.

Minimal first theorem for viability, in prose: for any family obtained by injecting an arbitrary all-essential log-width truth-table payload into `n` variables by renaming, bounded support cardinality alone is insufficient to produce the global fingerprint-separation contract.  Equivalently, `AllEssentialPayload + sublinear renamed support` should not imply `FingerprintSeparation` without an explicit matrix/separation witness.  This would demonstrate that the predicate is not merely the old support-cardinality filter in disguise.

# §4. Self-attack against existing NoGos

## NOGO-000001

Does the proposed idea fall to this NoGo?  **Probably no, if kept as a matrix/separation contract; yes, if weakened to uniform fixed-parameter provenance.**

NOGO-000001 kills any route that pairs a fixed-parameter route with overbroad uniform provenance and thereby reconstructs the previously refuted formula-support restriction route.  A distinguisher-matrix route should not assert that every formula satisfying broad uniformity automatically has the desired property.  It should require a concrete fingerprinting object plus a semantic Hamming-distance separation statement.  However, if the future design hid the matrix and only said that small local probes certify the route uniformly, it would risk reintroducing the same overbroad implication.  The safe rule is: do not let fixed local probes imply the audit predicate without the global separation contract.

## NOGO-000004

Does the proposed idea fall to this NoGo?  **No for the proposed route; yes for the sparse-language reference if used naively.**

NOGO-000004 shows that a pure syntactic support-cardinality filter admits the prefix-AND family on a logarithmic window: the support size is unbounded but sublinear, exactly satisfying the old diversity condition.  A matrix/fingerprint route is not supposed to accept a family because its support size has that shape.  It should ask whether the induced fingerprints separate sparse positives from far negatives at the theorem's approximation radius.  Prefix-AND on a log window provides no such global separation by itself.  The caution is that Chen--Jin--Williams sparsity, by itself, is too close to a cardinality-only story; sparsity should be treated as background motivation, not as the full audit predicate.

## NOGO-000005

Does the proposed idea fall to this NoGo?  **No, provided the report's scope correction is enforced.**

NOGO-000005 corrected the earlier overclaim: the formal artefact at that stage killed the prefix-AND specialization, not arbitrary all-essential truth-table payloads.  This report deliberately does not use the prefix-AND special case as evidence that arbitrary payloads are excluded.  The proposed first theorem is exactly the inverse sanity check: show that the future predicate has an additional separation requirement that arbitrary renamed log-width payloads do not get for free.  Therefore the route respects the scope correction instead of relying on the narrowed prefix-AND proof.

## NOGO-000006

Does the proposed idea fall to this NoGo?  **Not automatically; this is the central reason to prefer the distinguisher route.**

NOGO-000006 formalizes the arbitrary all-essential log-width truth-table payload obstruction: any filter that only measures support cardinality cannot distinguish benign prefix-AND from arbitrary all-essential log-width truth tables.  The proposed matrix route is meant to fail closed against this attack.  An arbitrary payload can be embedded into a log-width window and can satisfy all-essentialness, but it does not thereby provide a sparse matrix with code-like separation, nor does it show that fingerprint composition stays within the needed model threshold.  If a future predicate accepts arbitrary payloads merely because the payload support is logarithmic and all-essential, then it has collapsed back into the dead support-cardinality design.  The next audit must explicitly test that collapse.

# §5. Self-attack against classical barriers

## Relativization

Does the proposed idea satisfy the barrier's hypothesis?  **Unclear; assume risk until a non-relativizing ingredient is isolated.**

The repo's relativization interface treats a statement scheme as relativizing when it is oracle-invariant.  A finite-matrix fingerprint statement can be written in a way that is purely combinatorial and may therefore look oracle-insensitive.  That is dangerous: if the whole embedding is just a relativizing sparse-language argument, it should not be advertised as a robust path around classical barriers.  The possible non-relativizing ingredient is the MCSP/meta-complexity component: truth-table complexity and succinct-vs-explicit encodings often depend on representation details not captured by an arbitrary oracle-invariant scheme.  A follow-up must state exactly which component fails oracle invariance before claiming a relativization bypass.

## Natural Proofs

Does the proposed idea satisfy the barrier's hypothesis?  **The underlying magnification literature is designed to avoid the standard natural-proofs trap, but the future predicate must avoid largeness.**

Chen--Hirahara--Oliveira--Pich--Rajgopal--Santhanam explicitly analyze this question and show that some MCSP magnification instances would rule out natural proofs rather than instantiate them.  The distinguisher-matrix route is consistent with that lesson only if `FingerprintSeparation` is not a large, constructive, useful property of Boolean functions in the Razborov--Rudich sense.  Since the predicate quantifies over structured sparse matrices and a sparse/promise target, it is plausibly not large over all truth tables.  But a careless reformulation as "many functions fail small fingerprints" could become large and constructive.  Thus the route is barrier-aware but not automatically safe.

## Algebrization

Does the proposed idea satisfy the barrier's hypothesis?  **Unclear; no bypass should be claimed.**

The repo's algebrization interface mirrors oracle-family invariance under algebraic oracle changes.  The proposed finite Hamming-metric/matrix audit does not obviously use low-degree extensions or algebraic oracle machinery, so it neither clearly satisfies nor clearly violates the barrier's hypothesis.  That means the honest classification is neutral: this route may help avoid support-cardinality hardwiring, but it does not currently provide an algebrization self-defense.  A follow-up should include a toy oracle-family parameter and check whether fingerprint separation survives algebraic-oracle substitutions.

# §6. Verdict

**Verdict:** `survivor`.

Reason: Atserias--Müller's distinguisher-matrix approach is the strongest follow-up found for this specific prompt because it suggests a concrete audit predicate that is not support-cardinality-only and is not automatically satisfied by arbitrary log-width truth-table payloads.  The route is still far from a lower-bound endpoint, and it must not be advertised as mainline progress.  Its value is narrower but real: it gives a crisp next audit object, `matrix + fingerprint separation`, whose first job is to resist NOGO-000001 and NOGO-000006.

Recommended next move: create a documentation-only or audit-skeleton seed pack for `distinguisher-matrix-provenance`, with the first deliverable being a no-collapse lemma against renamed arbitrary log-width payloads.  Do not attempt to formalise the full 2025 magnification theorem in the first pass.

Scope violations: none.  This report contains no Lean code, no JSONL edits, no trust-root edits, no promoted theorem surface, no endpoint claim, and no unconditional separation claim.

# §7. Follow-up seed pack outline

* Proposed seed pack id: `fp3b5_distinguisher_matrix_provenance`.

* Goal: Test whether sparse distinguisher matrices and fingerprint-separation predicates can serve as a provenance/audit shape that avoids the support-cardinality hardwiring failures while remaining close enough to post-2019 hardness magnification to be mathematically meaningful.  The seed pack should formalise only the audit interface and anti-collapse checks, not the full magnification theorem.

* Suggested slot decomposition:
  1. **D1 — finite matrix primitives:** define Boolean matrices, row support, column support, Hamming distance, and fingerprint map in an isolated audit namespace.
  2. **D2 — toy sparse-language separation:** specify and prove a small finite theorem showing that separation is a semantic condition, not a consequence of support cardinality.
  3. **D3 — log-width payload anti-collapse:** show that renamed arbitrary all-essential log-width payloads do not imply fingerprint separation without an explicit matrix witness.
  4. **D4 — barrier checklist:** add documentation mapping the toy route to relativization, natural-proofs, and algebrization predicates.
  5. **D5 — literature-to-parameter table:** record which parameters are copied from Atserias--Müller and which are deliberately omitted from the first audit.

* Inherited forbidden scope from this seed pack: no Lean code in this report; no trust-root edits; no JSONL ledger edits; no promotion to accepted route; no creation of proposed-package directories; no endpoint claim; no unconditional separation claim.  A future seed pack must continue to distinguish side-track/audit progress from mainline lower-bound progress unless it explicitly reduces one of the repository's main source obligations.
