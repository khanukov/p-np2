# D5 literature-to-parameter table — gpt55

Slot: D5  
Handle: gpt55  
Scope classification: Infrastructure / literature documentation only.  
Outcome target: markdown report only; no Lean, no JSONL/spec/trust-root edits, no `SourceTheorem_*`, no `gap_from_*`, no final endpoint, no `ProvenanceFilter_v1` promotion.

## 1. Executive summary

This report records a conservative parameter map from the post-2019 hardness-magnification literature into the fp3b6 audit skeleton for sparse distinguisher matrices and fingerprint-separation predicates.  It is intentionally not a proof plan for a lower-bound endpoint.  Its only deliverable is a verified-literature table that future D1/D2/D3/D4 workers can use without re-resolving bibliographic identifiers.

The audit skeleton has four parameter families:

1. **Matrix sparsity**: row support and column support bounded by a generic `k`.
2. **Fingerprint length**: output length `m` for a map from `n` input coordinates to `m` fingerprint coordinates.
3. **Separation / approximation radius**: a radius or gap parameter distinguishing accepted objects from far objects.
4. **Composition cost**: the cost of composing the fingerprint with the weak model at the relevant near-threshold regime.

The table below treats Atserias--Müller 2025 as the only directly matrix-shaped source for D5.  The other four papers are included because the seed pack and Q4 report cite them as magnification/barrier context: they supply gap parameters, sparsity parameters, model thresholds, locality-barrier warnings, and restricted-model MCSP lower-bound thresholds, but they do not directly define the fp3b6 matrix predicate.  Where a mapping would require reading unverified theorem-level constants beyond the resolved bibliographic pages and abstracts, it is marked `[unverified]` rather than inferred.

Practical recommendation: the first audit pass should copy only **generic shape constraints** (`k`, `m`, radius/gap symbols, and weak-model cost placeholders) and should deliberately omit theorem-tight constants.  This keeps D3 focused on the NOGO-000006 anti-collapse question: an all-essential log-width truth-table payload should not be accepted merely because its support window is small; an explicit semantic matrix/fingerprint witness is required.

## 2. Parameter dictionary

| Audit parameter | Intended meaning in fp3b6 | Literature analogue | First-pass status | Risk note |
| --- | --- | --- | --- | --- |
| `n` | Ambient number of Boolean input coordinates to the audit witness/fingerprint map. | Truth-table input sizes are often written as `N = 2^n` in MCSP/MKtP papers; sparse-language papers also use input length and sparsity-growth parameters. | Copy as a local finite dimension only. | Name collision risk: some papers use `n` for log truth-table length and `N` for truth-table length. |
| `m` | Number of fingerprint output bits / number of matrix rows. | Atserias--Müller use sparse matrix distinguishers; output length corresponds to the number of measurements/fingerprint coordinates. | Copy only as a generic bound. | Exact theorem-level `m(n)` choices are `[unverified]` here. |
| `k_row` | Maximum row support of the Boolean matrix. | Sparse-matrix row sparsity in Atserias--Müller; local oracle/query fan-in in locality-barrier language. | Copy as generic `≤ k`. | Do not equate row support with formula support cardinality; NOGO-000007 forbids support-cardinality-only acceptance. |
| `k_col` | Maximum column support of the Boolean matrix. | Sparse-matrix column sparsity in Atserias--Müller; load/regularity side of code-like sparse matrices. | Copy as generic `≤ k`. | Column support is not supplied by older MCSP magnification papers in this matrix form. |
| `fp_D(x)` | Fingerprint of an object `x` under matrix/witness `D`. | Atserias--Müller distinguishers preserve code-like distance information. | Copy as an abstract semantic map. | The exact algebraic convention for multiplying by the matrix is not fixed in this markdown report. |
| `r` | Hamming-distance or promise radius separating positives from far negatives. | Gap-MCSP/Gap-MKtP use two thresholds `s_1, s_2`; sparse-language magnification uses sparsity/distance-to-language style promises; matrix distinguishers retain distance properties. | Keep symbolic. | Mixing Hamming distance between truth tables with circuit-size gaps is a parameter-risk hotspot. |
| `δ` or `Δ` | Distance-preservation loss / minimum fingerprint separation. | Code-like distance preservation in Atserias--Müller; promise gaps in OPS; approximation/far-from-language parameters in general magnification. | Keep symbolic. | Exact constants are `[unverified]` and should not be baked into Lean. |
| `C_fp` | Cost to compute fingerprint bits in the target weak model. | Formula/circuit thresholds in OPS and CJW; restricted models in CHMY. | Keep as a predicate, not a numeric theorem. | The audit route must not claim the full magnification theorem. |
| `s_1(N), s_2(N)` | Small-vs-large complexity thresholds for gap meta-complexity problems. | OPS explicitly states Gap-MCSP / Gap-MKtP thresholds `s_1(N), s_2(N)`. | Reference only; not copied into D1/D3. | First pass deliberately avoids concrete promise problems. |
| `β, ε, c` | Magnification constants / exponent slack. | OPS page states a universal constant `c`, small `β`, and `ε > 0` in its theorem summary; CJW and CHMY use analogous weak-lower-bound constants. | Documented but omitted from skeleton. | These constants are not needed for anti-collapse. |
| sparse language density | Number of positive instances as a function of length. | CJW focuses on all sparse NP languages; Atserias--Müller discusses sufficiently sparse NP problems. | Used only as motivation. | Not equivalent to matrix row/column sparsity. |
| locality | Small fan-in oracle-query locality in magnification proofs. | CHOPRS identify a locality barrier. | Barrier note only. | Do not mistake locality-barrier oracle gates for fp3b6 matrix rows. |

## 3. Per-paper mapping table

| Paper | Cited parameters | Mapping to audit skeleton | Copied vs omitted | Reason |
| --- | --- | --- | --- | --- |
| Albert Atserias and Moritz Müller, **"Simple general magnification of circuit lower bounds"**, arXiv:2503.24061, 2025. | Verified bibliographic page says the method uses **distinguishers**, described as sparse matrices retaining some code-like error-correcting-code properties, and gives applications to general magnification, formula lower bounds for approximating sufficiently sparse NP problems, sharp thresholds, and uniform MCSP magnification. Exact row/column support functions, output length, and distance-loss constants: `[unverified]` in this report. | Direct source for `SparseDistinguisherMatrix`, `fingerprint`, and a semantic `FingerprintSeparation` predicate. `k_row`, `k_col`, `m`, `r`, and distance-preservation bounds should be represented symbolically. | **Copied:** sparse matrix / distinguisher shape; generic code-like distance-preservation intent; sufficiently sparse problem motivation. **Omitted:** exact theorem constants, construction details, sharp-threshold claims, and uniform MCSP theorem statement. | This is the only D5 source whose verified abstract directly mentions sparse matrices as distinguishers. The fp3b6 first pass is an audit skeleton, not a full formalization of the 2025 magnification theorem. |
| Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Ján Pich, Ninad Rajgopal, and Rahul Santhanam, **"Beyond Natural Proofs: Hardness Magnification and Locality"**, ITCS 2020; arXiv:1911.08297; DOI 10.4230/LIPIcs.ITCS.2020.70. | Verified Dagstuhl page gives ITCS 2020, LIPIcs 151, article 70, pages 70:1--70:48, and keywords including hardness magnification, natural proofs, MCSP, and circuit lower bounds. Its abstract frames the **locality barrier**: target problems admit efficient circuits with small fan-in oracle gates, while lower-bound methods often extend to such oracle-augmented circuits. Concrete oracle fan-ins and theorem constants: `[unverified]` here. | Maps to D5's **barrier-notes layer**, not to the matrix primitive. Locality warns that `k_row`/small local dependence cannot by itself be advertised as barrier-safe. Natural-proofs discussion warns against turning fingerprint separation into a large constructive property. | **Copied:** locality-barrier checklist role; natural-proofs caution; MCSP/magnification context. **Omitted:** theorem-specific oracle locality parameters, naturalizability theorem statements, and any claim that fp3b6 bypasses the barrier. | D5 is not D4, but D5 must explain why parameter choices should remain semantic and non-promotional. This paper is the main verified source for the locality-barrier warning inherited by the seed pack. |
| Igor C. Oliveira, Ján Pich, and Rahul Santhanam, **"Hardness Magnification Near State-of-the-Art Lower Bounds"**, Theory of Computing 17(11), 2021. | Verified ToC page gives volume 17, article 11, pages 1--38, published November 30, 2021, DOI 10.4086/toc.2021.v017a011. Its abstract states gap versions of MKtP/MCSP with thresholds `s_1(N), s_2(N)` and `N = 2^n`, and lists sample theorem thresholds involving `GapMCSP[2^{β n}/cn, 2^{β n}]`, `GapMKtP[2^{β n}, 2^{β n}+cn]`, circuit/formula/branching-program sizes, `ε > 0`, and a universal constant `c`. | Provides the **gap/radius dictionary**: fp3b6's `r` / `δ` placeholders correspond to promise separation rather than merely support size. Provides weak-model cost placeholders for `FingerprintFormulaCost`. | **Copied:** symbolic gap-threshold notation; warning that model-specific thresholds matter. **Omitted:** exact constants, theorem conclusions, concrete Gap-MCSP/Gap-MKtP target formalization, and any endpoint implication. | OPS supplies the most explicit verified parameter notation among the sources, but importing those exact thresholds would exceed the audit skeleton and risk accidental endpoint language. |
| Lijie Chen, Ce Jin, and R. Ryan Williams, **"Hardness Magnification for all Sparse NP Languages"**, FOCS 2019; DOI 10.1109/FOCS.2019.00077; ECCC TR19-118. | Verified sources give FOCS 2019, pages 1240--1255, authors Chen/Jin/Williams, and the title. Search snippets and the ECCC page identify the sparse-NP-language focus. Detailed sparsity exponents and all theorem thresholds: `[unverified]` here. | Provides the **sparse-language** motivation for treating the target family abstractly rather than hardwiring MCSP-specific syntax. It maps to a generic `SparseTarget`/YES-set parameter in future prose, not to `SparseDistinguisherMatrix` row support. | **Copied:** all-sparse-NP-language perspective; sparse target motivation. **Omitted:** exact sparsity rate, exponent thresholds, search-MCSP/search-MKtP variants, and theorem consequences. | The audit report must avoid conflating language sparsity with matrix sparsity. CJW supports keeping target sparsity as a separate parameter from `k_row`/`k_col`. |
| Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, and Yuichi Yoshida, **"One-Tape Turing Machine and Branching Program Lower Bounds for MCSP"**, STACS 2021; DOI 10.4230/LIPIcs.STACS.2021.23; journal DOI 10.1007/s00224-022-10113-9. | Verified Dagstuhl page gives STACS 2021, LIPIcs 187, article 23, pages 23:1--23:19, and keywords including MCSP, Kolmogorov complexity, one-tape Turing machines, branching programs, lower bounds, PRGs, and hitting set generators. Verified abstract states `MCSP[s(n)]`, inputs of length `N := 2^n`, and restricted-model lower bounds around one-tape Turing machines and branching programs. The verified Dagstuhl abstract includes displayed thresholds: a randomized two-sided-error one-tape Turing machine with an additional one-way read-only input tape cannot compute `MCSP[2^{μ₂·n}]` in time `N^{1.99}` for some `μ₂ > μ₁`; a nondeterministic or parity branching program of size `o(N^{1.5}/log N)` cannot compute MKTP; and nondeterministic/co-nondeterministic/parity branching programs for MCSP have size at least `N^{1.5-o(1)}`. The journal DOI 10.1007/s00224-022-10113-9 is verified by DBLP/ResearchGate search metadata, with Theory of Computing Systems 68(4):868--899 (2024) in DBLP. | Provides **restricted-model cost context** for `FingerprintFormulaCost` and barrier realism: weak models differ, and lower bounds near magnification thresholds can be model-specific. It does not supply a matrix fingerprint parameter. | **Copied:** notation `MCSP[s(n)]`, `N = 2^n`, restricted-model vocabulary. **Omitted:** local PRG construction details, hitting-set generator seed length, one-tape/branching-program theorem constants, and any use as endpoint progress. | CHMY is useful context but remains a restricted lower-bound side track for fp3b6 unless a separate bridge is supplied. D5 therefore records it as parameter context only. |


### Per-source parameter extraction notes

#### Atserias--Müller 2025

* Bibliographic identity: verified.
* Direct matrix relevance: high.
* Parameter names to copy into audit prose: `k_row`, `k_col`, `m`, `r`, `δ`.
* Parameter values to copy into Lean now: none.
* Why no exact values: D5 checked the public arXiv metadata/abstract, not theorem internals.
* Safe claim: sparse matrix distinguishers are the inspiration for the fp3b6 matrix/fingerprint object.
* Unsafe claim: any concrete fp3b6 `k` or `m` equals the paper's optimal threshold.
* Follow-up needed for exact constants: theorem-by-theorem extraction from arXiv v2.

#### Chen--Hirahara--Oliveira--Pich--Rajgopal--Santhanam ITCS 2020

* Bibliographic identity: verified.
* Direct matrix relevance: indirect.
* Barrier relevance: high.
* Parameter names to copy into audit prose: locality/fan-in placeholders only.
* Parameter values to copy into Lean now: none.
* Safe claim: locality is a barrier that a small-support audit predicate must explicitly address.
* Unsafe claim: fp3b6 already avoids locality or natural-proofs barriers.
* Follow-up needed: D4 should cite theorem-level locality statements if it uses exact fan-in.

#### Oliveira--Pich--Santhanam ToC 2021

* Bibliographic identity: verified.
* Direct matrix relevance: indirect.
* Gap-parameter relevance: high.
* Parameter names to copy into audit prose: `s_1(N)`, `s_2(N)`, `N = 2^n`, `β`, `ε`, `c`.
* Parameter values to copy into Lean now: none.
* Safe claim: gap thresholds motivate a symbolic separation radius in `FingerprintSeparation`.
* Unsafe claim: D1/D3 formalizes Gap-MCSP or Gap-MKtP.
* Follow-up needed: only a later target-specific seed pack should formalize concrete promise problems.

#### Chen--Jin--Williams FOCS 2019

* Bibliographic identity: verified.
* Direct matrix relevance: indirect.
* Sparse-language relevance: high.
* Parameter names to copy into audit prose: sparse target density / YES-set size placeholders.
* Parameter values to copy into Lean now: none.
* Safe claim: sparse-language magnification motivates keeping the target abstract.
* Unsafe claim: language sparsity is the same as matrix row or column sparsity.
* Follow-up needed: theorem-level extraction if a later audit needs exact density rates.

#### Cheraghchi--Hirahara--Myrisiotis--Yoshida STACS 2021 / journal version

* Bibliographic identity: verified.
* Direct matrix relevance: low.
* Restricted-model relevance: medium.
* Parameter names to copy into audit prose: `MCSP[s(n)]`, `N = 2^n`, one-tape time, branching-program size, PRG seed length.
* Parameter values to copy into Lean now: none.
* Safe claim: model-specific restricted lower bounds provide context for `FingerprintFormulaCost`.
* Unsafe claim: these restricted lower bounds are fp3b6 mainline progress or a matrix witness.
* Follow-up needed: only if D4 discusses local-PRG side-track barriers.

## 4. Deliberate omissions

The first audit pass deliberately does **not** formalize or commit to the following items.

1. **Full Atserias--Müller magnification theorem.**  The Q4 report and fp3b6 README frame full formalization as far beyond this seed pack.  D5 records only the matrix/fingerprint parameter surface.
2. **Exact row/column support functions from Atserias--Müller.**  The verified public abstract establishes sparse matrices and code-like distance behavior, but D5 has not verified theorem-level bounds.  They remain `[unverified]`.
3. **Exact fingerprint output length `m(n)`.**  The audit skeleton needs a finite codomain length; it does not need the sharp magnification value.
4. **Exact distance-preservation constants.**  `FingerprintSeparation` should remain a predicate over symbolic radii/gaps until a later theorem-specific formalization.
5. **Concrete MCSP / Gap-MKtP target promise problem.**  OPS provides verified gap notation, but fp3b6's first pass is a provenance audit against hardwiring collapse, not a formal MCSP package.
6. **Search-MCSP / search-MKtP variants.**  They are mentioned in the literature context but are not part of D5's parameter skeleton.
7. **Distribution-specific average-case statements.**  No distributional assumption is needed for D3 anti-collapse.
8. **Theorem endpoint implications.**  This document does not claim any unconditional complexity separation or accepted route promotion.
9. **Local PRG and hitting-set internals from CHMY.**  Those are restricted-model lower-bound ingredients and would distract from the semantic matrix witness required by fp3b6.
10. **Natural-proofs / algebrization certificates.**  D5 notes risks; D4 is the dedicated barrier-checklist slot.

## 5. NOGO interaction

The table is shaped by four existing NoGoLog entries.

| NOGO | Constraint imported into D5 | Parameter consequence |
| --- | --- | --- |
| NOGO-000006 | Arbitrary all-essential log-width truth-table payload hardwiring can satisfy a support-cardinality filter. | Do not allow `k = O(log n)` or all-essentialness alone to imply `FingerprintSeparation`. Require an explicit matrix/fingerprint witness. |
| NOGO-000007 | Support-cardinality-only provenance filters admit hardwiring twins with the same support profile. | Keep `k_row`/`k_col` as necessary but not sufficient. The semantic separation predicate is load-bearing. |
| NOGO-000008 | Purely syntactic filters are vulnerable to tautological-seed rewrites. | The table prefers semantic Boolean-function/fingerprint parameters over displayed gate-count parameters. |
| NOGO-000009 | Structural-normalization patches can destroy the filter's own non-vacuity witness. | Do not propose normalization as the missing parameter. The route should operate on matrix/fingerprint semantics instead. |

The immediate D3-facing consequence is narrow: the anti-collapse theorem should refute the implication from arbitrary all-essential log-width payload plus small support to fingerprint separation **without** an explicit matrix witness.  It should not try to prove that every payload lacks every possible separating matrix; trivial or specially structured payloads may admit trivial witnesses.

## 6. Barrier notes

### Relativization

Status: **risk / neutral**.  Finite Hamming-metric statements can look oracle-insensitive.  The Q4 report flags the MCSP/meta-complexity component as the plausible non-relativizing ingredient, but D5 does not verify a non-relativizing theorem.  Therefore no bypass is claimed.

### Natural proofs

Status: **risk unless non-largeness is maintained**.  CHOPRS is the verified source for treating natural proofs and locality as a serious barrier interface.  A fingerprint predicate that ranges over a sparse/promise target and an explicit matrix witness is plausibly not a large property over all Boolean functions, but this report does not prove that.  A later D4 certificate must prevent reformulating `FingerprintSeparation` as a broad constructive/useful/largeness property.

### Algebrization

Status: **neutral / unverified**.  None of the verified source pages establish an algebrization bypass for the fp3b6 matrix audit skeleton.  Keep all algebrization language out of D1/D3 except as a warning to be handled by D4.

### Locality barrier

Status: **load-bearing warning**.  CHOPRS identify locality as a barrier for direct combinations of known lower-bound methods with magnification.  A small row support `k_row` is not, by itself, a success signal; it can be part of the same locality risk.  The matrix route is only interesting if semantic separation and provenance prevent collapse to the NOGO-000006/000007 hardwiring patterns.

## 7. Recommendation

Proceed with the D1/D2/D3 audit skeleton using **symbolic parameters**:

```text
n              ambient dimension
m              fingerprint length
k_row, k_col   matrix support bounds, usually combined as k in first pass
r              separation / far-negative radius
δ or Δ         distance-preservation slack
C_fp           weak-model composition-cost predicate
```

Do not import exact magnification thresholds into the first Lean interface.  The first-pass table supports a safer design rule: `SparseDistinguisherMatrix` is a structural precondition, while `FingerprintSeparation` is an explicit semantic witness condition.  This separation is essential for resisting NOGO-000006 and NOGO-000007.

Recommended next step for integrators: if a later worker wants theorem-tight parameters from Atserias--Müller, create a separate literature-extraction task that reads the theorem text and records exact row/column support, output length, and distance-loss formulas with page/theorem citations.  Until then, all such constants should remain `[unverified]`.

## 8. Verified references

The following identifiers were resolved and checked against public bibliographic pages during this D5 pass.

| Reference | Verification status | Verified facts | URL |
| --- | --- | --- | --- |
| Albert Atserias and Moritz Müller, "Simple general magnification of circuit lower bounds." | Verified. | arXiv:2503.24061; submitted March 31, 2025; title and authors verified; arXiv DOI 10.48550/arXiv.2503.24061 shown. | <https://arxiv.org/abs/2503.24061> |
| Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Ján Pich, Ninad Rajgopal, and Rahul Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality." | Verified. | ITCS 2020; LIPIcs volume 151; article 70; pages 70:1--70:48; DOI 10.4230/LIPIcs.ITCS.2020.70; arXiv:1911.08297 resolved. | <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2020.70>, <https://arxiv.org/abs/1911.08297> |
| Igor C. Oliveira, Ján Pich, and Rahul Santhanam, "Hardness Magnification Near State-of-the-Art Lower Bounds." | Verified. | Theory of Computing volume 17, article 11, pages 1--38; published November 30, 2021; DOI 10.4086/toc.2021.v017a011; CCC 2019 special issue. | <https://theoryofcomputing.org/articles/v017a011/> |
| Lijie Chen, Ce Jin, and R. Ryan Williams, "Hardness Magnification for all Sparse NP Languages." | Verified. | FOCS 2019; pages 1240--1255; DOI 10.1109/FOCS.2019.00077; ECCC TR19-118; authors/title verified by DBLP/ECCC/search-indexed IEEE PDF. | <https://dblp.org/rec/conf/focs/ChenJW19>, <https://eccc.weizmann.ac.il/report/2019/118/> |
| Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, and Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP." | Verified. | STACS 2021; LIPIcs volume 187; article 23; pages 23:1--23:19; DOI 10.4230/LIPIcs.STACS.2021.23; journal DOI 10.1007/s00224-022-10113-9 listed in the seed prompt and compatible with the journal-version metadata, but the journal page itself was not needed for the first-pass table. | <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2021.23> |


### Verification method notes

* The citation check used resolver-facing pages where available: arXiv for preprints, Dagstuhl/DROPS for LIPIcs papers, Theory of Computing for the ToC article, DBLP/ECCC for the FOCS paper, and DBLP/search metadata for the Springer journal DOI.
* Parameters were copied only when visible on the verified public page or in the page abstract/snippet returned by the resolver.
* Parameters mentioned only in Q4 but not reverified during this pass are not used as exact constants.
* When a paper has both conference and journal/preprint versions, the table records the verified bibliographic identity but does not assume theorem statements are identical across versions.
* Every table row separates bibliographic verification from parameter extraction.  A verified paper identity does not automatically make every parameter mapping verified.
* This is why many entries are marked `[unverified]` even though the corresponding DOI/arXiv identifier is verified.
* No citation in this report is used as evidence for a `PpolyDAG` bridge, a source theorem, or an accepted guard promotion.
* No source is treated as establishing fp3b6 non-vacuity.  Non-vacuity is a future audit obligation, not a D5 literature fact.
* No source is treated as excluding arbitrary truth-table hardwiring by itself.  That exclusion is the future D3 anti-collapse task.
* The parameter dictionary is therefore a conservative vocabulary alignment, not a theorem catalogue.

### Unverified parameter details retained as unverified

* Atserias--Müller exact row-support, column-support, fingerprint-length, and distance-loss formulas: `[unverified]`.
* CHOPRS exact small-fan-in oracle/locality constants: `[unverified]`.
* OPS theorem-level constants beyond the public ToC abstract's displayed examples: `[unverified]`.
* CJW exact sparse-language exponent thresholds and search-problem thresholds: `[unverified]`.
* CHMY one-tape / branching-program headline constants listed in the Dagstuhl abstract are verified as literature facts, but their use as fp3b6 matrix parameters is `[unverified]`; they should remain restricted-model context, not skeleton constants.
