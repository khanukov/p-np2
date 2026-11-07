# Exact proof map and claim boundary

| Layer | Actual contract | Status |
|---|---|---|
| OpenProblem.R | exists fixed k, forall d, no Nonempty BoundedSearchSolver; exact concrete codec, canonical C_DAG and full-table polynomial | UNPROVED research premise |
| R_iff_original | definitional expansion of the accepted treeProblem abbreviation | new independently elaborated equivalence, no new assumption |
| core SingleResearchGap | same-language Ordinary NP plus conditional non-Ppoly using concrete threshold growth | accepted source copied exactly |
| Ordinary.uniformP_ppolyDAG | SAME arbitrary L: Ordinary P implies canonical DAG P/poly | unconditional accepted source copied exactly |
| close | R implies SAME k/language in Ordinary NP and outside PpolyDAG/Ordinary P | composition of accepted proofs; extracted build/review status is separate |
| Audit | fully expanded named mirrors and separate type pins; seven printed roots | elaboration and axiom reporting; does not enforce an axiom allowlist |
| LightAudit | exact equivalence mirror/type pins; three presence-checked direct roots and transitive axiom allowlist | fail-closed axiom checks, not independent reproofs |
| KernelAudit | eight presence-checked direct roots and transitive axiom allowlist | fail-closed axiom checks, not independent reproofs |
| attempt template | imports only the light problem API | PARTIAL, final rejection required today |

The simulation uses the literal six-symbol Bool x Option Bool alphabet, two-sided
TM0 tape, fixed finite table, raw input initialization and literal halting. A live
accept label is not halt. The circuit's saturated halted state is not a continued
unpadded Ordinary.trace. Machine/table, clock and length construct the circuits;
language answers/correctness are not circuit-construction data. Lengths zero and
one remain covered by the original unchanged proofs. Ordinary NP uses its actual
relation, parser and original-input witness bound.

No hidden hNPWit, growth, simulator, clock, parser-success, provider or legacy
verifier premise has been introduced. R is substantial nonuniform promise-search
lower-bound strength, not a proved magnification shortcut. Decision-to-search is
used in its established direction; no converse or class-equivalence claim is made.
This package is Infrastructure extraction, not a new lower-bound proof. Existing
source options, heartbeat caps and scoped linter settings are preserved. Strict
new API checks do not imply unsuppressed whole-dependency lint or clean history.

PROVENANCE.json records the actual copied module/header closure, not a
proof-body/declaration minimum. Its strict v2 direct source mapping uses the
public `https://github.com/khanukov/p-np2.git` snapshot
`c96d9d72c99120e3775437414417505fd4904a3d` and exact
`conditional_separation/core/...` paths. All 1062 copied core hashes remain
unchanged. The original pnp3/pnp4 paths and donor
`e5dbbe7fd6dee72ae3c3b31a84b54fc1b2727f8f` are preserved as historical
LOCAL/NON-PUBLIC origin, not publicly fetchable inputs. Byte reproduction does
not independently establish prior internal acceptance, novelty, or a proof of R. All names, including private owners, remain the
original ones. The one additional accepted full-proposition surface is copied
because this package explicitly promises its roots. License terms are inherited,
not independently adjudicated. No literature/novelty audit is claimed.

## Research note

This is the mathematical introduction to the **direct standalone route**, not
an accompanying claim of a new lower bound. The only substantial research
premise supplied to `ConditionalSeparation.close` is the unproved
[`OpenProblem.R`](ConditionalSeparation/OpenProblem.lean). Ordinary NP membership
for its eventual language and the same-language Ordinary-P-to-DAG inclusion are
already proved in this formal development. The differently typed legacy
`ContentVerifierBridge` is not an extra assumption of `close`.

### The instance, promise and witness

Use three different length parameters:

| Symbol | Meaning |
|---|---|
| `n : Nat` | Number of variables of a Boolean function, including `n = 0` |
| `N = tableLen n = 2^n` | Number of bits in its **full** truth table `x` |
| `m` | Physical bit length of a query to the eventual prefix language |

For a fixed natural `k`, write `t_k(n) = n^k + k`. The promise on `x` is that
there exists a tree/formula `c` with `size c ≤ t_k(n)` computing that entire
truth table. There is no requirement to handle a NO-instance correctly. This
is a promise **search** problem: a valid output must encode such a small tree,
not merely say YES. See `treeMCSPSearchProblem`,
`TreeCircuitWitnessCodec.verifies` and `TreeMCSPSearchWitnessEncoding.ofCodec` in
[`SearchMCSPConcreteTargets.lean`](core/Pnp4/Frontier/SearchMCSPConcreteTargets.lean).

The witness object is literally `Pnp3.Models.Circuit n`: input, constant, NOT,
AND or OR, recursively arranged as a tree. Inputs/constants count as one node;
NOT adds one; a binary node adds both subtree sizes and one. Repeated subtrees
are counted repeatedly. It is a formula-size witness, not a sharing-enabled
DAG witness ([`Circuit`, `Circuit.size`](core/Models/Model_PartialMCSP.lean)).

The concrete witness bit width is

```text
W_k(n) = (bitLength n + 4) * (n^k + k).
bitLength 0 = 0; otherwise bitLength n = floor(log2 n) + 1.
```

`treeCircuitWitnessCodec` uses a self-delimiting tree code with input indices of
width `bitLength n`. Its encoder pads a short code to width `W_k(n)` with false
bits. The decoder consumes one complete tree and discards the returned tail;
it does **not** demand that every unused tail bit be zero. Malformed syntax or
an invalid input index may still fail, and the relation separately checks the
decoded tree's size and full truth table. These tail bits are different from
the zero-padding field of a prefix query below. See
[`treeSelfDelimitingCode`](core/Pnp4/Frontier/ContractExpansion/ConcreteTreeCodec.lean)
and [`SelfDelimitingCircuitCode.toCodec`](core/Pnp4/Frontier/ContractExpansion/ConcreteCodecGap.lean).

### The solver and exact quantifier order

A solver is a nonuniform family `S_(n,i)`, one Boolean circuit on **N input bits**
for each length `n` and each output bit `i < W_k(n)`. Its vector output must
satisfy the above relation on every promised table. Neither a uniform generator
for the family nor an algorithm constructing the circuits is required.

The solver circuits are the actual canonical `C_DAG`, an adapter to
`Pnp3.ComplexityInterfaces.DagCircuit`: gates can share previous wires, depend
only on earlier gates, and have constant/NOT/AND/OR operations. Size is the gate
count **plus one** for the output. Do not conflate this size with the tree size
of the sought witness. See [`C_DAG`](core/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean)
and [`DagCircuit`, `DagCircuit.size`, `InPpolyDAG`](core/Complexity/Interfaces.lean).

The literal statement in OpenProblem is:

```text
R = exists ONE k : Nat, for EVERY d : Nat,
      no BoundedSearchSolver exists for that fixed threshold/codec,
      with size(S_(n,i)) <= (2^n)^d + d for EVERY n and output bit i.
```

The correctness field is quantified over every `n` and every promised table
`x`; no correctness is required outside the promise. The bound is per output
bit and polynomial in **N**, not in `n`. The natural parameters include zero;
there is no hidden positive-length or sufficiently-large-length exception.
[`BoundedSearchSolver`](core/Pnp4/Frontier/SearchMCSPMagnification.lean) records
the family, its bounds and promise correctness explicitly.

`exists k, forall d` cannot be replaced by `forall d, exists k`: one threshold
must defeat all polynomial solver degrees. Excluding one degree is insufficient.
Nor does a proof of `R → R` supply R. This all-degrees nonuniform lower bound is
a substantial open premise; calling it a weak magnification shortcut would
misdescribe its strength. Polynomial growth of this threshold and codec width
in table length is proved separately by
[`polyBoundedInTable_thresholdPoly`](core/Pnp4/Frontier/ContractExpansion/ThresholdGrowth.lean)
and the concrete codec growth lemmas; it is not another research hypothesis.

### The language in the conclusion

For this codec, `L_k` is the **content prefix-extension** language, not a synonym
for ordinary decision-MCSP. A canonical query of length `M_k(n)` has layout

```text
8-bit tag 178 | Elias-gamma(n+1) | N truth-table bits x |
bitLength(W_k(n))-bit index i | i active prefix bits p | W_k(n)-i zero bits
M_k(n) = 8 + gammaLen(n) + N + bitLength(W_k(n)) + W_k(n)
gammaLen(n) = 2*bitLength(n+1)-1; 0 <= i <= W_k(n).
```

The strict parser checks the tag, decoded length, index bound and zero inactive
padding. A full witness agrees with `p` on its first `i` bits; zero query padding
is a syntactic condition, not an extra hardness hypothesis. See
[`treeMCSPPrefixM`, `parseTreeMCSPPrefixInput`](core/Pnp4/Frontier/ContractExpansion/PrefixParserConvention.lean)
and [`PrefixInput.prefixAgrees`](core/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean).

For an **arbitrary** physical word `y` of length `m`, the actual total language
is defined by:

```text
L_k(m,y) = true iff there exists w of length certificateLength(m,1) = m+1
such that ContentAccepts(codec_k, concat(y,w)).
```

`ContentAccepts` reads through `padRead` (out-of-range bits are false), decodes
a header on a padded window, runs the strict parser on the **computed** query
window `M_k(n)`, and reads its `W_k(n)` witness bits immediately after that
window. It requires successful parsing, prefix agreement and the tree search
relation. For canonical queries this is the intended witness-extension question.
For arbitrary physical lengths the displayed definition, including certificate
concatenation, is authoritative: do not silently replace it with a strict
`m = M_k(n)` language. Also do not infer that padding `y` leaves membership
unchanged: the certificate length and concatenation boundary move with `m`.
See [`ContentAccepts`, `ContentPrefixExtendable`, `ContentPrefixExtensionLanguage`](core/Pnp4/Frontier/ContractExpansion/ContentPrefixExtension.lean)
and [`certificateLength`](core/Complexity/Interfaces.lean).

### What the existing theorems establish

[`R_iff_original`](ConditionalSeparation/Equivalence.lean) is `Iff.rfl`: it
unfolds `treeProblem` to the exact OpenProblem formula. It proves no lower
bound and changes no quantifier. The decision-to-search transfer uses deciders
for this prefix-extension language to construct a greedy search solver with a
polynomial size schedule. This formalized direction is not a general
search/decision equivalence for MCSP.

[`close`](ConditionalSeparation/Conditional.lean), via
[`single_research_gap_ordinary_separation`](core/Pnp4/Frontier/ContractExpansion/SingleResearchGapFinal.lean),
composes the already proved NP construction, transfer and
[`Ordinary.uniformP_ppolyDAG`](core/UniformClassBridgeClosure/OrdinaryPpolyDAG.lean).
**Assuming R**, it returns one and the same `k` and `L_k` with:

```text
Ordinary.UniformNP L_k  AND  NOT PpolyDAG L_k  AND  NOT Ordinary.UniformP L_k.
```

This is an internal conditional theorem. No supplied proof closes R; no new
claim of its satisfiability, nonvacuity, novelty or unconditional P≠NP follows
from the packaging, a partial lemma, an axiom printout or successful tests.

### Model and literature boundaries

[`Ordinary.Model`](core/UniformClassBridgeClosure/Model.lean) fixes a finite
label type, one actual TM0 table over the six symbols `Bool × Option Bool`,
accept/reject states and polynomial exponents **before** all inputs. The tape
model is two-sided; the input encoding is literal. `Decides` demands actual
halting and no earlier visit to an accept/reject label; a live accept label is
not a completed decision. `UniformNP` fixes its verifier and both exponents,
rejects malformed pair encodings, bounds its witness in the original input
length, and bounds verifier time in encoded-pair length. The circuit class is
the explicit DAG model above. These definitions and their proved inclusion
are precise; independent adequacy/equivalence to all textbook machine and
complexity-class presentations has not been established here. Mirrors/type
pins and standard-axiom checks are not independent semantic reproofs.

| Primary reference | Relevance and limit for this R |
|---|---|
| Oliveira–Pich–Santhanam, *Hardness Magnification Near State-of-the-Art Lower Bounds*, [CCC 2019, Article 27](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2019.27) | Magnification for its specified Gap-MCSP/MKtP parameters motivates the program. No identification with this formula threshold, promise, codec and all-degrees DAG-search premise is supplied; the title is not a black-box proof of R. |
| Chen–Jin–Williams, *Hardness Magnification for Sparse Languages*, [ECCC TR19-118](https://eccc.weizmann.ac.il/report/2019/118/download), later JACM 2022 | Sparsity and search variants have their own parameters and consequences. Applicability requires matching those hypotheses; this note does not establish that match. |
| Ilango, [ECCC TR23-165, §1.1](https://eccc.weizmann.ac.il/report/2023/165/download/) | Search/decision relations need explicit reductions. Our specialized prefix-language transfer does not establish a universal MCSP search/decision equivalence. |

This is a finite applicability map, not an exhaustive literature or novelty
audit, institutional endorsement, or proof of R. For compiling and exchanging
small closed partial work, use the [partial-work guide](README.md#partial-work-across-machines).
