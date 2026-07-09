# Streaming magnification model audit

Status: **AUDIT COMPLETE; IMPLEMENTATION NOT YET CLAIMED**

Base: `main@5d8ee5f80e1dbc4fb7bd0c725fa98f1a999770d0`

Local branch: `research/mmw-chmy-streaming-p-ne-np`

Read-only reference branches:

- `origin/claude/elegant-noether-CnlU5@b1f4f31d9ed5d2d803dc041efab4f164b2815198`
- `origin/claude/gallant-goldberg-iqjsx0@57ee057a4b0dc3a3259b60e73790960847a6d65b`
- `origin/claude/fervent-einstein-7m9anz@4a8ee0c97b25cc770cdcb0677a189cef90a4842d`

Primary sources:

- McKay, Murray, Williams, [*Weak lower bounds on resource-bounded compression imply strong separations of complexity classes*](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf), STOC 2019 (MMW).
- Chen, Jin, Santhanam, Williams, [*Constructive Separations and Their Consequences*](https://theoretics.episciences.org/12881/pdf), TheoretiCS 2024, especially Lemma 3.2.
- Hirahara, Ilango, Williams, [*Beating Brute Force for Compression Problems*](https://eccc.weizmann.ac.il/report/2023/171/download), STOC 2024/ECCC TR23-171, especially Lemma 2.1.

## Object-by-object alignment

| Paper object | Exact paper meaning | Repository object at the base | Match? | Required repair |
| --- | --- | --- | --- | --- |
| Boolean circuit in MCSP | Ordinary shared fan-in-2 Boolean DAG over AND/OR/NOT; size is internal gate count | `Pnp3.ComplexityInterfaces.DagCircuit` is a genuine topologically ordered DAG, but `Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP.treeCircuitClass` uses `Pnp3.Models.Circuit`, a tree/formula | Partial | Reuse or adapt `DagCircuit`; do not reuse `treeCircuitClass` for the MMW endpoint. Add a concrete serializable DAG representation and reconcile its gate-count convention with `DagCircuit.size = gates + 1`. |
| Truth-table ordering | `N = 2^n` bits in lexicographic input order from `0^n` to `1^n` | `Pnp3.Models.truthTableFunction` indexes by `bitVecToNat`, with coordinate 0 as the least-significant bit | No proof of equality | Define the paper order explicitly, or prove an input-coordinate reversal theorem preserving DAG size. Do not silently identify the two orders. |
| search-MCSP result | On every table, return a size-at-most-`s(n)` circuit computing it, or report that none exists | `SearchMCSPCompressionProblem` has a promise and a witness relation; `totalOnPromise` only supplies a witness on promised inputs | No | Introduce a concrete tagged total result and prove both found and no-circuit directions. |
| NO result | `noCircuit` iff no valid bounded circuit computes the table | No concrete NO witness/correctness theorem in the current search surface | No | Make failure a constructor, not an all-zero code or an unconstrained promise case. |
| Streaming machine | One fixed deterministic one-pass bit-RAM program; explicit next-bit requests; fixed finite RAM instruction palette | No MMW streaming model in `main` | No | Add operational configurations, small-step semantics, input cursor, work memory, output/report phase, and one uniform program for all lengths. A bare `List Bool -> MCSPResult` is forbidden. |
| Space | Maximum `S(N)` work bits, excluding the read-only input and write-only output | No corresponding search-MCSP resource measure | No | Define it from reachable operational configurations. |
| Update/report time | Worst-case RAM operations between successive reads, and final reporting operations | No corresponding resource measure | No | Define worst-case gaps, not amortized total time; include polynomial reporting time. |
| Circuit-Min-Merge | Canonical minimum-size, then lexicographically first, DAG satisfying disjoint interval constraints; output bits are in `Sigma_3^P` for the oracle-free case | No implementation in `main` | No | Define validity on malformed codes, size-then-code order, fixed tagged output, and the exact finite-PH language. |
| Stream-Merge | Merge current circuit, already-read prefix, and next block into a canonical bounded DAG, or fail | No implementation in `main` | No | Handle the last partial block, `blockLen > N`, rounding, and tag length. The STOC pseudocode's divisibility shortcut cannot be copied literally. |
| One-tape RTM | Separate one-way read-only input tape, one two-way read/write work tape, and for RTM an independent one-way random tape | Existing `Pnp3.Internal.PsubsetPpoly.TM` starts with the whole input on its single read/write tape | No | Keep CHMY in a separate module with a separate machine semantics. Do not identify it with the MMW RAM or the existing loaded-input TM. |
| Threshold | For the requested specialization, `s_k(n) = max n (n^k)`, `k >= 1`; table length is `N = 2^n` | Existing MCSP surfaces accept arbitrary thresholds but have no requested schedule | Partial | Add the exact schedule and keep `n`, `N`, gate count, and code length distinct. |
| Circuit-code length | MMW uses a fixed-constant `O(s log s)` placeholder; modern fan-in-2 encoding is `(1+o(1)) s log_2(s+n)` | Tree-code bounds exist under `ContractExpansion`; no general DAG codec/bound exists | No | Prove an explicit finite bound such as `c * s * ceilLog2(s+n+2)` for the chosen DAG codec. Do not treat MMW's constant `100` as definitional. |
| Polynomial-in-`s` quantifiers | One uniform machine, then existential space/update/report exponents and constants, then an eventual universal length bound | Current weak-search targets fix one size schedule and do not express the full streaming resource negation | No | Define solvability with `exists machine, exists exponents/constants/n0, forall n >= n0`; the lower bound negates the entire existential. |
| `P = NP` / `P_ne_NP` | Equality/inequality of uniform language classes | `Pnp3.ComplexityInterfaces.P`, `NP`, and `P_ne_NP := P != NP` are concrete TM-based definitions | Yes at endpoint | A proof of the MMW upper direction still needs the finite-PH collapse/search-reconstruction derivation; `main` has no PH hierarchy supporting it. |
| Nonuniform `P/poly` | Polynomial-size shared DAG circuit families | `Pnp3.ComplexityInterfaces.PpolyDAG` and `InPpolyDAG` | Yes | Do not substitute `PpolyFormula`. The direct MMW Theorem 1.3 route reaches `P_ne_NP` without first producing this nonuniform source. |

## Repository audit findings

1. `SearchMCSPMagnification.lean` is a conditional contract surface. Its decisive field is `SearchMCSPMagnificationContract.magnifiesToVerifiedDAGSource`; it does not prove that field.
2. The reference verifier work does **not** close the full NP-witness stack. `elegant` proves semantic checking only and explicitly lacks the bridge to `TM.accepts`. `gallant`/`fervent` package `ContentPrefixExtensionNPWitness` as a structure, and their endpoint still takes both `hNoPoly` and `hNPWit`. Thus witness-checking semantics advanced, but neither the formal NP witness nor `hNoPoly` is discharged.
3. `main` contains no operational MMW one-pass streaming RAM.
4. `main` contains neither Circuit-Min-Merge nor Stream-Merge for standard DAG MCSP.
5. `main` contains no formalization of CHMY Lemma 15.
6. No audited zero-argument theorem in the inspected base or reference branches proves `P_ne_NP` without an explicit source/lower-bound hypothesis.

## MMW corrections that the formalization must make explicit

- The final block may have fewer than the nominal `O(s log s)` bits. It must be processed with `r = min blockLen (N - consumed)` rather than ignored.
- A successful merge and failure must use a collision-free tagged fixed-length encoding. The paper's prose alternates between an `L`-bit answer and `1<C>`; Lean must fix the body and tag lengths.
- Algorithm 1 calls an object named `Circuit-Min-Merge` at one point although the stated signature is Stream-Merge. The implementation must keep these two specifications distinct.
- If `blockLen > N` at small lengths, use one partial block. The eventual asymptotic proof may patch finitely many small `n`, but correctness is required at every length.
- The A-free route should be formalized directly over ordinary AND/OR/NOT DAGs; literal empty-oracle gates must not be silently equated with ordinary circuits at an exact threshold.

## Exact resource quantifiers

For fixed `k >= 1`, the intended positive predicate has the following normal form (with correctness for every table and eventual resource bounds):

```text
exists one uniform stream machine M,
exists a b : Nat,
exists Cspace Cupdate Creport n0 : Nat,
forall n >= n0,
forall T : TruthTable n,
  CorrectTotalSearch M n T (s_k k n) /\
  Space M n T <= Cspace * (s_k k n + 1)^a + Cspace /\
  MaxUpdateGap M n T <= Cupdate * (s_k k n + 1)^b + Cupdate /\
  ReportTime M n T <= Creport * (s_k k n + 1)^b + Creport.
```

The requested lower bound is the negation of this entire existential. Ruling out one fixed exponent or one fixed machine is insufficient.

## Current classification and governance note

The mathematical MMW target is a conditional magnification theorem:

```text
not PolyStreamingSolvable(search-MCSP[s_k]) -> P != NP.
```

It is not an unconditional separation until the antecedent is proved. In addition, current `AGENTS.md` only labels a pnp4 route as P-vs-NP mainline when it reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource` and reaches `NP not_subset PpolyDAG`. MMW Theorem 1.3 reaches uniform `P != NP` directly, so it must be reported as a direct conditional route, not silently relabeled as the repository's existing nonuniform mainline. A future deliberate route-policy change or an additional proved `VerifiedNPDAGLowerBoundSource` bridge would be needed to classify it as that mainline.

## Open implementation frontier after this audit

The first missing formal object is a **concrete serializable ordinary DAG circuit model with a proved code-length bound and exact truth-table ordering**. It is infrastructure, not a lower-bound hypothesis. After that object is closed, the next mathematical/formal frontier is the finite-PH derivation of exact Stream-Merge under `P = NP`; no `Contract`, `Source`, `Provider`, typeclass, axiom, or hidden instance may stand in for it.
