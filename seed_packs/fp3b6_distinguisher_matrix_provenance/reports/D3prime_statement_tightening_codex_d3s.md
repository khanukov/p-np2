# D3' statement tightening — codex_d3s

Slot: D3S  
Handle: codex_d3s  
Scope classification: Infrastructure / markdown-only statement audit.  
Progress classification: Infrastructure. This report tightens the D3' theorem target; it does not prove a lower bound, promote a provenance filter, edit trust roots, append NoGoLog entries, or claim an endpoint.

## 0. Required-reading checklist

Read for this report:

- `seed_packs/fp3b6_distinguisher_matrix_provenance/README.md`
- `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_literature_parameter_table_gpt55.md`
- `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/Round2_D2_D3_D5_operator_review.md`, including §9 addendum
- `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/MatrixPrimitives.lean`
- `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/AntiCollapse.lean`
- `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean`
- `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean`
- `outputs/nogolog.jsonl` entries `NOGO-000006`, `NOGO-000007`, `NOGO-000008`, and `NOGO-000009`

## 1. What failed in old D3

The landed D3 statement has the shape:

```text
support_card(adversaryFamily_v_arbpayload F n) = widthFn n
∧
∀ m k r x,
  no sparse matrix separates {x} from {x} at radius r+1.
```

The second conjunct is degenerate for two reasons.

First, `{x}` versus `{x}` is an overlapping YES/NO relation.  A positive-radius fingerprint-separation predicate requires every YES point and every NO point to map to fingerprints at distance at least the requested radius.  If the same point is on both sides, any fingerprint map sends it to the same fingerprint on both sides, so the Hamming distance is exactly zero.  The failure is therefore just the identity fact `dist(fp_D x, fp_D x) = 0`, not an anti-collapse fact about arbitrary log-width payloads.

Second, the load-bearing impossibility does not mention the payload `F`.  The payload support-cardinality theorem is real, but the matrix failure would remain true if `F` were deleted from the theorem.  Thus old D3 only records that overlapping relations cannot be positively separated; it does not say that an all-essential hardwired payload defeats a non-overlapping, payload-derived YES/far-NO contract.

The later statement `¬(P → R)` does not strengthen this content.  If

```text
P := support_card(adversaryFamily_v_arbpayload F n) = widthFn n
R := ∃ D, SparseDistinguisherMatrix D ∧ FingerprintSeparation D {x} {x} (r+1),
```

then `¬(P → R)` is merely the implication-shaped presentation of `P ∧ ¬R` in classical logic, and the proof indeed uses the same two ingredients: the support-cardinality lemma for `P`, and the overlapping-singleton impossibility for `¬R`.  Rewriting the connective changes rhetoric, not mathematical content.  D3' must instead make `F` a non-spurious dependency of the non-separation claim and must use disjoint YES/NO sets.

## 2. Candidate D3'-A statement

### 2.1 Core idea

Use a concrete all-essential payload family whose derived YES set is a single payload-window point, and whose far-NO set is a large Hamming ball shell away from that point.  The no-separation proof should be a row-support union argument, not the old `{x}` versus `{x}` argument.

Let `w(n) := widthFn n = Nat.log2 (n + 1)`.  Take an all-essential payload family `F_and` with

```text
F_and n u := AND over all coordinates of u : Bitstring (w(n)).
```

At an ambient length `n`, define `anchor_n : Bitstring n` by:

- the first `w(n)` coordinates are `true`;
- the tail coordinates are `false`.

Define the payload-window Hamming distance from `anchor_n` by counting disagreements only in the first `w(n)` coordinates.

### 2.2 YES_F

```text
YES_F(n) := { anchor_n }.
```

Equivalently, this is the unique ambient input with tail fixed to zero and with the embedded payload window satisfying `F_and n = true`.

### 2.3 NO_F

For a fixed input-farness parameter `ρ ≥ 1`, define:

```text
NO_F(n, ρ) :=
  { y : Bitstring n |
      y agrees with anchor_n on every tail coordinate, and
      payloadWindowDistance(y, anchor_n) ≥ ρ }.
```

This is derived from `F_and` because `F_and` singles out the all-true payload-window point; the NO set is the set of tail-fixed ambient inputs whose payload window is far from that unique accepting payload point.

### 2.4 What “far” means

“Far” means Hamming-far in the embedded payload window, not merely unequal as ambient bitstrings:

```text
payloadWindowDistance(y, anchor_n) ≥ ρ.
```

The intended first Lean target can set `ρ = 2` for a small concrete theorem, or keep `ρ` symbolic with hypotheses `1 ≤ ρ` and `m * k + ρ ≤ w(n)`.  The tail is fixed in both YES and NO so that outside-window coordinates cannot accidentally provide a separator unrelated to the payload.

### 2.5 Fixed sparse matrix bounds

The sparse matrix bounds should be fixed before choosing the large enough ambient length:

```text
m : Nat       -- fingerprint output length / row count
k : Nat       -- row and column support bound from SparseDistinguisherMatrix
δ := 1        -- fingerprint separation radius
ρ : Nat       -- input farness radius, with 1 ≤ ρ
```

The no-separation theorem should assume:

```text
m * k + ρ ≤ w(n).
```

Reason: any `m × n` matrix with row support at most `k` queries at most `m*k` input coordinates in the union of its row supports.  If at least `ρ` payload-window coordinates are not queried, choose `y ∈ NO_F(n, ρ)` by flipping exactly `ρ` unqueried payload-window coordinates of `anchor_n` and leaving every queried coordinate and every tail coordinate unchanged.  Then every row sees the same selected bits on `anchor_n` and `y`, so the fingerprints are equal.  Equal fingerprints contradict radius-`1` separation.

Column sparsity is still part of `SparseDistinguisherMatrix`; it is not load-bearing in this counting proof, but it keeps the statement aligned with the D1 matrix interface and the D5 symbolic parameter dictionary.

### 2.6 Why a trivial one-row coordinate separator cannot immediately solve it

A one-row coordinate selector sees only one coordinate.  If `ρ ≥ 1` and `w(n) ≥ 2`, then for every selected coordinate inside the payload window there is a NO point that flips `ρ` unselected payload coordinates and agrees with `anchor_n` on the selected coordinate.  If the selected coordinate is outside the payload window, the tail-fixing condition makes the YES and NO values agree there as well.  Therefore a one-coordinate row cannot separate all YES/NO pairs.

The more general guard `m*k + ρ ≤ w(n)` is exactly the multi-row version of this stress test.

### 2.7 Candidate theorem statement, in prose

```text
For every fixed m k ρ with 1 ≤ ρ, there exists n with m*k + ρ ≤ widthFn n
such that, for the all-essential payload family F_and and the non-overlapping
sets YES_F(n) and NO_F(n,ρ) above, no BoolMatrix D satisfying
SparseDistinguisherMatrix m n k D has FingerprintSeparation D YES_F NO_F 1.
```

This is existential anti-collapse in the required sense: it gives a specific all-essential payload and a non-overlapping payload-derived far-NO relation for which bounded sparse matrices do not supply the semantic fingerprint witness.

## 3. Candidate D3'-B statement

### 3.1 Core idea

A hardwiring-twin target should compare two families with the same support profile but different fingerprint contracts:

- an honest family `H` for which a sparse fingerprint witness is supplied as part of the honest provenance; and
- a hardwiring twin `T` with the same support profile, for which no comparable sparse fingerprint witness exists against its payload-derived far-NO relation.

This is the right conceptual answer to `NOGO-000007`, but it is more delicate than D3'-A because “same support profile” must not collapse to a syntactic-only condition vulnerable to `NOGO-000008`/`NOGO-000009`, and “comparable fingerprint witness” must fix the same matrix budget before comparing `H` and `T`.

### 3.2 What H is

A proposed honest object is a packaged family

```text
H := HonestProfiledFamily
```

with the following fields, all at each length `n`:

1. a semantic support set `S_H(n) ⊆ Fin n`, intended to be the canonical prefix support of size `widthFn n`;
2. disjoint relation sets `YES_H(n), NO_H(n) ⊆ Bitstring n`;
3. an explicit matrix `D_H(n) : BoolMatrix m n`; and
4. a proof/contract that `D_H(n)` satisfies `SparseDistinguisherMatrix m n k` and `FingerprintSeparation D_H(n) YES_H(n) NO_H(n) δ`.

For a minimal finite first target, `H` can be a code-like toy family whose YES/NO relation is deliberately aligned with a small public fingerprint witness.  For example, at a selected length, `YES_H` and `NO_H` may differ on a declared checker coordinate or on a declared set of checker coordinates, while the family's semantic support profile remains the full prefix window by requiring the underlying honest predicate to depend on all prefix coordinates.

### 3.3 What T is

The hardwiring twin `T` should use the D3'-A payload construction on exactly the same support profile:

```text
T := hardwired all-essential prefix-window payload twin using F_and.
```

At the same length `n`, define:

```text
YES_T(n) := { anchor_n }
NO_T(n,ρ) := tail-fixed points at payload-window distance at least ρ from anchor_n.
```

The intended non-separation side is:

```text
¬ ∃ D_T : BoolMatrix m n,
    SparseDistinguisherMatrix m n k D_T ∧
    FingerprintSeparation D_T YES_T(n) NO_T(n,ρ) 1,
```

under the same budget guard `m*k + ρ ≤ widthFn n`.

### 3.4 What “same support profile” means

For D3'-B, “same support profile” should be semantic and lengthwise, not merely displayed syntax:

```text
SameSupportProfile H T :=
  ∀ n,
    supportSet(H n) = supportSet(T n)
    ∧ supportCard(H n) = supportCard(T n)
    ∧ supportSet(H n) = prefixWindow(widthFn n).
```

At minimum, the theorem should assert equality of the actual `FormulaCircuit.support` sets, not only equality of support cardinalities.  Cardinality-only equality would fall back into `NOGO-000007`; syntax-only equality would invite the rewrite/normalisation problems captured by `NOGO-000008` and `NOGO-000009`.

### 3.5 What matrix/fingerprint contract distinguishes H and T

The distinguishing contract is asymmetric:

```text
FingerprintSeparation D_H YES_H NO_H δ
```

is positively supplied for `H`, while the theorem proves that no `D_T` with the same `m,k,δ` budget separates `T`'s payload-derived YES/far-NO relation.  The same support profile therefore does not imply the same fingerprint provenance status.

### 3.6 Candidate theorem statement, in prose

```text
There exist H, T, n, m, k, ρ such that:
  1 ≤ ρ,
  m*k + ρ ≤ widthFn n,
  SameSupportProfile H T at n,
  ∃ D_H, SparseDistinguisherMatrix m n k D_H ∧
       FingerprintSeparation D_H YES_H(n) NO_H(n) 1,
  and
  ¬ ∃ D_T, SparseDistinguisherMatrix m n k D_T ∧
       FingerprintSeparation D_T YES_T(n,ρ) NO_T(n,ρ) 1.
```

This is the preferred strategic shape, but it should not be dispatched until `H` is pinned down with a genuinely full-support semantic profile and a fixed-budget matrix witness.  Otherwise the statement risks becoming another support-profile slogan rather than a theorem.

## 4. Trivial-separator stress test

### 4.1 Candidate D3'-A

Question: could a matrix row selecting one differing coordinate separate the YES/NO sets?

Answer: no, provided the theorem includes the guard `m*k + ρ ≤ widthFn n` and uses `ρ ≥ 1`.  For `m=1,k=1`, a selected coordinate is only one queried coordinate.  Since at least `ρ` payload-window coordinates remain unqueried, choose the NO point by flipping unqueried coordinates only.  The one row then sees the same value on the YES anchor and on this NO point, so the fingerprints agree.  A one-coordinate separator therefore fails.

Result: **passes stress test**.

### 4.2 Candidate D3'-B

Question: could a matrix row selecting one differing coordinate separate the YES/NO sets?

For the honest side `H`, yes, a small explicit coordinate/checker separator may be exactly the witness.  That is not a defect, because D3'-B is supposed to assert positive fingerprint provenance for `H`.

For the hardwiring-twin side `T`, no, if `T` reuses the D3'-A anchor/far-ball relation and the theorem fixes the same budget guard `m*k + ρ ≤ widthFn n`.  The coordinate row can be avoided by flipping only unquered payload-window coordinates, producing a NO point with the same fingerprint as the YES anchor.

Result: **passes stress test for the negative `T` side**, but **not yet dispatch-ready** until the honest `H` object and `SameSupportProfile` predicate are specified tightly enough to avoid a cardinality-only or syntax-only collapse.

## 5. Quantifier discipline

### 5.1 Candidate D3'-A quantifiers

Recommended order:

```text
∀ m k ρ,
  1 ≤ ρ →
  ∃ n,
    m*k + ρ ≤ widthFn n ∧
    let F := F_and in
    AllEssentialPayload F ∧
    YES_F(n) ∩ NO_F(n,ρ) = ∅ ∧
    ¬ ∃ D : BoolMatrix m n,
        SparseDistinguisherMatrix m n k D ∧
        FingerprintSeparation D YES_F(n) NO_F(n,ρ) 1.
```

A finite starter theorem may instead fix concrete `m`, `k`, `ρ`, and `n`, but the non-degeneracy-critical order is the same: choose the matrix budget before the large enough payload window, and make the negative statement quantify over all matrices at that fixed budget.

### 5.2 Candidate D3'-B quantifiers

Recommended order:

```text
∃ H T n m k ρ,
  1 ≤ ρ ∧
  m*k + ρ ≤ widthFn n ∧
  SameSupportProfile H T n ∧
  (∃ D_H : BoolMatrix m n,
      SparseDistinguisherMatrix m n k D_H ∧
      FingerprintSeparation D_H (YES_H n) (NO_H n) 1) ∧
  ¬ ∃ D_T : BoolMatrix m n,
      SparseDistinguisherMatrix m n k D_T ∧
      FingerprintSeparation D_T (YES_T n ρ) (NO_T n ρ) 1.
```

If generalized uniformly over infinitely many lengths, the budget must still be fixed before the negative `T` matrix quantifier; otherwise the identity matrix with enough rows can trivially separate many far-ball relations.

## 6. Recommendation

Recommendation: **dispatch_D3prime_A**.

Reason: D3'-A has a clean non-degenerate theorem shape whose proof obligation is a finite support-union argument against all sparse matrices at a fixed budget.  It directly fixes the old D3 mistakes:

- `YES_F` and `NO_F` are disjoint by construction;
- `NO_F` is far in payload-window Hamming distance;
- `F_and` is all-essential and load-bearing because its unique accepting payload point defines the anchor;
- the no-separation proof depends on the sparse row-support budget rather than on overlapping-singleton reflexivity; and
- a one-coordinate separator is neutralized by choosing the NO point outside queried coordinates.

D3'-B remains valuable as a follow-up, but it needs one more design pass to pin down a genuinely honest full-support `H` and a semantic `SameSupportProfile` predicate.  Dispatching B too early risks reproducing the support-cardinality-only and syntax-only traps documented by `NOGO-000007` through `NOGO-000009`.

## 7. Lean target sketch

No Lean code is written in this report.  If D3'-A is dispatched, use a new handle directory rather than importing the old D3 theorem:

```text
pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_d3prime_a/AntiCollapsePrime.lean
```

Suggested theorem/definition names for the next Lean worker:

- `andPayloadFamily`
- `payloadAnchor`
- `payloadWindowDistance`
- `payloadFarNoSet`
- `payloadYesSet`
- `andPayload_allEssential`
- `payloadYes_farNo_disjoint`
- `sparseMatrix_queryUnion_card_le_mul`
- `exists_farNo_agreeing_on_queryUnion`
- `andPayload_no_sparse_fingerprintSeparation`

Suggested headline theorem:

```text
andPayload_no_sparse_fingerprintSeparation
```

Target prose statement:

```text
For fixed m k ρ with 1 ≤ ρ, choose n with m*k + ρ ≤ widthFn n.
For the all-essential AND payload and its anchor/far-ball YES/NO sets,
there is no m-row k-sparse matrix whose fingerprint separates YES from NO
at fingerprint radius 1.
```

## 8. Output summary

Slot: D3S  
Handle: codex_d3s  
Report path: `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D3prime_statement_tightening_codex_d3s.md`  
Recommendation: dispatch_D3prime_A  
Candidate D3'-A: all-essential AND payload; YES is the all-true prefix anchor with fixed zero tail; NO is the tail-fixed payload-window Hamming-far shell; no fixed-budget sparse matrix separates when `m*k + ρ ≤ widthFn n`.  
Candidate D3'-B: same-support-profile honest/twin schema with a positive witness for honest `H` and D3'-A-style no-witness hardwiring twin `T`; strategically useful but not yet recommended until `H` is made fully semantic and fixed-budget.  
Trivial-separator stress-test result: D3'-A passes; D3'-B passes on the negative hardwiring-twin side but needs one design pass before dispatch.  
Commands run: see final response.  
Scope violations: none; markdown report only.
