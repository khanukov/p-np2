# R1-C2 structured failure: one-bit branchDeciderCircuit construction

## 1) What was attempted

Goal attempted:

- construct `branchDeciderCircuit : ∀ n j, C_DAG.Family (instanceBits n)`
  from:
  - `deciderFamily : DagCircuitFamily (TreeMCSPPrefixExtractedLanguage ...)`
  - `queryBuilder : ∀ n j, BuildPrefixQueryForBitObligation ... n j`.

Attempt path:

1. Inspect `C_DAG` adapter (`ContractExpansion/C_DAG_Adapter.lean`) and
   underlying `Pnp3.ComplexityInterfaces.DagCircuit` API.
2. Search for a circuit-level combinator to wire a DAG circuit over inputs of
   length `M n` with an input-embedding map from base instance bits to query bits.
3. Search for substitution/composition/rewiring + size lemma suitable for
   constructing `x ↦ deciderFamily (M n) (queryBuilder ... x ... b).payload`.

Result: could not produce a real construction term with current exposed APIs.

---

## 2) Exact type blocker

The current `queryBuilder` interface is **function-level**:

```lean
BuildPrefixQueryForBitObligation ... n j :=
  BitVec (instanceBits n) → PrefixDecisionState ... n j → Bool → PrefixQueryInput ... n j
```

while `deciderFamily` expects a circuit input bitvector of length `M n`.

To build `branchDeciderCircuit`, we need a primitive equivalent to:

```lean
DagCircuit.compose
  : DagCircuit m → (Fin m → DagCircuit n) → DagCircuit n
```

(or a comparable substitution/wiring operator plus semantics/size theorems).

No such public primitive was found in the frozen interfaces used by pnp4.

---

## 3) Missing closure lemma/primitive

Missing primitive set (minimal):

1. **DAG input substitution / rewire composition**
   - Build a new `DagCircuit n` by wiring each input pin of `DagCircuit m` to a
     circuit over `n` bits (or at least to a projection/constant expression).

2. **Semantics theorem for composition**
   - `eval (compose C φ) x = eval C (φ_eval x)`.

3. **Size bound theorem for composition**
   - explicit upper bound needed by R1-C1 ledger.

4. **Circuit-realizable query embedding**
   - current queryBuilder is a pure function producing payload bitvectors; missing
     bridge that each payload bit is itself produced by a small DAG over base `x`.

Without these, `branchDeciderCircuit` cannot be constructed constructively.

---

## 4) Local engineering vs route-level blocker

Classification: **LOCAL_CLOSURE_BLOCKER** (not a route-level impossibility).

Why local:

- The mathematical construction is standard (compose decider with query encoder).
- Blocker is API exposure: no publicly usable DAG composition/wiring operator with
  semantics + size lemmas at this layer.

Why not route-level:

- No contradiction with SearchMCSP route logic.
- No barrier argument that construction is impossible in principle.

---

## 5) Recommended next move

Single next step:

1. Add a minimal DAG wiring/composition helper module (local to contract
   expansion or a safe pnp3 utility layer), exposing:
   - composition operator,
   - eval correctness lemma,
   - size upper bound lemma.

Then redefine `BuildPrefixQueryForBitObligation` in circuit-realizable form
(or add a companion obligation proving query payload bits are realizable by small
DAGs), and retry R1-C3 construction.

This keeps the effort engineering-local and directly unblocks `hExtract` work.
