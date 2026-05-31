# R1-C3 structured failure: branchDeciderCircuit construction

## 1. What was attempted

I attempted to construct a real

```lean
branchDeciderCircuit :
  ∀ n j,
    C_DAG.Family ((treeMCSPSearchProblem threshold encoding).instanceBits n)
```

from the existing R1-C2 data:

- `deciderFamily : DagCircuitFamily (TreeMCSPPrefixExtractedLanguage threshold encoding obligations)`
- `queryBuilder : ∀ n j, BuildPrefixQueryForBitObligation threshold encoding obligations n j`.

The intended semantic target is:

```lean
x ↦ deciderFamily (obligations.M n)
      ((queryBuilder n j x prefixState branchBit).payload)
```

I audited the currently exposed APIs in:

- `pnp4/.../ContractExpansion/C_DAG_Adapter.lean`
- `pnp3/Complexity/Interfaces.lean`

for circuit-level composition/rewiring operators and corresponding size lemmas.

---

## 2. Exact type blocker

The blocker is a mismatch between **function-level query construction** and
**circuit-level composition needs**.

Current query builder type:

```lean
BuildPrefixQueryForBitObligation ... n j :=
  BitVec (instanceBits n) → PrefixDecisionState ... n j → Bool → PrefixQueryInput ... n j
```

This returns a payload bitvector by function evaluation, not by a family of DAG
circuits producing each payload bit.

To construct `branchDeciderCircuit` we need a primitive of the form (or equivalent):

```lean
composeDag : DagCircuit m → (Fin m → DagCircuit n) → DagCircuit n
```

plus correctness/size theorems.

No such composition/substitution/rewiring operator is exposed at the pnp3/pnp4
interfaces used by this route.

---

## 3. Missing primitive(s)

Minimal missing primitives:

1. **DagCircuit input substitution / rewiring composition**
   - Wire each input coordinate of a decider `DagCircuit (M n)` to either
     projection/constant/derived gate over base input width `instanceBits n`.

2. **Eval composition theorem**
   - `eval (composeDag D φ) x = eval D (fun i => eval (φ i) x)`.

3. **Size-composition upper bound**
   - explicit inequality needed to connect with `estimatedOutputBitSize`.

4. **Circuit-realizable query encoding bridge**
   - a theorem/interface showing each query payload bit from `queryBuilder` is
     realized by a small DAG circuit over base input bits.

Without these, branch decider construction is blocked.

---

## 4. Why this blocks `hExtract`

`TreeMCSPConcretePrefixToSolverObligation` needs an actual
`BoundedSearchSolver`, which requires concrete output circuits. At one-bit level,
we cannot even construct the required branch decider circuit from the current
interfaces.

So the extraction chain cannot proceed from statement-level skeleton to
constructive solver family until the missing composition bridge is added.

---

## 5. Local vs route-level classification

Classification: **ROUTE_LEVEL_BLOCKER** under current interface design.

Reason:

- This is not just “one missing helper lemma” in the current file.
- `BuildPrefixQueryForBitObligation` is function-level and lacks a circuit-level
  realizability contract; even with a local theorem tweak, constructive wiring is
  unavailable.
- The route can likely be repaired, but it requires interface redesign at the
  extraction boundary (query-as-circuit, not query-as-function).

---

## 6. Recommended next move

Single recommended move:

1. Refactor `BuildPrefixQueryForBitObligation` (or add a companion) to expose
   **payload-bit circuits**:
   - for each query bit coordinate `k`, provide
     `Qk : C_DAG.Family (instanceBits n)`;
   - prove `eval Qk x` equals payload bit `k`.
2. Add a local pnp3/pnp4 composition primitive and size theorem:
   - compose decider with query-bit circuits;
   - obtain branch decider circuit and size ledger bound.

This should convert R1-C3 from blocker to construction-landed without touching
trust-root or endpoints.
