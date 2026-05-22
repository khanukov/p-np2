# SearchMCSP R1-C0: concrete prefix-to-solver extraction feasibility audit

## 1) Executive verdict

**YELLOW_NEEDS_SIZEBOUND_REPAIR**

Short reason:

- The extraction shape from `PpolyDAG (PrefixExtensionLanguage parser)` to
  `Nonempty (BoundedSearchSolver target)` is conceptually standard and appears
  feasible.
- The blocking uncertainty is not logical correctness but the **exact size
  accounting** needed to land it under a practical `sizeBound` in the current
  `BoundedSearchSolver` surface (one circuit per output bit, no explicit shared
  DAG accounting in the type).

---

## 2) Exact theorem surface

Target theorem in current symbols:

```lean
TreeMCSPConcretePrefixToSolverObligation
  (threshold : Nat → Nat)
  (encoding : TreeMCSPSearchWitnessEncoding threshold)
  (sizeBound : Nat → Nat)
  (obligations : TreeMCSPPrefixParserObligations threshold encoding) : Prop
```

Unfolded form:

```lean
Pnp3.ComplexityInterfaces.PpolyDAG
  (TreeMCSPPrefixExtractedLanguage threshold encoding obligations)
→ Nonempty
    (BoundedSearchSolver
      (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem
      (TreeMCSP_C_DAG_Target threshold encoding sizeBound).circuitClass
      (TreeMCSP_C_DAG_Target threshold encoding sizeBound).sizeBound)
```

With `TreeMCSP_C_DAG_Target ...` and concrete language alias from L1, this is
exactly the R1-C extraction obligation.

---

## 3) Bit-by-bit extraction plan

Assume a nonuniform decider family for
`TreeMCSPPrefixExtractedLanguage threshold encoding obligations`.

Plan:

1. **Prefix query semantics**
   - For fixed instance `x` and current prefix `p` of length `i`, build encoded
     language input representing `(tag, n, x, i+1, p ++ b, pad)` for branch
     `b ∈ {0,1}`.
   - Query decider on branch-0 encoding first.

2. **Bit selection rule**
   - If branch-0 query accepts, output bit `0`.
   - Otherwise output bit `1`.

3. **Output-bit circuits**
   - For each witness coordinate `j`, define one output circuit that implements
     the above rule using previously selected bits as internal logic.
   - In nonuniform setting, this is done by circuit composition/hardwiring of
     parser-layout constants and branch control.

4. **Correctness on promised inputs**
   - Promise gives existence of at least one full witness.
   - Prefix extension semantics guarantee at each step at least one branch is
     extendable.
   - Chosen bits therefore stay on an extendable path.

5. **Malformed inputs**
   - Handled by parser-level rejection semantics of `PrefixExtensionLanguage`.
   - Extraction only needs canonical well-formed encodings for queries; malformed
     ambient inputs are irrelevant to solver correctness because solver feeds the
     decider with deliberate internal encodings.

---

## 4) Size ledger

This is the critical risk section.

Let:

- `S_dec(n)` = size bound of prefix-language decider on ambient length `M(n)`;
- `W(n)` = witness bit-length = `problem.witnessBits n`;
- `E(n, j)` = overhead to encode query input for step `j` (tag/gamma/x/i/p/pad);
- `C_sel(n, j)` = control logic cost to choose branch bit from decider result and
  prior extracted bits.

Per-bit output circuit size candidate:

\[
S_{out}(n,j) \approx S_{dec}(M(n)) + E(n,j) + C_{sel}(n,j).
\]

Important subcases:

1. **Naive duplication per `j`**
   - Each output bit circuit internally recomputes all earlier branch decisions.
   - Worst-case can introduce multiplicative blowup by `j`, giving near
     `O(W(n) * S_dec(M(n)))` for late bits.

2. **Shared-DAG intuition vs current type**
   - Mathematically one wants shared prefix-query DAG reused across bits.
   - But `BoundedSearchSolver` stores **separate per-bit circuits**; shared nodes
     are not explicitly represented across coordinates.
   - Unless we prove a factoring lemma that each per-bit circuit can stay within
     a similar polynomial bound despite recomputation, the ledger can inflate.

3. **Parser/encoding overhead**
   - If query encoder is circuit-friendly (mostly wiring + constants + small
     arithmetic on `i`), overhead can be low-order polynomial.
   - If gamma/index handling needs heavy arithmetic each time, overhead may be
     nontrivial but still likely polynomial.

4. **Required `sizeBound` relation**
   - Safe conservative expectation: `sizeBound` must dominate composed extraction
     circuits, potentially larger polynomial than base decider bound.
   - If current intended `sizeBound` is too tight (e.g., near-decider-size with
     no slack), theorem may fail without repair.

Conclusion on ledger:

- Feasibility likely with **repaired/explicit sizeBound schedule**.
- Not yet justified that one can keep the exact same polynomial as raw decider
  family without additional sharing lemmas.

---

## 5) Nonuniformity audit

- Uses one decider family by length (standard `PpolyDAG` witness), reused in the
  construction.
- Does **not** require advice depending on specific runtime input instance `x`
  beyond normal nonuniform length-dependent circuits.
- No forbidden per-instance hardwiring is needed for extraction theorem itself;
  all hardwiring is of parser format constants and branch wiring schema.
- Risk remains only in accidental over-hardwiring if implementation shortcuts the
  query encoder by embedding large per-input tables (should be disallowed).

---

## 6) Correctness proof plan

Inductive skeleton:

1. **Base:** empty prefix is extendable for promised `x` by totality.
2. **Step:** if prefix `p` is extendable, then at least one of `p0` or `p1`
   extendable (witness next bit decides branch).
3. **Choice rule correctness:** branch-0 accepted ⇒ choose `0`; else choose `1`.
   If both accepted, either is fine.
4. **Invariant:** chosen prefix after each step is extendable.
5. **Termination:** at full length `W(n)`, extendable full prefix means relation
   witness itself, yielding solver correctness.

This uses only language semantics + decider correctness, no NP-membership fact.

---

## 7) Dependency on NP proof

Extraction theorem **does not require** `L ∈ NP`.

- It needs only: (i) decider existence for language, (ii) prefix-extension
  semantics, (iii) construction/size of query circuits.
- NP is needed later for packaging into `VerifiedNPDAGLowerBoundSource`, but not
  for decider-to-solver extraction itself.

---

## 8) Hardwiring / NoGo audit

- **CircuitPHP side-track failure:** informative caution only; does not directly
  refute this extraction because this step is conditional on `PpolyDAG` decider.
- **Per-slice hardwiring risk:** moderate; must ensure extraction circuits are
  length-uniform and not per-instance lookup tables.
- **Wrapper fields risk:** improved in L1 surface; obligations are explicit.
- **FormulaCertificateProviderPartial refutation:** not on this dependency path.
- **Iso-strong closure no-go:** not directly applicable, but reinforces need for
  strict quantifier discipline and no hidden witness universality tricks.

Status: risks are manageable with explicit size/accounting lemmas.

---

## 9) Recommended next Lean task

Exactly one next task (recommended):

**Prove one size ledger lemma** for the query embedding circuit family:

- formalize an upper bound template for per-bit extraction circuit size in terms
  of `S_dec(M(n))`, `W(n)`, and fixed parser overhead;
- derive a concrete admissible `sizeBound` schedule for
  `TreeMCSP_C_DAG_Target threshold encoding sizeBound`.

Why this task first:

- correctness proof skeleton is standard;
- size accounting is currently the highest uncertainty and directly determines
  whether R1-C theorem can inhabit current `BoundedSearchSolver` type.

---

## Final assessment snapshot

- Logical extraction shape: **feasible**.
- Immediate blocker: **exact per-output-bit size bound accounting**.
- Route status at R1-C0: **YELLOW_NEEDS_SIZEBOUND_REPAIR**.
