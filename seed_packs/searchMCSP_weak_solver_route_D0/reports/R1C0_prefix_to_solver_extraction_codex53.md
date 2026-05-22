# SearchMCSP R1-C0 extraction feasibility audit

## 1. Executive verdict

**YELLOW_NEEDS_SIZEBOUND_REPAIR**

Reason: the extraction argument is logically standard and likely feasible, but the
current `BoundedSearchSolver` surface (separate per-output-bit circuits) makes
size accounting the critical unresolved item. The theorem is plausibly true with
an explicitly repaired `sizeBound` schedule and supporting composition lemmas.

---

## 2. Exact theorem surface

Current obligation symbol:

```lean
TreeMCSPConcretePrefixToSolverObligation
  (threshold : Nat → Nat)
  (encoding : TreeMCSPSearchWitnessEncoding threshold)
  (sizeBound : Nat → Nat)
  (obligations : TreeMCSPPrefixParserObligations threshold encoding) : Prop
```

Unfolded exactly (from `SearchMCSPTargetSurface.lean`):

```lean
Pnp3.ComplexityInterfaces.PpolyDAG
  (TreeMCSPPrefixExtractedLanguage threshold encoding obligations)
→ Nonempty
    (BoundedSearchSolver
      (TreeMCSP_C_DAG_Target threshold encoding sizeBound).problem
      (TreeMCSP_C_DAG_Target threshold encoding sizeBound).circuitClass
      (TreeMCSP_C_DAG_Target threshold encoding sizeBound).sizeBound)
```

Expanded components relevant to R1-C0:

- `TreeMCSP_C_DAG_Target ... .problem = treeMCSPSearchProblem threshold encoding`.
- `TreeMCSP_C_DAG_Target ... .circuitClass = C_DAG`.
- `TreeMCSPPrefixExtractedLanguage ... = PrefixExtensionLanguage obligations.parser`.

So the theorem shape is:

```lean
PpolyDAG (PrefixExtensionLanguage obligations.parser)
→ Nonempty (BoundedSearchSolver (treeMCSPSearchProblem threshold encoding) C_DAG sizeBound)
```

---

## 3. Bit-by-bit extraction plan

Assume `hDec : PpolyDAG (TreeMCSPPrefixExtractedLanguage threshold encoding obligations)`.

Extraction sketch:

1. **Prefix queries**
   - For input instance `x` at parameter `n`, and current prefix bits `p` of
     length `i`, build canonical well-formed query strings encoding
     `(tag, n, x, i+1, p ++ b, pad)` for `b=0,1` via parser convention.
   - Feed query to the decider family from `hDec`.

2. **Choose next bit**
   - Query branch `b=0`.
   - If decider says YES, choose bit `0`; else choose bit `1`.

3. **Output-bit circuits**
   - For each witness coordinate `j`, define output circuit `Out_j` over `x` that
     recursively simulates the above branch-choice process up to depth `j+1` and
     outputs the chosen bit.
   - Nonuniform constants include parser format and fixed wiring templates.

4. **Correctness on promised inputs**
   - Promise gives existence of at least one valid witness for relation.
   - Prefix-extension semantics ensure at each stage at least one branch remains
     extendable.
   - Branch rule preserves extendability invariant.

5. **Malformed inputs**
   - Solver never needs malformed external strings; it fabricates canonical
     query strings internally.
   - Parser-reject behavior is only needed to show language semantics are clean;
     solver correctness depends on well-formed internal encodings.

---

## 4. Size ledger

Let:

- `S_dec(n)` = size of decider circuit at ambient length `M(n)`.
- `W(n)` = witness length (`problem.witnessBits n`).
- `E(n,j)` = encoding overhead to build prefix query at stage `j`.
- `Sel(n,j)` = branch selection/control overhead.

Per-output-bit circuit size prototype:

\[
S_{out}(n,j) \lesssim S_{dec}(M(n)) + E(n,j) + Sel(n,j) + R(n,j)
\]

where `R(n,j)` is recomputation overhead for earlier branch decisions.

Critical cases:

1. **If naive recomputation**
   - `R(n,j)` can scale with `j`.
   - Late bits may require up to `O(W(n) * S_dec(M(n)))`-style overhead.

2. **If sharing available only inside each `Out_j` DAG**
   - Could reduce constants but still may keep linear-in-`j` growth.

3. **If cross-bit sharing were modeled**
   - Global solver graph could be smaller, but current
     `BoundedSearchSolver` type does not model cross-output DAG sharing.

Consequences for `sizeBound`:

- Usually **not safe** to assume “same polynomial as decider” without proof.
- Likely need a repaired schedule dominating composed extraction circuits.
- Possible acceptable form: polynomial in `M(n)` multiplied by low-order factor
  depending on `W(n)` (still polynomial if `W` is polynomial in `M`).
- Requires explicit composition theorem/lemma in `C_DAG` model.

Status:

- **Too small risk:** if `sizeBound` intended near raw decider size.
- **Too large risk:** if inflated bound weakens downstream lower-bound meaning.
- Therefore: **repair with explicit ledger theorem is required**.

---

## 5. Nonuniformity audit

- Uses one decider family by input length (standard `PpolyDAG` witness).
- Construction is length-nonuniform, not per-instance-advice nonuniform.
- No per-input truth-table hardwiring is required by extraction design.
- Advice/constants are parser layout + circuit templates, fixed by length.
- Construction is compatible with legitimate nonuniformity discipline.

Verdict: nonuniformity model is acceptable if implemented as length-family only.

---

## 6. Correctness proof plan

Induction on prefix length `i`:

1. **Base (`i=0`)**
   - Empty prefix is extendable on promised input via problem totality.

2. **Step**
   - Assume prefix `p` length `i` is extendable: there exists witness `w` with
     `p` as prefix and `relation n x w`.
   - Then next witness bit `w_i` shows at least one branch (`p0` or `p1`) is
     extendable.

3. **Branch rule**
   - If `p0` is extendable, decider accepts branch-0 query; algorithm picks `0`.
   - Otherwise picks `1`; by previous item, branch-1 must be extendable.

4. **Invariant**
   - Chosen prefix remains extendable at each stage.

5. **Termination (`i = W(n)`)**
   - Full-length extendable prefix is a full witness; relation holds.
   - Output vector from `Out_j` circuits satisfies target relation.

This proves solver correctness assuming decider correctness and encoding lemmas.

---

## 7. Dependency on NP proof

Extraction does **not** require `TreeMCSPConcretePrefixNPObligation`.

- Needed for extraction: prefix semantics + decider in `PpolyDAG` + circuit
  construction + size bounds.
- Needed for final verified source packaging: NP obligation is separate and used
  later by `verifiedSource_of_treeMCSP_concrete_prefix_obligations`.

So expected answer is confirmed: **No NP dependency for extraction itself**.

---

## 8. Required closure lemmas

Exact lemma buckets needed for Lean closure:

1. **C_DAG composition/closure under wiring**
   - Need: compose decider with query-encoder gadgets and selectors.
   - Status: **missing/partial** (adapter exists; extraction-specific closure
     lemmas not yet exposed in this surface).
   - Risk: **hard but local**.

2. **Hardwired constants and fixed bits injection**
   - Need: encode fixed tag/pad/prefix constants into DAG circuits.
   - Status: **likely existing primitives in pnp3 DAG toolkit, not yet wrapped
     for this theorem**.
   - Risk: **moderate**.

3. **Parser/input embedding lemma**
   - Need: canonical query constructor corresponds to parser acceptance and to
     intended `PrefixInput` fields.
   - Status: **partially present** in `PrefixParserConvention` infrastructure,
     but extraction-ready wrapper lemma seems **missing**.
   - Risk: **moderate-to-hard**.

4. **Boolean control gadget (if/then/else via gates)**
   - Need: output `0/1` based on decider result.
   - Status: **existing primitives expected**, theorem surface not yet bundled.
   - Risk: **low**.

5. **Prefix projection and extension mechanics**
   - Need: formal relation between chosen branch history and query payload.
   - Status: **missing theorem packaging** (logic known, Lean lemma absent).
   - Risk: **moderate**.

6. **Size preservation/composition bounds**
   - Need: explicit upper bound transferring decider size + encoder overhead to
     each output circuit.
   - Status: **missing and critical**.
   - Risk: **high (main R1-C0 blocker)**.

Trust-root risk for these lemmas: **low** (all local engineering within existing
circuit semantics, no trust-root edits needed).

---

## 9. Hardwiring / NoGo audit

- **CircuitPHP D1 caution:** relevant as warning that global no-solver lower
  bounds are hard; does not invalidate conditional extraction theorem.
- **Formula-certificate refutation chain:** not on this dependency path.
- **Support-bound refutations:** not directly reused; still caution against
  accidental vacuity.
- **Iso-strong closure:** not directly in route, but warns against hidden
  quantifier/hardwiring loopholes.
- **Per-slice hardwiring hazard:** moderate risk if extraction implementation
  accidentally encodes per-instance tables; should enforce length-family-only
  construction.
- **Wrapper-field hazard:** reduced after L1 because obligations are explicit;
  remain vigilant not to re-hide extraction in structure fields.

Net result: no fatal conflict detected, but discipline required.

---

## 10. Recommended next Lean task

Exactly one L1 task:

**Prove a size ledger lemma for extraction output circuits in `C_DAG`.**

Why this one:

- correctness induction is standard and comparatively straightforward;
- size lemma is the decisive unresolved feasibility item for inhabiting
  `TreeMCSPConcretePrefixToSolverObligation` with meaningful `sizeBound`.

A good target shape:

- given decider polynomial bound + encoder overhead polynomial,
- produce explicit polynomial upper bound for each `Out_j`,
- derive admissible `sizeBound` schedule.

---

## Final R1-C0 snapshot

- Extraction feasibility (logical): **yes, plausible**.
- Dominant blocker: **per-output size accounting in current solver surface**.
- Route decision: **YELLOW_NEEDS_SIZEBOUND_REPAIR**.
