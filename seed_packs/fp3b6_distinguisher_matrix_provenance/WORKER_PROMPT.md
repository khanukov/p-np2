# Worker prompt — fp3b6 distinguisher-matrix provenance (Round 1: D1 + D5)

> Send this entire file as the prompt body to one independent
> research engineer (human + LLM session) per slot.  Workers
> self-pick `<YOUR-HANDLE>` and ONE slot.  Multiple workers may
> attack the same slot; the cleanest output is merged at
> audit-review.  This is **Round 1**: only D1 and D5 are open
> (parallel-dispatchable, no inter-deps).  D2 / D3 / D4 are
> gated on D1 landing.

---

You are working on slot `D1` or `D5` of seed pack
`fp3b6_distinguisher_matrix_provenance/`.  The seed pack
defines the audit-route Phase-1 sketch for a distinguisher-matrix
provenance filter, opened per fp3b5 strategic audit Family A
recommendation as the post-V2-closure FP-3b.2 design candidate.

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN before you start.

## 1. Required reading (in order)

1. `seed_packs/fp3b6_distinguisher_matrix_provenance/README.md` —
   pack goal, slot decomposition, allowed/forbidden scope.
2. **Strategic audit that opened this pack** (load-bearing):
   `seed_packs/fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md`
   — especially §2 closure constraints (C1-C8) and §3.1 Family A
   analysis.
3. **Source first-move report** (load-bearing):
   `seed_packs/first_move_search_2026/reports/gpt55/Q4_distinguisher-matrix-magnification.md`
   — especially §3 embedding sketch, §4 NOGO self-attack, §5
   barrier self-attack, §7 follow-up seed pack outline (the
   recommended slot decomposition this pack implements).
4. **V2 closure trail (anti-evidence motivation):**
   * `seed_packs/fp3b3_provenance_filter_v2_design/operator_reviews/v2_family_closure_retrospective.md`
     — why syntactic-only filters are CLOSED.
   * `outputs/nogolog.jsonl` lines 7, 8, 9 (NOGO-000007, 000008,
     000009) — the closure constraint set.
5. **NOGO-000006 specifically** (the adversary D3 will eventually
   resist):
   * `outputs/nogolog.jsonl` line 6.
   * `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/` —
     the formal Lean adversary family.
6. **Trust root** (READ-ONLY):
   * `pnp3/Complexity/Interfaces.lean` for `FormulaCircuit`,
     `eval`, `support`, `Bitstring`.
   * Mathlib `Matrix`, `Finset`, `Bool`-arithmetic.
7. **RESEARCH_CONSTITUTION.md** Rules 0, 1, 9, 12, 16.

## 2. Slot list — Round 1 (pick ONE)

**Dependency DAG:**

```text
D1 (matrix primitives, Lean)        D5 (literature parameter table, MD)
        |                                   ↓
        +----> Round 2 D2, D3
                 |
                 +----> Round 3 D4
```

D1 and D5 are independent; pick whichever fits your skill set.

| Slot | File | Goal | Depends on |
| ---- | ---- | ---- | ---------- |
| D1 | `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_<HANDLE>/MatrixPrimitives.lean` | `SparseDistinguisherMatrix`, `fingerprint`, support-card lemmas, sparsity-preservation, basic compute lemmas. | — |
| D5 | `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_literature_parameter_table_<HANDLE>.md` | Markdown table mapping audit-skeleton parameters to Atserias-Müller 2025 + Chen-Hirahara-Oliveira ITCS 2020 + Oliveira-Pich-Santhanam + Chen-Jin-Williams + Cheraghchi-Hirahara-Myrisiotis-Yoshida parameters. | — |

D2 / D3 / D4 are NOT in this dispatch round; do not pick them.

## 3. D1 — Matrix primitives (Lean)

### 3.1 Definitions required

```lean
namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_<HANDLE>

/-- Boolean matrix with `m` rows indexed by `Fin m` and `n`
columns indexed by `Fin n`. -/
abbrev BoolMatrix (m n : Nat) : Type := Fin m → Fin n → Bool

/-- Support of row `i`: the set of columns where row `i` has
value `true`. -/
def rowSupport {m n : Nat} (D : BoolMatrix m n) (i : Fin m) :
    Finset (Fin n) :=
  Finset.univ.filter (fun j => D i j = true)

/-- Support of column `j`: the set of rows where column `j` has
value `true`. -/
def colSupport {m n : Nat} (D : BoolMatrix m n) (j : Fin n) :
    Finset (Fin m) :=
  Finset.univ.filter (fun i => D i j = true)

/-- Sparse distinguisher matrix predicate: every row has
support ≤ k and every column has support ≤ k. -/
def SparseDistinguisherMatrix {m n : Nat} (k : Nat)
    (D : BoolMatrix m n) : Prop :=
  (∀ i : Fin m, (rowSupport D i).card ≤ k) ∧
  (∀ j : Fin n, (colSupport D j).card ≤ k)

/-- XOR-of-AND fingerprint map: `(fingerprint D x) i = XOR over
`j ∈ rowSupport D i` of `x j`. -/
def fingerprint {m n : Nat} (D : BoolMatrix m n)
    (x : Pnp3.ComplexityInterfaces.Bitstring n) :
    Pnp3.ComplexityInterfaces.Bitstring m :=
  fun i => (rowSupport D i).foldr (fun j acc => xor (x j) acc) false
```

### 3.2 Required lemmas

```lean
/-- Sparsity is symmetric under transpose. -/
theorem sparseDistinguisherMatrix_transpose
    {m n k : Nat} (D : BoolMatrix m n)
    (h : SparseDistinguisherMatrix k D) :
    SparseDistinguisherMatrix k (fun j i => D i j)

/-- Fingerprint output length matches the matrix row count. -/
theorem fingerprint_codomain {m n : Nat} (D : BoolMatrix m n) :
    ∀ (x : Pnp3.ComplexityInterfaces.Bitstring n),
      (fingerprint D x : Fin m → Bool) -- type matches
   -- (this is automatically true; the lemma is just a sanity check)

/-- Fingerprint bit `i` depends only on `rowSupport D i`. -/
theorem fingerprint_local {m n : Nat} (D : BoolMatrix m n)
    (i : Fin m)
    (x y : Pnp3.ComplexityInterfaces.Bitstring n)
    (h : ∀ j ∈ rowSupport D i, x j = y j) :
    fingerprint D x i = fingerprint D y i

/-- Empty matrix (all false) yields constant-false fingerprint. -/
theorem fingerprint_zero {m n : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) :
    fingerprint (fun _ _ => false) x = fun _ => false

/-- Sparsity of the zero matrix at any k. -/
theorem sparseDistinguisherMatrix_zero
    {m n : Nat} (k : Nat) :
    SparseDistinguisherMatrix k
      ((fun _ _ => false) : BoolMatrix m n)

end V_<HANDLE>
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
```

### 3.3 Optional helpers (allowed but not required)

* `rowSupport_card_eq_finsetCard`: connection to standard
  `Finset.card`.
* `fingerprint_xor`: fingerprint distributes over XOR of input
  bitstrings.
* Concrete small-matrix examples (e.g., 2×2 identity, 4×4 parity).

### 3.4 Critical scope rules

* **No `Classical.choose`**, no truth-table reconstruction, no
  `ttFormula`.
* **No `sorry` / `admit` / `axiom` / `opaque`** in committed
  Lean.
* **No editing existing audit-route or trust-root modules.**
* **No `lakefile.lean` edits** to remove or rename existing
  modules.  ADDING a new module under `Glob.one` is allowed
  and expected.
* **Wire the new module** into `lakefile.lean` under the
  existing `Glob.one ...` list pattern.
* **Optional smoke** at
  `pnp3/Tests/AuditRoutes_DistinguisherMatrix_<HANDLE>_Smoke.lean`
  allowed but not required.

### 3.5 Expected LOC

150-250 (definitions + lemmas, no proofs of substantive
theorems — those are D2/D3).

## 4. D5 — Literature-to-parameter table (Markdown)

### 4.1 Deliverable

A markdown file at
`seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_literature_parameter_table_<HANDLE>.md`
containing:

### 4.2 Required sections

**Section A — Parameter list.**

Enumerate the parameters of the audit skeleton in this pack:

* `n` — number of input variables.
* `m` — fingerprint output length.
* `k` — row/column support bound.
* `r` — separation radius (Hamming distance below which "near
  YES", above which "far NO").
* `<other parameters as introduced by D1>`.

**Section B — Per-paper parameter mapping.**

For each of the five Q4-cited papers, fill a table row:

| Paper | Cited parameters | Mapping to audit skeleton | Copied vs omitted | Reason |
| --- | --- | --- | --- | --- |

Papers:

1. Atserias-Müller 2025 (arXiv:2503.24061).
2. Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam ITCS 2020
   (arXiv:1911.08297; DOI 10.4230/LIPIcs.ITCS.2020.70).
3. Oliveira-Pich-Santhanam, Theory of Computing 17(11), 2021.
4. Chen-Jin-Williams FOCS 2019 (DOI 10.1109/FOCS.2019.00077;
   ECCC TR19-118).
5. Cheraghchi-Hirahara-Myrisiotis-Yoshida STACS 2021 (DOI
   10.4230/LIPIcs.STACS.2021.23; journal DOI
   10.1007/s00224-022-10113-9).

**Section C — Deliberate omissions.**

What does the first audit pass deliberately NOT formalise from
the magnification literature?  Why?  Expected items:

* Full magnification theorem statement (years, not months —
  per Q4 §3).
* Specific MCSP / Gap-MKtP target promise problem (kept
  abstract in audit skeleton).
* Threshold-tight parameter values (audit uses generic bounds
  ≤ k, ≤ m without committing to specific magnification-strength
  thresholds).
* Distribution-specific average-case statements.
* Concrete promise gap parameters.

**Section D — Citation verification.**

For each cited paper, confirm:
* DOI / arXiv ID exists and resolves (LLM workers MUST verify;
  hallucinated citations are a HARD failure).
* Title and author list as cited in Q4 are correct.
* Year and venue are correct.

If a citation cannot be verified, REMOVE it from the table and
flag in Section D as `[VERIFICATION_FAILED]` with the reason.
Do NOT include unverified citations.

### 4.3 Critical scope rules for D5

* **Markdown only.**  No Lean.
* **No new claims about magnification.**  Only document existing
  literature parameters.
* **No promotion language.**  No "this proves...", no "this
  unlocks...".  Only "this paper uses parameter X with value Y".
* **Honest about uncertainties.**  If a paper's parameter
  mapping is ambiguous, state "ambiguous" and note possible
  interpretations.

### 4.4 Expected LOC

200-400 markdown lines.

## 5. File-path convention

Pick `<YOUR-HANDLE>` (short, lowercase, alphanumeric — e.g.
`gpt55`, `claude46`, `sonnet46`).  Multiple workers can attack
the same slot in parallel — each lands its own attempt under
its handle.

For D1, your files go to:

```
pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_<HANDLE>/
```

Wire each new module into `lakefile.lean` under the existing
`Glob.one ...` list.

For D5, your file goes to:

```
seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_literature_parameter_table_<HANDLE>.md
```

## 6. Allowed / forbidden scope

See seed pack `README.md` §4.  Hard rules summary:

* **No trust-root edit.**
* **No editing any audit-route module** outside
  `DistinguisherMatrixProvenance/V_<HANDLE>/`.
* **No `outputs/nogolog.jsonl` / `outputs/attempts.jsonl` /
  `spec/known_guards.toml` writes.**
* **No `Candidates/` creation.**
* **No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness`
  / final endpoint / P ≠ NP language.**
* **No FP-4 bridge work.**
* **No `sorry` / `admit` / `axiom` / `opaque` / `Fact` /
  typeclass-payload in committed Lean** (Rules 1, 16).
* **No `Classical.choose` in matrix-primitive definitions.**
* **No truth-table reconstruction.**

## 7. Slot acceptance criteria

* **D1 complete** when: build green, check.sh green, all
  required definitions + lemmas land, no forbidden constructs.
* **D5 complete** when: parameter table is filled, every cited
  paper has a verified identifier, deliberate omissions are
  documented, scope-rule discipline is honoured (no claims
  beyond literature documentation).

## 8. Failure mode — structured failure report

If you cannot complete the slot (Lean errors you can't resolve;
literature you can't verify; obstruction you discover), ship
a structured failure report at:

```
seed_packs/fp3b6_distinguisher_matrix_provenance/failures/<SLOT>_<HANDLE>.md
```

with EXACTLY four sections (per pack README §6):

1. **What was attempted.**
2. **Where it broke.**  Lean error verbatim, or precise
   obstruction.
3. **Local vs global obstruction.**
4. **What an integrator must know.**

For D5, "global obstruction" would mean: "the Q4-cited literature
does not actually support the audit skeleton as described";
this would invalidate the fp3b5 strategic audit's Family A
recommendation and trigger cascade to Family B.

## 9. Output format (response back to operator)

```
Slot: D1 | D5
Handle:
Branch:
Commit:
File(s):

Outcome:
  LANDED | FAILURE_REPORT

If LANDED:
  Lean module LOC (D1):
  markdown LOC (D5):
  key definitions / lemmas (D1):
  key citations verified (D5):
  smoke test added (D1, optional): YES/NO

If FAILURE_REPORT:
  failure file path:
  local/global classification:
  shortest explanation:

lake build: green/red
./scripts/check.sh: green/red

Scope violations:
  none | list
```

## 10. Work style

* Do not ask the operator questions.  Ship results or a
  structured failure report.
* Do not stop on `needs_review`.
* Do not invent additional infrastructure beyond what §3 (D1)
  or §4 (D5) requires.
* Cite specific line numbers when referencing existing Lean
  code or other repo files.
* For D5: **verify every citation** before including it.  A
  hallucinated DOI is worse than an omitted paper.
* If the slot you picked seems to require trust-root edits
  or editing existing audit-route modules, your design
  approach is wrong — rethink, OR ship a failure report
  explaining why the slot's spec is incompatible with the
  allowed scope (this would be a Local design-spec failure,
  operator will re-spec).

The pack's research goal is the **anti-collapse theorem in D3**
(Round 2).  D1 and D5 are the foundation; the meaningful test
of the design idea is D3.  Honour the foundation discipline:
clean primitives in D1 + verified parameter table in D5
together make D3 (and D2 + D4) much faster to land.
