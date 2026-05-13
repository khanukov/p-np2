# Source theorem size policy — Rule 4 expansion algorithm

This document specifies how `K_stmt` and `K_exp` are measured for a
candidate's `SourceTheorem_<id>` and `gap_from_<id>`. It is the operational
counterpart to **Rule 4** of `RESEARCH_CONSTITUTION.md`.

Limits (see also `spec/target.toml::[source_theorem_size]`):

- `K_stmt = 40` lines for the bare statement of `SourceTheorem_<id>`
- `K_exp = 200` lines for the dependency-closed expansion

Exceeding the limit produces `human-review-required`, **not** auto-reject.

---

## 1. Inputs

For each candidate `<id>`:

- `proof.lean` (and any siblings declared in `manifest.toml::[files]`)
- the elaborated AST of `SourceTheorem_<id>`
- the elaborated AST of `gap_from_<id>`

---

## 2. Measuring `K_stmt`

1. Locate `SourceTheorem_<id>` in the AST.
2. Render the statement (i.e. the type, not the term) with `pp.all := true`.
3. Apply normalization:
   - strip line comments (`-- ...`),
   - strip block comments (`/- ... -/`),
   - collapse runs of blank lines to a single blank,
   - normalize whitespace inside lines (no measurement of indentation).
4. Count remaining non-blank lines.

This count is `K_stmt_actual`. The check is

```
K_stmt_actual ≤ K_stmt
```

where `K_stmt` comes from `spec/target.toml::[source_theorem_size].K_stmt`.

`K_stmt` is intentionally tight: a source theorem that does not fit in 40
normalized lines is almost always smuggling a definition into its
statement.

---

## 3. Measuring `K_exp` — dependency closure

`K_exp` measures the **expanded statement**, including everything that the
candidate adds inside its package, but stopping at trusted boundaries.

### 3.1 Algorithm

```
Q := empty queue
seen := empty set

# Seed with the bodies and statements involved in the bridge.
enqueue Q with statement(SourceTheorem_<id>)
enqueue Q with statement(gap_from_<id>)
enqueue Q with body(gap_from_<id>)

while Q is non-empty:
  let node := pop(Q)
  for each identifier `r` referenced in `node`:
    if r is in `seen`: continue
    if r is at a trusted boundary (see §3.2): continue
    if r is candidate-local (see §3.3):
      seen.add(r)
      enqueue Q with statement(r)
      if r is one of:
        def, abbrev, structure, inductive, class, instance
      then enqueue Q with body(r)
    else:
      # External non-trusted reference — record but do not expand.
      seen.add(r)

return total normalized line count of all elements in `seen`
       plus the normalized line count of the seed statements.
```

Identifiers `r` may be `theorem`, `lemma`, `def`, `abbrev`, `structure`
fields, `inductive` constructors, `class` fields, `instance` declarations,
or `notation` macros that expand to candidate-local code.

### 3.2 Trusted boundary (not expanded, not counted)

References to any of the following are treated as opaque atoms; their
bodies are **not** counted in `K_exp`:

- `pnp3/Spec/FrozenSpec.lean::*` (once it exists)
- `pnp3/Complexity/Interfaces.lean::*` (the active trust root identifiers)
- the stdlib whitelist:
  - `Init.*`, `Std.*`, `Mathlib.Init.*`
  - `Nat.*`, `Int.*`, `Bool.*`, `Fin.*`, `List.*`, `Option.*`, `Sum.*`,
    `Prod.*`, `Vector.*`, `Array.*`, `String.*`
  - basic algebra/order classes from `Mathlib.Order.*`,
    `Mathlib.Algebra.Group.*`, `Mathlib.Algebra.Ring.*`
- the `Core` whitelist:
  - `Pnp3.Core.BitVec`
  - `Pnp3.Core.Family`
  - `Pnp3.Core.Bitstring`

If a candidate needs to use a non-whitelisted definition from `Core`, it
must be added to this list via a Foundational PR; otherwise it is counted.

### 3.3 Candidate-local

A reference is candidate-local if it is declared in any of:

- `pnp3/Candidates/<method>/<id>/**.lean`
- a file imported transitively by the candidate that itself lives under
  `pnp3/Candidates/`

Anything in `pnp3/Magnification/`, `pnp3/LowerBounds/`,
`pnp3/ThirdPartyFacts/`, `pnp3/RefutedPredicates/`, or
`pnp3/Magnification/AuditRoutes/` is **not** candidate-local. References
into those directories are flagged separately:

- references into `pnp3/RefutedPredicates/` or
  `pnp3/Magnification/AuditRoutes/` cause **automatic Rule 6 rejection**.
- references into `pnp3/Magnification/` (non-audit) or
  `pnp3/LowerBounds/` are recorded as **external trusted-but-flagged**;
  they are counted as one line each (their identifier reference) but their
  bodies are not expanded.

### 3.4 Normalization

Same as §2: strip comments, collapse blank runs, count non-blank lines.

### 3.5 Result

```
K_exp_actual := normalized_lines(seed_statements ∪ seen_candidate_local_bodies)
```

The check is

```
K_exp_actual ≤ K_exp
```

If `K_exp_actual > K_exp`, the candidate is `human-review-required`
(Rule 4). If the dependency closure references refuted-route code, the
candidate is **rejected** regardless of size (Rule 6).

---

## 4. Why dependency closure rather than surface lines

A bare statement that says

```
theorem SourceTheorem_X : MyBigPredicate F := ...
```

is one line. Without expansion, a candidate can hide an unbounded amount
of mathematical content inside `MyBigPredicate`. The closure algorithm
above forces those definitions to be counted unless they are in the
trusted boundary.

This is the same idea as Rule 16's `pp.all` rendering, applied to size
rather than to typeclass channels.

---

## 5. Verifier output contract

For each candidate, the verifier emits a JSON record of the form

```json
{
  "candidate_id": "...",
  "k_stmt_actual":           42,
  "k_stmt_limit":            40,
  "k_stmt_status":           "exceeded",
  "k_exp_actual":            173,
  "k_exp_limit":             200,
  "k_exp_status":            "ok",
  "trusted_boundary_hits":   ["Pnp3.Core.BitVec", "..."],
  "candidate_local_hits":    ["MyHelperPred", "..."],
  "external_flagged_hits":   [],
  "refuted_hits":            [],
  "size_status":             "human-review-required"
}
```

`size_status` values:

- `ok` — both checks pass.
- `human-review-required` — at least one of `K_stmt` or `K_exp` exceeded.
- `refuted-import` — Rule 6 fail. Candidate rejected.

---

## 6. PR 8 MVP implementation note

`scripts/check_source_theorem_size.sh` ships as a **grep-based MVP**
(`implementation_level = MVP_GREP_FALLBACK`), not the full BFS + `pp.all`
algorithm above. Concrete deviations:

1. **No `pp.all` rendering.** The MVP reads `proof.lean` directly,
   strips Lean comments via the same awk pass used by
   `check_refuted_predicate_usage.sh`, and counts non-blank source
   lines.

2. **`K_stmt_actual`** — found heuristically by matching
   `^[[:space:]]*(theorem|def|noncomputable def|abbrev|structure|inductive|class)[[:space:]]+<source.theorem>`
   and counting lines until the first subsequent line containing `:=`
   or `where` (inclusive). One-line definitions like
   `def F : Prop := True` count as 1.

3. **`K_exp_actual`** — count of all non-blank, non-comment lines in
   the entire candidate `proof.lean`. This is a **loose upper bound**:
   the MVP does not BFS through candidate-local references and does
   not stop at trusted-boundary identifiers. PR 15 replaces this with
   the full algorithm.

4. **Refuted-import detection** is delegated to PR 4a's
   `scripts/check_refuted_predicate_usage.sh`. The PR 4a guard's
   hard-fail zone already includes `pnp3/Candidates/`, so any bare
   refuted-predicate name in candidate-local code triggers a
   `refuted-import` reject at the verifier level. The size checker
   itself only reports `ok` / `human-review-required` /
   `missing-source-theorem`.

5. **Trusted-boundary exemption** (§3.2) is **not** implemented in
   MVP. References from `proof.lean` into `Spec/FrozenSpec.lean`
   (after PR 10), `ComplexityInterfaces`, `Core.*`, or stdlib are
   currently counted toward `K_exp_actual`. This will inflate the
   count for legitimate candidates that import standard
   infrastructure; PR 15 addresses this by AST-based reference
   tracing.

`spec_version` of this MVP: `0.1.0`. When PR 15 lands, bump to
`0.2.0` and remove this section.
