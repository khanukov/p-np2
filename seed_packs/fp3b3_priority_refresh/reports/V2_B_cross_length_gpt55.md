# Route: V2-B cross-length coherence

Handle: gpt55

Report path: `seed_packs/fp3b3_priority_refresh/reports/V2_B_cross_length_gpt55.md`

Verdict: hold_for_nonvacuity

NOGO-000008 interaction: survives direct tautological-rewrite attack, because the current V2-B predicate is driven by semantic evaluation across adjacent lengths rather than by displayed OR/NOT/gate-count syntax.

Non-vacuity assessment: currently too narrow; cumulative parity is the only explicit honest family in the sketch, while OR, AND, and seededPrefixAnd do not satisfy the xor-successor equation.

Phase 2 theorem targets:

- `V2_B_not_support_cardinality_only`
- `V2_B_excludes_arbitraryLogWidthTT`
- `V2_B_nonvacuity`
- `V2_B_rewrite_invariant_or_rewrite_insensitive`
- Additional target recommended below: `V2_B_nonparity_honest_family_or_scope_bound`

Recommended next action: hold for a non-vacuity refresh before dispatching a full Phase 2 seed pack.

Commands run:

- `sed -n '1,220p' RESEARCH_CONSTITUTION.md`
- `python - <<'PY' ... outputs/nogolog.jsonl ... PY` for NOGO-000006 through NOGO-000009 review
- `sed -n '1,240p' spec/known_guards.toml`
- `nl -ba pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean | sed -n '1,220p'`
- `nl -ba pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_B_gpt55/Sketch.lean | sed -n '1,260p'`
- `nl -ba pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean | sed -n '1,235p'`
- `nl -ba pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean | sed -n '1,120p;240,310p'`
- `nl -ba pnp3/Barrier/NaturalProofs.lean | sed -n '1,120p'`
- `nl -ba pnp3/Barrier/Relativization.lean | sed -n '1,120p'`
- `nl -ba pnp3/Barrier/Algebrization.lean | sed -n '1,120p'`
- `./scripts/check.sh`

Scope violations: none.  This report is markdown-only; it makes no JSONL edits, no spec edits, no trust-root edits, no promotion, no endpoint claim, and no candidate-package claim.

## 1. Route definition

The current V2-B sketch is a Phase 1 predicate on an `InPpolyFormula` witness.  Its stated purpose is audit/infrastructure-level review, not lower-bound progress.  The file explicitly classifies the work as an infrastructure / side-track audit design sketch and says it does not claim an exclusion theorem, accepted guard, lower-bound source obligation, or final endpoint.

The formal surface has two components:

1. a CL-0 toy trace carrying a constant opcode, with `StrongCrossLengthCoherence` required of that toy trace; and
2. the real condition: for every length `n`, input `x : Bitstring n`, and appended bit `b`, the formula at length `n + 1` must evaluate on the extended input to the old formula value xor `b`.

Assessment:

- It is genuinely cross-length in the sense that it relates the semantics of `w.family n` and `w.family (n + 1)` on adjacent input lengths.  This is materially different from V2-A's local displayed formula tests.
- It is also parity-specific: the fixed successor equation is exactly the cumulative-parity recurrence.  The sketch admits parity by construction and does not currently display a second honest family.
- It is not merely a disguised syntactic property.  The decisive clause speaks about `FormulaCircuit.eval`, not gate counts, support counts, OR/NOT presence, or a chosen displayed normal form.  However, the CL-0 toy trace itself is weak: the constant `opCode`/trace requirement mostly names the intended recipe and does not by itself encode a rich family-construction law.  The semantic recurrence is doing almost all of the work.

Therefore V2-B should be read as: **semantic cross-length recurrence with a parity-shaped transition**, not as a general cross-length provenance theory yet.

## 2. NOGO interaction

### NOGO-000006 — arbitrary all-essential `ttFormula` payload

Status: survives provisionally / uncertain until Phase 2.

Reasoning: NOGO-000006 defeats filters that allow a fresh all-essential log-width truth table to be chosen independently at each length.  V2-B directly attacks that freedom by requiring every adjacent pair of lengths to obey one fixed xor-successor law.  A generic arbitrary-payload family will not satisfy this law.

The uncertainty is quantifier-level.  The Phase 2 theorem must state exactly which arbitrary-payload class is excluded.  If the class includes payload families intentionally chosen to follow the xor recurrence, the route cannot exclude them all.  The plausible target is therefore not “every all-essential payload is rejected,” but “the NOGO arbitrary fresh-payload mechanism is not admitted unless it collapses to the honest recurrence class.”

### NOGO-000007 — support-cardinality meta-barrier

Status: survives.

Reasoning: V2-B is not support-cardinality-only.  Two witnesses with the same support-cardinality profile can differ on the adjacent-length xor equation.  The proposed target `V2_B_not_support_cardinality_only` should make this explicit by constructing or specifying a same-support-profile pair separated by V2-B.

### NOGO-000008 — tautological rewrite attack

Status: survives direct attack.

Reasoning: NOGO-000008 lands against displayed syntax: adding `(x₀ OR NOT x₀)` changes the visible gate inventory while preserving the Boolean function.  V2-B's key clause is semantic evaluation across adjacent lengths.  A tautological conjunction that preserves `FormulaCircuit.eval` cannot change whether the xor-successor equation holds.  Thus the exact V2-A attack does not apply directly.

Caveat: this is only rewrite-insensitivity for tautological semantic rewrites.  If a different rewrite changes the cross-length embedding convention while preserving each length pointwise, Phase 2 must still show the recurrence is stated on a canonical extension map or is invariant under equivalent extension maps.

### NOGO-000009 — normalisation meta-barrier

Status: survives / not directly applicable.

Reasoning: NOGO-000009 defeats the normalize-then-filter patch for syntactic V2-A.1: eliminating the tautological seed also destroys V2-A's own syntactic non-vacuity witness.  V2-B does not rely on a bottom-up structural normaliser and does not need to preserve displayed OR/NOT gates, so that meta-barrier does not land directly.

Caveat: any future attempt to broaden V2-B by adding a syntactic normalisation pre-pass would re-enter the NOGO-000009 blast radius.  The safe path is to keep the theorem target semantic/rewrite-insensitive rather than normalize-then-syntactic.

## 3. Non-vacuity

Current risk: V2-B may admit only parity-like families.

### Explicit honest family

The sketch's explicit honest family is cumulative parity: `family n` computes xor of all `n` input bits, and the adjacent transition is `parity (x ++ [b]) = parity x xor b`.  This is a real nonempty witness class, so the predicate is not literally empty.

### OR / AND / seededPrefixAnd

- OR does not satisfy the xor-successor equation.  If the old OR value is `true` and `b = true`, the xor successor gives `false`, while OR at the next length remains `true`.
- AND does not satisfy the xor-successor equation.  If the old AND value is `true` and `b = false`, xor gives `true`, while AND at the next length gives `false`.
- seededPrefixAnd does not satisfy the xor-successor equation for the same reason as prefix AND.  The tautological seed is semantically neutral, so it cannot turn conjunction recurrence into xor recurrence.

### Is there a real honest family beyond parity?

Not currently shown.  Families of the form `parity xor constant`, or variants with a fixed base convention, may satisfy an affine xor recurrence, but those are still parity-like.  A broader useful family would need either:

1. a parameterized transition family with several opcodes and corresponding semantic laws; or
2. a formal statement that V2-B intentionally isolates one narrow honest recurrence and that this narrowness is still useful for the FP-3 audit question.

As written, the filter is probably too narrow for accepted guard status.  It is useful as anti-hardwiring evidence only after Phase 2 proves that its narrow honest class is intentional and not merely a parity singleton.

## 4. Phase 2 theorem targets

If the route is revived after a non-vacuity refresh, a future Phase 2 seed pack should target the following surfaces.

### `V2_B_not_support_cardinality_only`

Goal: prove that V2-B is not determined by the function `n ↦ |support (w.family n)|`.

Expected content: exhibit or specify two formula-family witnesses with the same support-cardinality profile such that one satisfies the V2-B recurrence and the other violates it.

### `V2_B_excludes_arbitraryLogWidthTT`

Goal: prove that the NOGO-000006 fresh-payload mechanism is rejected when adjacent payloads are allowed to vary independently.

Important quantifier discipline: do not claim rejection of every possible all-essential payload family.  State the theorem so it excludes the arbitrary fresh-pick adversary, or proves that any admitted log-width payload must satisfy the xor recurrence and hence is no longer arbitrary hardwiring.

### `V2_B_nonvacuity`

Goal: prove at least one honest admitted family.

Minimum acceptable witness: cumulative parity.  Stronger preferred witness: a non-parity family or a small family of opcode-indexed recurrences showing V2-B is not just a parity recognizer.

### `V2_B_rewrite_invariant_or_rewrite_insensitive`

Goal: prove that semantic tautological rewrites cannot change V2-B status.

Expected statement: if two witnesses compute pointwise-identical functions at every length, then the xor-successor clause holds for one exactly when it holds for the other, assuming the same length-extension map.

### `V2_B_nonparity_honest_family_or_scope_bound`

Goal: resolve the non-vacuity risk directly.

Acceptable outcomes:

- produce a genuinely non-parity honest family admitted by a generalized V2-B recurrence; or
- prove and document that the current V2-B is intentionally parity-specific, then scope it as a narrow audit route rather than an accepted provenance filter.

## 5. Barrier analysis

### Natural Proofs

V2-B, as sketched, is a family/provenance relation on an `InPpolyFormula` witness plus a cross-length transition law.  It is not simply an extensional property of a single Boolean function at one input length.

However, the decisive xor clause is extensional at the family level: it depends only on the sequence of Boolean functions computed by `w.family n`, not on displayed syntax.  That helps with NOGO-000008 but moves the route closer to classical natural-property concerns if the property is later made constructive, large, and useful against a broad circuit class.

Current assessment: natural-proof risk is uncertain.  The route may avoid the exact V2-A representation-sensitivity story, because it is intentionally semantic; but a semantic family property requires a future barrier certificate explaining why it is not a large constructive property of hard functions.

### Relativization

The recurrence itself appears to relativize: an oracle version of the same length-extension law can be stated without changing the equation.  That is not fatal for an audit filter, but it means V2-B should not be advertised as a non-relativizing lower-bound method.

Current assessment: relativization risk is medium.  A Phase 2 report should either keep V2-B explicitly audit-only or provide an oracle-separation/bypass witness in the repository's abstract relativization interface.

### Algebrization

No obvious algebraic ingredient appears in V2-B.  The recurrence is Boolean xor across adjacent lengths and could likely be represented algebraically over GF(2), which may make it algebrization-friendly rather than algebrization-resistant.

Current assessment: algebrizing risk is uncertain-to-medium.  Nothing in the current sketch demonstrates an algebrization bypass.

## 6. Recommendation

Recommendation: hold_for_nonvacuity.

Rationale: V2-B survives the direct NOGO-000008 and NOGO-000009 attacks because it is semantic and cross-length rather than displayed-syntax-driven.  It also plausibly survives NOGO-000007 because support cardinality alone cannot determine the recurrence.  But the current recurrence is so specifically xor/parity-shaped that it risks being a parity-only filter.  Dispatching Phase 2 immediately would likely spend effort proving a narrow parity recognizer rather than a robust provenance filter.

Suggested next seed pack, after a short non-vacuity refresh: `fp3b3_5_v2_b_cross_length_nonvacuity_refresh`.

Slot decomposition if revived:

1. T1 — formalize semantic recurrence core and same-function rewrite invariance.
2. T2 — prove parity non-vacuity and search for non-parity admitted families.
3. T3 — prove not support-cardinality-only via same-profile separation.
4. T4 — attack NOGO-000006 with careful quantifiers around arbitrary fresh payloads.
5. T5 — barrier note for Natural Proofs / relativization / algebrization.
6. T6 — operator review deciding between dispatching a full Phase 2 or archiving V2-B as a parity-specific audit artifact.
