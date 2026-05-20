# Stage 4 — Self-Attack Probe (Role D)

**Role**: D — Self-Attack Engineer.

**Stance**: prosecutor with constructive obligation.

This is the **adversarial step before formal proof**.  Role D
must attempt to break the idea by exhibiting concrete adversaries.

## Worker prompt template

```
You are a hostile adversary for proof attempt <X>.

Your goal: BREAK the idea by constructing a counterexample, a
trivial solver, or a collapse into a refuted route.  Bias toward
finding the break.

Apply each of the six attack modes:
1. Hardwiring witness.
2. Trivial solver.
3. Non-uniform bypass.
4. Syntactic rewrite.
5. Collapse into refuted route.
6. Hidden assumption of main theorem.

For each attack, attempt construction in writing
(pseudocode / parameter regime / specific instance).
DO NOT write Lean.

Report format:
- Per-attack result: BROKEN with witness | UNCLEAR | NOT_APPLICABLE.
- Overall verdict: SELF_GREEN / SELF_YELLOW / SELF_RED.

If SELF_RED: provide the breaking witness explicitly.
```

## Idea under review

(Copy thesis.)

## Six-point attack checklist

### Attack 1 — Construct a hardwiring witness

(Can a small circuit — e.g., truth-table hardwiring at the
canonical length — be exhibited that satisfies all the idea's
hypotheses?  If yes, the idea cannot produce a lower bound at
that parameter regime.)

**Witness candidate**: (...)

**Result**: BROKEN / UNCLEAR / NOT_APPLICABLE.

### Attack 2 — Construct a trivial solver

(Is the underlying problem already in P / NP / P/poly via a
trivial reduction?  If yes, the idea is targeting the wrong
complexity class.)

**Witness candidate**: (...)

**Result**: BROKEN / UNCLEAR / NOT_APPLICABLE.

### Attack 3 — Find a per-slice non-uniform bypass

(Does the idea require uniformity that the adversary can break
with non-uniform advice?  If yes, the proof fails non-uniformly.)

**Witness candidate**: (...)

**Result**: BROKEN / UNCLEAR / NOT_APPLICABLE.

### Attack 4 — Replace the witness with a syntactically equivalent rewrite

(Can a syntactic transformation reduce a "hard" witness to a
"trivial" one without changing semantics?  If yes, the idea's
syntactic distinction is illusory.)

**Witness candidate**: (...)

**Result**: BROKEN / UNCLEAR / NOT_APPLICABLE.

### Attack 5 — Check for collapse into an already-refuted route

(Does the idea, under any natural specialisation, reduce to a
route already in the refuted catalogue?  Cross-reference
`pnp3/Docs/BARRIER_CATALOGUE.md`.)

**Collapse candidate**: (...)

**Result**: BROKEN / UNCLEAR / NOT_APPLICABLE.

### Attack 6 — Check for hidden assumption of the main theorem

(Does the idea require, as a hypothesis somewhere, the very
statement it purports to prove?  Check the dependency graph
between hypothesis-side and conclusion-side surfaces.)

**Circularity candidate**: (...)

**Result**: BROKEN / UNCLEAR / NOT_APPLICABLE.

## Counting / dimension / symmetry sanity checks

(In addition to the six structured attacks, do the standard quick
sanity checks:)

- **Cardinality of YES set vs free-rows count** — is `|YES| <
  2^|free|` so that any selective property is impossible by
  counting?  (This catches the iso-strong failure mode.)
- **Trace-image cardinality vs covered labelings** — same family.
- **Dimension counting** for algebraic routes.
- **Symmetry counters** — does the route distinguish two
  instances that are symmetric under some action?

## Final verdict

**`SELF_GREEN` / `SELF_YELLOW` / `SELF_RED`**

(If SELF_RED: provide the breaking witness explicitly.  Include
which of the six attacks succeeded and the concrete construction.)
