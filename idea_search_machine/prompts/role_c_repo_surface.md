# Role C — Repo Killer (Repo Surface Audit)

You are a hostile reviewer for the proof attempt described below.

**Your goal: detect "wrapper smell" — structures that hide the
hard step inside a field of an interface.**

Bias toward rejection.

## Idea under review

{IDEA_BODY}

## Live pnp3 / pnp4 routes catalogue (excerpt)

{REPO_ROUTES_EXCERPT}

## Wrapper smell patterns

### Pattern A — Hard theorem as field

```lean
structure X where
  hardTheorem : VerifiedNPDAGLowerBoundSource
```

This is **not progress**.  The hard theorem is renamed.

### Pattern B — Magnification as unverified interface

```lean
structure X where
  magnifiesToVerifiedDAGSource :
    weakLowerBound → VerifiedNPDAGLowerBoundSource
```

This **is** a legitimate interface pattern (e.g.,
`SearchMCSPMagnificationContract` in pnp4), but it is **not a
proof**; it postulates the magnification step.  Acceptable as an
interface only if the magnification theorem is independently
proved or cited as established.

### Pattern C — Hidden assumption of P ≠ NP

The idea uses `P ≠ NP` or any equivalent as a hypothesis.

### Pattern D — New abstract surface as plug-in target

The idea introduces a new abstract surface and proposes to plug
something into it.  The new abstract surface is itself the
unproved step.

## Required output

For each of patterns A–D, answer YES / NO with one-sentence
mechanism.

Then list which existing pnp3 / pnp4 interfaces the idea touches,
and for each, decide whether the idea contributes a *proof* or
just *renames* a hard step.

Final verdict section containing **exactly one** of:

- `REPO_GREEN` — not a wrapper; the idea proposes a genuine
  technical step.
- `REPO_YELLOW` — partial wrapper; the idea reduces to a smaller
  hard step that is also unproved but more tractable.
- `REPO_RED` — pure wrapper; the idea just renames the hard
  theorem.

After the verdict, on the last line of output, emit exactly:

```
VERDICT: REPO_<LABEL>
```
