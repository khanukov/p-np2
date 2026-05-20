# Stage 4 — Self-Attack Probe (Role D, retroactive)

**Role**: D — Self-Attack Engineer.

**Stance**: prosecutor with constructive obligation.

This retroactive write-up demonstrates that **Stage 4 would have
killed the iso-strong route in ~30 minutes** via a single counting
observation in Attack 1.

## Idea under review

Canonical iso-strong forcing route (see `stage1_idea_card.md`).

## Six-point attack checklist

### Attack 1 — Construct a hardwiring witness

**Observation**: at canonical parameters `sYES = 1, sNO = 2`, the
YES set is exactly the set of partial truth tables consistent with
**some size-1 circuit** — i.e., a constant function (`true` or
`false`) or a single-input projection / negation.

The number of such size-1 circuits is bounded:

```
|Size1Candidate n| = 2 (constants) + 2 * n (projections / negations)
                  ≈ n + 2 (after simplification of the canonical encoding)
```

The induced trace image on any free-row set `D` has cardinality at
most `n + 2`.

The free-row set has size `2^|free rows|` possible Boolean
labelings.  At canonical input length `partialInputLen p = 2 ·
2^m`, the free-row cardinality `|free rows| = 2^m - |D|` can be
arbitrarily large.

**Critical inequality**:

```
|trace image| ≤ n + 2  vs  |labelings on free rows| = 2^|free rows|
```

For `m ≥ ⌈log₂(n + 3)⌉ + 1`, we have `2^|free rows| > n + 2`, so
the trace image is **strictly smaller** than the labeling space.

By pigeonhole, some Boolean labeling is **outside** the trace
image.  Construct a partial table that agrees with `yYes` on `D`
but realises this missing labeling on free rows.  This partial
table:

- is a valid encoding (trivially);
- agrees with `yYes` on `D` (by construction);
- is **not** in the YES set (because it does not match any
  size-1 circuit's trace, hence no size-1 circuit is consistent
  with it).

Therefore the iso-strong forcing condition is **violated** by
construction: there exists a valid encoding agreeing with `yYes`
on `D` that is not in YES.

**Witness construction** (sketch):

```
Given:
  yYes : YES-side partial truth table (consistent with some C₀ : Size1Candidate)
  D    : coordinate set with |free rows| > log₂(n + 2)
Construct:
  label : free_rows → Bool, chosen outside the trace image of
          Size1Candidate restricted to free rows
  z : partial truth table defined by
        z(j) = yYes(j)        if j ∈ D
        z(j) = label(j)       if j ∈ free_rows
Then:
  z is a valid encoding agreeing with yYes on D, but z ∉ YES.
```

**Result**: **BROKEN**.  The iso-strong forcing condition is
immediately violated by trace counting.

### Attack 2 — Construct a trivial solver

(At canonical parameters, the Gap-Partial-MCSP language is in
P/poly via truth-table hardwiring — this was already noted by L0
#1388.  But this attack does not kill the iso-strong idea
directly; it kills the higher-level magnification claim, not the
specific forcing condition.)

**Result**: **NOT_APPLICABLE** to the iso-strong forcing
specifically; **BROKEN** for the broader "decide the language"
claim.

### Attack 3 — Find a per-slice non-uniform bypass

(Skipped — Attack 1 already kills the idea.)

**Result**: not investigated.

### Attack 4 — Replace the witness with a syntactically equivalent rewrite

(Skipped — Attack 1 already kills the idea.)

**Result**: not investigated.

### Attack 5 — Check for collapse into an already-refuted route

(At the time of the retroactive write-up, the iso-strong route
would have collapsed into "selective property of small YES sets
cannot satisfy a forcing condition over a large free space" — a
folklore counting observation in the same family as the natural-
proofs and locality barrier intuitions.)

**Result**: **partial collapse into folklore**; further
formalisation would have been formalising folklore.

### Attack 6 — Check for hidden assumption of the main theorem

**Result**: not investigated (Attack 1 already kills).

## Counting sanity check

`|Size1Candidate n| = n + 2`, well-known.

`|labelings on free rows| = 2^|free rows|`, well-known.

`n + 2 << 2^|free rows|` for any non-trivial `|free rows|`.

**Iso-strong forcing requires the trace image to *cover all*
Boolean labelings on free rows**, which is impossible by this
counting.

This 3-line observation is **the entirety of the kill**.  It is a
folklore counting argument that any complexity-theory researcher
would recognise within minutes.

## Final verdict

**`SELF_RED`** — killed at Attack 1 by trace counting.

## Breaking witness

See Attack 1 above.  Explicit construction:

```
m := any sufficiently large slice index (m ≥ ⌈log₂(n + 3)⌉ + 1)
n := input length at slice m
p := canonicalAsymptoticParams n
yYes := encodePartial of any size-1 truth table on D
D := any subset of rows with |free rows| > log₂(n + 2)
label : free_rows → Bool := chosen outside trace image of Size1Candidate
                            (existence by pigeonhole)
z := partial truth table agreeing with yYes on D and realising label
     on free rows
```

This `z` is a valid encoding agreeing with `yYes` on `D` but
`z ∉ YES`, so the iso-strong forcing condition fails.

## Retroactive lesson

This single counting observation — written in ~30 minutes of
mathematical work — would have replaced approximately **3 weeks
of formal engineering** by the audit chain (L0 + L1 sessions 1–4
+ route closure).  The formalisation produced 700+ lines of
kernel-checked Lean that, in retrospect, are a verbose proof of
this folklore observation.

The pipeline's Stage 4 is therefore validated.
