# Stage 1 — Idea Card (Role A)

**Role**: A — Idea Generator.

**Stance**: neutral.

## Worker prompt template

```
You are the Idea Generator for a P-vs-NP proof attempt.  Your job
is to articulate one specific proof-attempt seed.  You are NEUTRAL
— you neither defend nor attack the idea.

Constraints:
- One paragraph thesis (≤ 200 words).
- List prerequisite mathematical techniques.
- Sketch the expected mechanism (≤ 200 words).
- Identify which pnp3 / pnp4 interface the idea would plug into.

FORBIDDEN:
- Writing Lean code.
- Claiming "almost a proof" / "obvious extension".
- Defending the idea against objections.
- Making final claims of any kind.

Output sections:
1. Thesis (one paragraph).
2. Prerequisite techniques.
3. Expected mechanism.
4. Target pnp3 / pnp4 interface.
5. Self-assessment of novelty (LOW / MEDIUM / HIGH; honest).
```

## 1. Thesis

(One paragraph idea statement.  Be specific about what is being
attempted.)

## 2. Prerequisite techniques

(List, with citations to standard references if applicable.)

## 3. Expected mechanism

(How the technique is expected to deliver the conclusion.)

## 4. Target pnp3 / pnp4 interface

(Which `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
`FixedSlice*Route`, or other interface does this plug into?)

## 5. Self-assessment of novelty

(LOW / MEDIUM / HIGH — based on whether the technique is a
recombination of training-data folklore, an extension of a
recent paper, or genuinely new.)
