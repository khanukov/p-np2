# Stage 1 — Literature Kill Audit (Role B)

**Role**: B — Literature Killer.

**Stance**: **prosecutor, not advocate**.

## Worker prompt template

```
You are a hostile literature reviewer for proof attempt <X>.

Your goal: KILL the idea using published literature.  An idea that
survives your review means you FAILED to kill it.  Bias toward
rejection.

Read the idea card carefully.  Then answer each of the eight
questions with one of:
- "Killed by [paper], because [mechanism]."  (cite URL)
- "Conditional kill: [paper], applies under [assumption]."  (cite URL)
- "Not killed by [paper], because [reason]."  (cite URL)
- "Not found after search."  (list searches attempted)

For each question, run at least 2 targeted searches.  Include URLs
for every cited paper.

Final verdict: LIT_GREEN / LIT_YELLOW / LIT_RED / LIT_UNKNOWN.

LIT_UNKNOWN is NOT a default.  Use it only when search was
genuinely impossible.
```

## Idea under review

(Copy thesis from Stage 1 idea card.)

## Eight kill questions

### Q1 — Is this relativizing?

(Would the proof work uniformly under arbitrary oracles?  Cite
Baker-Gill-Solovay 1975 if yes.)

**Searches run**:
- (list)

**Verdict**: (one of: killed / conditional / not-killed / not-found)

### Q2 — Is this natural?

(Does the technique exhibit a property that is constructive in
poly time on truth tables and large?  Cite Razborov-Rudich JCSS
1997 if yes.)

**Searches run**:
- (list)

**Verdict**: (...)

### Q3 — Is this algebrizing?

(Does the technique extend to algebraic oracles?  Cite
Aaronson-Wigderson ACM TOCT 2009 if yes.)

**Searches run**:
- (list)

**Verdict**: (...)

### Q4 — Is this a known hardness-magnification dead end?

(Locality barrier?  OPS19 threshold gap?  Cite specific papers.)

**Searches run**:
- (list)

**Verdict**: (...)

### Q5 — Is this equivalent to a known open lower bound?

(Would proving the idea imply an already-open conjecture?)

**Searches run**:
- (list)

**Verdict**: (...)

### Q6 — Is this already proved impossible?

(Direct refutation citation.)

**Searches run**:
- (list)

**Verdict**: (...)

### Q7 — Is this already known to be too weak?

(Even if successful, would the bound fail to produce `NP ⊄
P/poly`?)

**Searches run**:
- (list)

**Verdict**: (...)

### Q8 — Is there a paper that directly says "this type of route does not work"?

(Aggressive search for negative results.)

**Searches run**:
- (list)

**Verdict**: (...)

## Final verdict

**`LIT_GREEN` / `LIT_YELLOW` / `LIT_RED` / `LIT_UNKNOWN`**

(One label.  If LIT_YELLOW or LIT_RED, list the kill citations
explicitly.  If LIT_UNKNOWN, explicitly state what additional
resources are needed.)
