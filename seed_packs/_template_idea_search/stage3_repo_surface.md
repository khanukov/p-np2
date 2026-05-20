# Stage 3 — Repo Surface Audit (Role C)

**Role**: C — Repo Killer.

**Stance**: prosecutor.

## Worker prompt template

```
You are a hostile reviewer for proof attempt <X>.  Your job is to
check whether the idea is a "wrapper" — a structure that hides
the hard step inside a field of an interface.

Wrapper smell A:
  structure X where
    hardTheorem : VerifiedNPDAGLowerBoundSource

This is not progress.  The hard theorem is renamed.

Wrapper smell B:
  structure X where
    magnifiesToVerifiedDAGSource :
      weakLowerBound → VerifiedNPDAGLowerBoundSource

This is a legitimate interface IF the magnification step is
independently proved or cited as established.  Otherwise it is a
hidden assumption.

Verdict: REPO_GREEN / REPO_YELLOW / REPO_RED.

If REPO_RED: cite the wrapper pattern and the unproved hard step.
```

## Idea under review

(Copy thesis.)

## Wrapper smell checks

### A. Does the idea inline a hard theorem as a field?

(Check whether the proposed structure has any field whose type is
`ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
`NP_not_subset_PpolyDAG`, or any equivalent abstract source.)

**Result**: yes / no.  Mechanism: (...)

### B. Does the idea postulate magnification as an unverified interface?

(Check whether the proposed structure has any field whose type is
`A → VerifiedNPDAGLowerBoundSource` for some `A` that is itself
unproved.)

**Result**: yes / no.  Mechanism: (...)

### C. Does the idea inline a hidden assumption of P ≠ NP?

(Check whether the idea uses `P ≠ NP` or any equivalent as a
hypothesis.)

**Result**: yes / no.  Mechanism: (...)

### D. Does the idea introduce a new abstract surface and then propose to plug something into it?

(If yes, the new abstract surface is itself the unproved step; the
plug-in does not constitute progress.)

**Result**: yes / no.  Mechanism: (...)

## Existing pnp3 / pnp4 interfaces analysed

(For each interface the idea touches, decide whether the idea
contributes a *proof* or just renames a hard step.)

| Interface | Idea contributes | Verdict |
|---|---|---|
| `ResearchGapWitness` | (...) | proof / wrapper |
| `VerifiedNPDAGLowerBoundSource` | (...) | proof / wrapper |
| `<other>` | (...) | (...) |

## Final verdict

**`REPO_GREEN` / `REPO_YELLOW` / `REPO_RED`**

(If RED: cite the wrapper pattern and the unproved hard step.)
