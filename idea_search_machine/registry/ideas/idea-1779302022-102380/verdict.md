# Final verdict


Idea id: `idea-1779302022-102380`
Created: 2026-05-20T18:33:42+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:33:42+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:34:31+00:00 |

## Thesis

I propose to separate **P from NP** (specifically, to lower-bound general Boolean circuit size for an NP-complete problem) by importing **Hochman–Meyerovitch undecidability of effective topological entropy for multidimensional subshifts of finite type (SFTs)** into the analysis of circuit families.

The bridge: encode a uniform family of Boolean circuits $\{C_n\}$ computing SAT-restricted-to-tiling-instances as a **2-dimensional sofic shift** $X_C \subseteq \Sigma^{\mathbb{Z}^2}$, where horizontal direction encodes circuit-layer evaluation and vertical direction encodes input variation. The **topological entropy** $h(X_C)$ of this shift is, by the Hochman–Meyerovitch realisation theorem (Annals of Math 2010), a $\Pi_1$-computable real iff the circuit family has bounded depth-vs-width tradeoff matching $\mathsf{P}$.

I conjecture (and the proof attempt aims to establish) a **rigidity dichotomy**: the sofic-shift entropy of any polynomial-size circuit family solving a tiling-encoded NP-complete language is forced (by Hochman's converse construction) to be a right-recursively-enumerable real strictly below a *threshold entropy* $h^\ast$, which is realised by the canonical 2D SFT encoding the NP-problem itself. Since the entropy of the problem-shift exceeds $h^\ast$, no polynomial circuit family can simulate it, yielding $\mathsf{P} \neq \mathsf{NP}$.

The cross-domain leverage: entropy is a *topological invariant of the symbolic dynamics* and is **immune to oracle relativization** (oracles change the alphabet but not the entropy class), and **non-natural** (the obstruction is a $\Pi_2$-arithmetical real, not a P/poly-checkable property of truth tables).

