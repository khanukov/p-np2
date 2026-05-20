# Final verdict


Idea id: `idea-1779302445-61377a`
Created: 2026-05-20T18:40:45+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:40:45+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:41:38+00:00 |

## Thesis

We propose separating **P from NP** via a **topological-entropy obstruction** on the space of **circuit-induced subshifts**. Associate to each polynomial-size circuit family $\{C_n\}$ a **multidimensional subshift of finite type (SFT)** $X_C \subseteq \Sigma^{\mathbb{Z}^2}$ whose admissible configurations encode space-time tableaux of $C_n$ on padded inputs (rows = circuit layers, columns = wire indices, with local SFT constraints enforcing gate-locality). For an NP-complete language $L$, the *acceptance subshift* $X_L$ — configurations encoding a verifier together with a witness — has a **specific topological entropy spectrum** controlled by the Hochman–Meyerovitch theorem: the set of entropies of $\mathbb{Z}^2$-SFTs is exactly the set of right-recursively-enumerable numbers, and these entropies are **computable invariants** that distinguish SFT classes.

**Cross-domain bridge (E14)**: We use the Hochman–Meyerovitch characterization of SFT entropies plus **Pavlov–Schraudner conjugacy invariants** to show that the "shift of finite type" associated to any P-circuit family has entropy in a strictly smaller recursive sub-class (call it $\mathcal{E}_P$) than the entropy of $X_{\mathrm{SAT}}$, which lies in $\mathcal{E}_{NP} \setminus \mathcal{E}_P$. The separation conclusion: if $\mathrm{P} = \mathrm{NP}$, the entropy of $X_{\mathrm{SAT}}$ would collapse into $\mathcal{E}_P$, contradicting an unconditional gap derivable from the **block-gluing distortion function** of the SAT subshift.

