# Final verdict


Idea id: `idea-1779302349-14adb7`
Created: 2026-05-20T18:39:09+00:00
Status: **CLOSED_AT_STAGE_1**

## Stage outcomes

| Stage | Verdict | Model | Mock | Ran at |
|---|---|---|---|---|
| stage0_generate | GENERATED | claude-opus-4-7 | no | 2026-05-20T18:39:09+00:00 |
| stage1_literature_kill | LIT_RED | claude-opus-4-7 | no | 2026-05-20T18:39:55+00:00 |

## Thesis

We propose to separate **P from NP** (specifically, to prove a superpolynomial circuit lower bound for an NP-complete problem on a structured input distribution) by importing the **Hochman–Meyerovitch theorem** on computable entropies of multidimensional subshifts of finite type (SFTs) into circuit complexity via a novel **"circuit-as-tiling" correspondence**.

The bridge is **E14 (topological/symbolic dynamics)**. The key idea: a Boolean circuit of size $s$ computing a function $f: \{0,1\}^n \to \{0,1\}$ can be encoded as a finite local rule generating a 2D SFT $X_C$, whose **topological entropy** $h(X_C)$ equals (up to normalisation) the log-density of admissible computation histories. Hochman–Meyerovitch (Annals 2010) characterise exactly which real numbers arise as entropies of 2D SFTs: they are precisely the right-recursively-enumerable reals in $[0,\infty)$, and entropy is **not** computable in general — it is $\Pi_2$-complete.

Our separation strategy: define an NP-complete tiling-flavoured language $L$ (a variant of bounded periodic tiling) such that any polynomial-size circuit family $\{C_n\}$ deciding $L$ would force the entropy $h(X_{C_n})$ to converge to a **computable** real at a polynomial rate. Hochman–Meyerovitch + a quantitative refinement (Gangloff–Sablik 2021, *Ergodic Theory Dyn. Syst.*) imply that polynomial-rate-computable SFT entropies form a strict subclass — specifically, the rate of approximation cannot beat a logarithmic barrier coming from the $\Pi_2$ structure. This gives a non-relativizing, non-algebrizing, non-natural lower bound.

