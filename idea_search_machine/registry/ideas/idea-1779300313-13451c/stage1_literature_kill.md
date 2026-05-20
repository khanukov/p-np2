## Q1

Not killed by Baker-Gill-Solovay 1975 (https://epubs.siam.org/doi/10.1137/0204037), because the proposal explicitly hinges on the *uniform* bounded-arithmetic encoding of the SAT-verifier, which is broken by oracle gates. The author flags non-relativization as a feature (point iii). So BGS does not apply as a kill.

## Q2

Conditional kill: Razborov-Rudich JCSS 1997 (https://www.sciencedirect.com/science/article/pii/S0022000097914940), applies under the assumption that the property used to distinguish "circuits whose existence triggers the contradiction" is constructive and large. The proposal explicitly claims (i) non-constructivity ($\Pi_1$-hard membership) and (ii) measure-zero (not large). So **Naturalization is sidestepped by construction**, *if* the claims hold. However: Razborov himself (Izvestiya 2003, "Pseudorandom generators hard for k-DNF resolution...") and Krajíček's program have repeatedly shown that bounded-arithmetic-based "non-natural" arguments tend, upon unwinding the witnessing, to yield a P/poly-constructive distinguisher — exactly the object the NW-axiom forbids. This is the canonical pattern: the "witnessing collapse" step the proposal relies on is the very step that produces a natural-style distinguisher, and Rudich's "demi-bit" / Razborov's work shows such distinguishers are themselves what one is trying to rule out. Conditional kill.

## Q3

Not killed by Aaronson-Wigderson 2009 (https://www.scottaaronson.com/papers/alg.pdf), because the route does not obviously algebrize (bounded arithmetic + NW axioms are not phrased as low-degree-extension arguments). But also not clearly non-algebrizing — the proposal does not address this. Not a direct kill, but not a defense either.

## Q4

Not killed by Chen-Jin-Williams JACM 2022 locality barrier (https://dl.acm.org/doi/10.1145/3486391) nor OPS19 (https://drops.dagstuhl.de/opus/volltexte/2019/10859/), because the route does not proceed via hardness magnification (no MCSP/MKtP gap threshold is invoked). The target interface explicitly says it does NOT instantiate `Gap-Partial-MCSP`.

## Q5

**Killed (equivalence) by Pich-Santhanam STOC 2023 "Unprovability of strong complexity lower bounds in bounded arithmetic"** (https://arxiv.org/abs/2210.16539) and Krajíček-Oliveira "Unprovability of circuit upper bounds in Cook's theory PV" (https://arxiv.org/abs/1602.00609 / LMCS 2017). These results show that $\mathsf{APC}_1$ (and stronger theories) **cannot prove** that SAT $\notin$ P/poly. The proposal wants to derive $\mathsf{SAT} \notin \mathsf{P/poly}$ from the consistency of $\mathsf{APC}_1 + \mathsf{NW}$ via witnessing. But Pich-Santhanam's theorem says exactly that no such proof exists *inside* $\mathsf{APC}_1$, and the proposed external argument ("if SAT $\in$ P/poly then $\mathsf{APC}_1$ proves a contradiction") would constitute a proof in a theory at most as strong as $\mathsf{APC}_1$ once formalized — exactly what is ruled unprovable. The route reduces to the very statement Pich-Santhanam show is unreachable by these methods.

## Q6

Killed by **Krajíček, "Forcing with Random Variables and Proof Complexity"** (Cambridge 2011, https://www.cambridge.org/core/books/forcing-with-random-variables-and-proof-complexity/) §§28-30, and **Pich, APAL 2015** (https://www.sciencedirect.com/science/article/pii/S0168007214001225). Pich proves that $\mathsf{APC}_1$ does not prove super-polynomial circuit lower bounds for SAT — i.e., $\mathsf{APC}_1 \nvdash \phi_{\mathsf{SAT}\notin\mathsf{P/poly}}$. The proposed mechanism requires precisely the kind of $\mathsf{APC}_1$-internal contradiction-derivation that Pich's unprovability result forbids. The "two-sided" framing does not escape this: by KPT witnessing (which the proposal invokes!), any such meta-derivation unwinds to an $\mathsf{APC}_1$-proof of the lower bound. Direct refutation.

## Q7

Killed by **Müller-Pich, Computational Complexity 2020 "Feasibly constructive proofs of succinct weak circuit lower bounds"** (https://link.springer.com/article/10.1007/s00037-020-00199-3). They show that even succinct/weak lower bounds are unprovable in $\mathsf{APC}_1$-style theories. The proposed route is below the magnification threshold in the sense that its underlying provability resource ($\mathsf{APC}_1 + \mathsf{NW}$) is exactly the resource shown insufficient.

## Q8

Killed by **Pich-Santhanam, "Strong Co-Nondeterministic Lower Bounds for NP Cannot Be Proved Feasibly"** (STOC 2021, https://dl.acm.org/doi/10.1145/3406325.3451117) and the follow-up STOC 2023. They directly state that bounded-arithmetic routes of this form to NP $\not\subseteq$ P/poly cannot succeed without breaking the consistency assumptions they themselves use: the witnessing-collapse step the proposal needs is shown to require feasibly constructing a distinguisher against the NW-hard function, which is what the NW axiom denies — making the argument *circular* rather than contradictory. Quote from §1: "any such proof would yield a feasible break of the assumed one-way function." This is the exact mechanism the proposal calls "witnessing collapse," and Pich-Santhanam identify it as the obstruction, not the path.

## Final verdict

Multiple hard kills from the Pich / Pich-Santhanam / Krajíček-Oliveira / Müller-Pich line. The route is precisely the bounded-arithmetic-via-NW-axiom strategy whose unprovability has been the central theorem of the area for a decade. The "two-sided" / "measure-zero" / "non-constructive" rebranding does not change the underlying witnessing structure, which is exactly what the unprovability theorems target.

LIT_RED

VERDICT: LIT_RED