## Q1

Not killed by Baker-Gill-Solovay 1975 (https://epubs.siam.org/doi/10.1137/0204037), because the proposer explicitly claims the obstruction is non-relativizing: topological entropy of a sofic shift is invariant under alphabet expansion. While the claim is unsubstantiated (oracles do more than expand alphabets — they alter local rules of $Y_C$, which Hochman–Meyerovitch entropy is highly sensitive to: a single rule change can flip entropy between r.e. classes), BGS itself is not a direct kill: the proposal at least nominally avoids diagonalization. Conditional kill at best.

## Q2

**Killed by Razborov-Rudich, JCSS 1997** (https://www.sciencedirect.com/science/article/pii/S0022000097914940), conditionally. The proposer claims non-naturality because the obstruction is "$\Pi_2$-arithmetical." But Razborov–Rudich's bar is largeness + constructivity of the *property of truth tables that the obstruction certifies*. The Step 4 contradiction argument routes through "$X_C$ simulates $X_{\mathsf{BDT}}$ entropically ⟹ rate is poly-r.e." This simulation predicate, when unfolded, *is* a property of the truth table of $C_n$ checkable in time polynomial in $2^n$ (one just enumerates legal patterns up to size $s(n)$ and counts), and it holds for a random function with high probability since entropy of "generic" shifts saturates. The non-naturality hand-wave does not survive: the *witness* the proof actually uses (polynomial rate of r.e. approximation) is itself a constructive, large property. See also Chow, "Almost-natural proofs" (2011, https://arxiv.org/abs/0805.1334) — escaping naturality requires concrete non-constructivity, not just high arithmetical complexity of an unused invariant.

## Q3

Not killed by Aaronson-Wigderson 2009 (https://www.scottaaronson.com/papers/alg.pdf), because no algebraic extension oracle is engaged with. But the proposal also gives no mechanism for surviving algebrization; the immunity claim of Step 0 is asserted, not proved. Not a direct kill.

## Q4

**Killed by Chen–Jin–Williams (and Oliveira–Pich–Santhanam) hardness magnification locality barrier**: Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality" (ITCS 2020 / JACM 2022, https://arxiv.org/abs/1911.08297). The proposed mechanism uses a *local* simulation of circuit evaluation as a 2D SFT with local rules of size $O(s(n))$ — this is exactly the "local reduction" pattern that the locality barrier formalizes as unable to yield super-polynomial lower bounds via known techniques. The entropy invariant is computed from local patterns of bounded radius, which fits the locality-barrier hypotheses precisely.

## Q5

Conditional kill: Jeandel–Vanier, "Turing degrees of multidimensional SFTs" (https://arxiv.org/abs/1108.1012), shows that entropy-rate-of-approximation classes for 2D SFTs correspond to $\Pi_1$ / r.e. Turing degrees — but does *not* refine these to polynomial-time rates. The "polynomial-rate right-r.e." class invoked in Step 3 is **not a class established in Hochman–Meyerovitch or Jeandel–Vanier**; Hochman–Meyerovitch characterize the r.e. reals achievable, with no resource-bounded refinement. So Step 3's "load-bearing claim" is equivalent to constructing a *resource-bounded* version of HM, which is an open problem (and likely equivalent to standard time-hierarchy/lower-bound questions). The proposal reduces P≠NP to an open problem of comparable depth.

## Q6

Not killed by direct refutation. No paper says "topological entropy cannot separate P from NP" verbatim.

## Q7

**Killed**: the simulation in Step 1 produces an SFT $Y_C$ with local rules of size $O(s(n))$, i.e., the *encoding alphabet grows with $n$*. This places the construction firmly in the "non-uniform local" regime that Oliveira–Pich–Santhanam, "Hardness magnification near state-of-the-art lower bounds" (CCC 2019, https://drops.dagstuhl.de/opus/volltexte/2019/10849/) identify as below the magnification threshold for any of the entropy-style invariants in the symbolic-dynamics literature, none of which have been shown to discriminate at $s(n) = n^{\omega(1)}$ vs $s(n) = 2^{O(n)}$. The Hochman–Meyerovitch characterization is *qualitative* (r.e. vs not) — it provides no quantitative gap usable for lower bounds.

## Q8

**Killed indirectly by Aaronson–Wigderson 2009 §6** and by Razborov, "Pseudorandom generators hard for $k$-DNF resolution and polynomial calculus resolution" (and the broader "barrier survey" line: Aaronson, "P=?NP", 2017, https://www.scottaaronson.com/papers/pnp.pdf, §6.2): any proof routing through a *recursive-theoretic invariant computable from local circuit structure* must explain how it avoids all three barriers; this proposal handwaves on relativization, fails naturality (Q2), is silent on algebrization, and lands in the magnification locality barrier (Q4). The pattern "import an undecidability result from another area" is specifically called out by Aaronson as historically unsuccessful (Post correspondence, word problems, Hilbert's 10th — none have yielded circuit lower bounds despite decades of attempts; see e.g., Mulmuley's GCT critique of such imports, https://www.cs.uchicago.edu/~mulmuley/papers/gct1.pdf).

Additionally, the entropy of a sofic shift encoding a polynomial-time-computable trace family is **rational** (entropies of finite-state sofic systems with computable transitions) — this is a folklore consequence of Lind–Marcus, *An Introduction to Symbolic Dynamics and Coding* (1995). Rational reals are trivially right-r.e. at polynomial rate. So Step 2's upper bound is correct but useless: ALL polynomial-trace shifts give rational entropy, and the proposer must then show $h^\ast$ is irrational with a specific non-poly-r.e. approximation rate — which Hochman–Meyerovitch does NOT guarantee for the *specific* tiling SFT $X_{\mathsf{BDT}}$. In fact, the BDT decision problem corresponds to an SFT whose entropy *is* computable (bounded domino tilings form a regular SFT with computable entropy via transfer-matrix methods — see Pavlov–Schraudner, https://arxiv.org/abs/1009.1750, on computability of entropies for specific SFT classes). Step 3 is therefore **false as stated**.

## Final verdict

Multiple hard kills:
- Q2: naturality argument is fake — the simulation witness is a large, constructive property.
- Q4: locality of the SFT encoding triggers the Chen et al. locality barrier.
- Q7: no quantitative entropy-rate gap exists in the cited literature; the construction is below known magnification thresholds.
- Q8: Step 3's load-bearing claim is contradicted by computability of entropy for tiling SFTs with bounded local rules (Pavlov–Schraudner and folklore from Lind–Marcus).

The Step 3 claim that $X_{\mathsf{BDT}}$ has non-poly-r.e. entropy approximation rate is unsupported and likely false.

`LIT_RED`

```
VERDICT: LIT_RED
```