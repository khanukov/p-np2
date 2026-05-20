## Q1

**Is this relativizing?**

Not killed by Baker-Gill-Solovay (https://epubs.siam.org/doi/10.1137/0204037), because the proposed approach encodes circuits as local SFT constraints via Aubrun–Sablik substitution systems, which inspect gate-level structure rather than treating circuits as oracle black-boxes. The mechanism is non-relativizing on its face. However, this also means the proposal must explain *how* it avoids relativization, which it does not do explicitly — but BGS itself doesn't kill it.

## Q2

**Is this natural?**

Conditional kill: Razborov-Rudich, "Natural Proofs," JCSS 55 (1997) (https://www.sciencedirect.com/science/article/pii/S0022000097914940), applies under the assumption that the "diagonalization on entropy values" implicitly defines a P/poly-constructible largeness property of truth tables. The proposal's "Kolmogorov-incompressibility flavor, but operating on entropy values" is precisely the kind of combinatorial-counting-via-disguise that Razborov–Rudich warns about: if the entropy-approximation gap can be detected by a polynomial-time test on truth tables of a large fraction of functions, the proof is natural and contradicts standard cryptographic assumptions (subexponential one-way functions / discrete log). The proposal gives no argument for non-naturalness, and the SFT entropy of a circuit family is a global, symmetric quantity over the function table — exactly the form that tends to be natural. This is a serious kill unless explicitly defused.

## Q3

**Is this algebrizing?**

Not killed by Aaronson-Wigderson (https://dl.acm.org/doi/10.1145/1490270.1490272), because tiling/SFT-local-rule arguments are syntactic/combinatorial and don't obviously go through low-degree extensions. Algebrization is not the natural barrier here.

## Q4

**Is this a known hardness-magnification dead end?**

Not killed by Chen et al. "Beyond Natural Proofs: Hardness Magnification and Locality" JACM 2022 (https://dl.acm.org/doi/10.1145/3538391) directly, because the proposal is not framed as magnification (it doesn't start from a weak lower bound and amplify). However, the *locality barrier* is highly relevant: the SFT encoding is by definition local (finite-range constraints), and Chen–Jin–Williams–Williams–Tell etc. show that local reductions / local circuit lower-bound techniques face systematic obstructions. The proposal's reliance on local SFT rules to enforce circuit semantics is exactly the locality-sensitive regime that magnification-locality barriers caution about.

Conditional kill: Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam, "Beyond Natural Proofs," applies under the assumption that the SFT-local rules constitute a "local reduction" in their formal sense.

## Q5

**Is this equivalent to a known open lower bound?**

Conditional kill: The reduction "right-r.e. real with polynomial-time approximation modulus" is essentially asking for a separation between time-bounded and unbounded Kolmogorov complexity / r.e.-reals — equivalent to MCSP-style or KT-complexity lower bounds (Allender et al., "Power from Random Strings," SICOMP 2006, https://epubs.siam.org/doi/10.1137/050628994; Hirahara FOCS 2018, https://ieeexplore.ieee.org/document/8555107). These are wide-open problems; reducing P vs NP to them is not progress, it's restatement.

## Q6

**Is this already proved impossible?**

Not found after search. Searched: "Hochman Meyerovitch complexity lower bound", "SFT entropy circuit complexity", "subshift finite type P vs NP". No direct refutation, because no one has seriously published this route.

## Q7

**Is this already known to be too weak?**

Conditional kill: Hochman–Meyerovitch (https://annals.math.princeton.edu/2010/171-3/p17) characterizes entropies as right-r.e. reals but the approximation rates in their construction are *not* polynomial — they involve heavy substitution/simulation overhead (towers of exponentials in many parameters). The claim that "if P=NP the entropy lies in polynomial-time-approximable right-r.e. reals" requires a quantitative refinement of HM that, to my knowledge, doesn't exist in published form. Gangloff–Sablik and follow-ups (e.g., Barbieri–Sablik, "The domino problem for self-similar structures") study computability of entropy but do not give the polynomial-rate dichotomy this proof requires. Without it, the obstruction is vacuous.

## Q8

**Is there a paper that directly says "this type of route does not work"?**

Killed (soft) by Razborov–Rudich JCSS 1997 plus the general meta-result of Aaronson–Wigderson (and the magnification-barrier literature, Oliveira–Pich–Santhanam CCC 2019, https://drops.dagstuhl.de/opus/volltexte/2019/10849/): any "global counting / entropy / Kolmogorov" measure of circuit families that is computable in P/poly from the truth table yields a natural property. The proposal's entropy is exactly such a global measure. Additionally, Hirahara–Santhanam ("On the Average-Case Complexity of MCSP," FOCS 2017+) implicitly shows entropy-of-trace style obstructions reduce to MCSP-type problems whose unconditional lower bounds are themselves the open question.

## Final verdict

The proposal faces (a) a strong naturalness concern (Q2) since SFT topological entropy is a symmetric, P/poly-evaluable functional of the circuit's truth table; (b) the locality barrier (Q4) since SFT constraints are local by construction; (c) a reduction-to-open-problem concern (Q5) since "polynomial-time approximable right-r.e. real" is essentially time-bounded Kolmogorov complexity, whose separation from unbounded versions is itself open and tied to MCSP; (d) a quantitative-Hochman–Meyerovitch gap (Q7) — the required polynomial-rate refinement of HM is not in the literature and is likely false as stated. The naturalness objection alone is a hard kill in the absence of an explicit non-naturalness argument, which the proposal does not provide.

LIT_RED

VERDICT: LIT_RED