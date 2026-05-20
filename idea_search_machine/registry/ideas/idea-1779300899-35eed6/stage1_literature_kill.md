## Q1

Not killed by Baker-Gill-Solovay 1975, because the proposal explicitly invokes the LPS quaternion-algebra construction whose correctness uses number-theoretic facts (Ramanujan conjecture/Deligne) that have no oracle analogue. The authors anticipate the relativization barrier and gate the argument on non-relativizing combinatorial geometry. https://epubs.siam.org/doi/10.1137/0204037

## Q2

Conditional kill: Razborov-Rudich JCSS 1997, applies under the assumption that the "VNC^1-unprovability" predicate, when unpacked through the KPT/Cook-Nguyen witnessing machinery, yields a P/poly-constructive, large property on truth tables. The authors claim measure-zero (singling out the LPS sequence) and non-constructivity (requires the expansion certificate). However, Razborov-Rudich applies to *any* combinatorial property usable to separate; the "single explicit sequence" framing is a known evasion attempt that Razborov himself (2003, "Pseudorandom generators hard for k-DNF resolution...") and Chow (2011) note is suspect: a lower bound for one explicit family typically generalizes to a large class via padding/closure. The "measure zero" claim is technically true but not sufficient — naturalization (Rudich's "natural-ization" lemma) often extracts a natural property from a putative single-family lower bound. https://www.sciencedirect.com/science/article/pii/S002200009791494X

## Q3

Not killed by Aaronson-Wigderson 2009, because the proposed argument is not arithmetization-based — it routes through bounded-arithmetic unprovability and combinatorial expansion, not low-degree extensions. However, Aaronson-Wigderson note that any technique avoiding both relativization and algebrization must use properties of circuits beyond their I/O behavior on arithmetized inputs; the proposal does not clearly identify such a property — the "VNC^1-unprovability token" is a meta-property, not a circuit-internal property. Not a direct kill but a warning. https://dl.acm.org/doi/10.1145/1490270.1490272

## Q4

**Killed by Chen, Jin, Williams, Wu, Yang et al. — the "locality barrier" line** (Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality," ITCS 2020 / JACM 2022), because the proposal's core move — transferring a *proof-complexity* fact about Tseitin/expander formulas into a P/poly lower bound via a witnessing meta-theorem — is exactly the kind of "magnification-style" transfer the locality barrier rules out. Specifically, the locality barrier shows that current magnification theorems (including Pich-Santhanam-style unprovability-to-lower-bound transfers) cannot break through because the hypothetical small circuit and the "hardness witness" can be locally simulated, defeating the contradiction step. The Pich-Santhanam 2021 framework is precisely identified by Chen et al. as subject to this barrier. https://arxiv.org/abs/1911.08297 and https://dl.acm.org/doi/10.1145/3538391

Additionally killed by Oliveira-Pich-Santhanam (OPS19, CCC 2019) "Hardness magnification near state-of-the-art lower bounds," because the threshold-gap phenomenon shows that magnification triggers require lower bounds for *sparse/parameterized* problems just below known bounds, and the proposed Tseitin variant on expanders sits in a regime where magnification does not fire (Tseitin is dense and standard NP, not the MCSP/MKtP sparse regime where magnification applies). https://drops.dagstuhl.de/opus/volltexte/2019/10849/

## Q5

Conditional kill: The proposal is equivalent to proving that resolution-with-substitution lower bounds for Tseitin on LPS expanders lift to P/poly lower bounds. This is essentially the long-standing open problem of lifting proof-complexity lower bounds (Atserias-Müller, "Automating resolution is NP-hard," FOCS 2019; Garlik 2019) to circuit lower bounds — known open and known to require breaking either natural proofs or proof-complexity barriers (Razborov, "Pseudorandom generators hard for k-DNF resolution and polynomial calculus resolution," Annals of Math 2015). https://annals.math.princeton.edu/2015/181-2/p01

## Q6

Not killed by direct refutation. No paper proves NP ⊄ P/poly is impossible (it's open). No paper proves the specific transfer impossible, but Q4's locality barrier is the closest to impossibility for this class of techniques.

## Q7

Killed by OPS19 threshold-gap (https://drops.dagstuhl.de/opus/volltexte/2019/10849/) and by the observation in Müller-Pich, "Feasibly constructive proofs of succinct weak circuit lower bounds" (APAL 2020, https://www.sciencedirect.com/science/article/pii/S0168007220300087): the unprovability-of-circuit-lower-bounds technology of Pich-Santhanam yields *unprovability* results, not lower bounds themselves; reversing the direction (using unprovability to *get* lower bounds) is known to require additional assumptions (a "feasible interpolation for unary NP" that Pich's own paper does not establish unconditionally). The proposal openly conditions on this missing meta-theorem, which is the entire crux — so the route is below the magnification/transfer threshold as currently known.

## Q8

**Killed by Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam 2020 (ITCS/JACM 2022)** which explicitly says proof-complexity-to-circuit-lower-bound transfers via local/witnessing arguments — exactly the proposed route — face the locality barrier. https://arxiv.org/abs/1911.08297

Also: Pich-Santhanam 2021 themselves (https://ieeexplore.ieee.org/document/9719665) explicitly state their unprovability results do *not* yield circuit lower bounds and identify the gap the proposal claims to close as a major open problem requiring new techniques — the "witnessing meta-theorem à la Krajíček-Pich" the proposal conditions on is not established and is precisely what Pich-Santhanam flag as missing.

Krajíček's monograph "Proof Complexity" (Cambridge 2019, §21) explicitly discusses why VNC^1/V^0_2 unprovability of circuit lower bounds does not, by current methods, yield the lower bounds themselves — the witnessing direction is blocked.

## Final verdict

Multiple hard kills: Q4 (locality barrier directly targets this transfer pattern), Q7 (below current magnification threshold; the conditioning meta-theorem is the open problem itself), Q8 (the cited Pich-Santhanam framework itself disclaims the implication being assumed). The proposal's escape clauses (measure-zero, non-relativizing via LPS number theory) do not address the locality barrier, which is the operative obstruction.

LIT_RED

VERDICT: LIT_RED