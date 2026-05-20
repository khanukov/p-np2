## Q1

Not killed by Baker–Gill–Solovay 1975 (https://epubs.siam.org/doi/10.1137/0204037), because the proposed route explicitly invokes the algebraic structure of the permanent polynomial (orbit closure in $\mathrm{GL}_{n^2}$), and representation-theoretic multiplicity obstructions are not preserved by oracle access. Standard GCT-style arguments are accepted as non-relativizing (cf. Mulmuley–Sohoni I, https://arxiv.org/abs/cs/9810005). The proposal correctly anticipates this.

## Q2

Conditional kill: Razborov–Rudich, JCSS 1997 (https://www.sciencedirect.com/science/article/pii/S0022000097914940), applies under the assumption that the property used to obstruct circuits is *constructive and large*. The proposed multiplicity obstruction is, by design, a property of a measure-zero variety (single polynomial's orbit closure), so it is **not large**. Hence not killed by naturalness — but only if the authors can actually exhibit a partition $\lambda$ with the claimed strict multiplicity gap, which is exactly the open problem.

## Q3

Not killed by Aaronson–Wigderson 2009 (https://dl.acm.org/doi/10.1145/1490270.1490272), because GCT-style obstructions are generally considered non-algebrizing: the construction depends on the specific symmetry group of the permanent, which an algebraic oracle does not preserve. Aaronson–Wigderson themselves cite GCT as a candidate non-algebrizing approach.

## Q4

**Killed by Bürgisser–Ikenmeyer–Panova, J. AMS 2019** ("No occurrence obstructions in geometric complexity theory", https://arxiv.org/abs/1604.06431), because it rules out occurrence obstructions for permanent vs. determinant in the relevant regime. The proposal claims to evade this by using **multiplicity** obstructions (citing Ikenmeyer–Kandasamy STOC 2020, https://arxiv.org/abs/1911.02534). However, **Ikenmeyer–Kandasamy 2020 themselves prove that multiplicity obstructions for permanent vs. determinant must have *positive* multiplicity in the determinant orbit closure** — i.e., they cannot be "vanishing multiplicity" obstructions, severely constraining the route. Worse, Dörfler–Ikenmeyer–Panova ("On geometric complexity theory: multiplicity obstructions are stronger than occurrence obstructions", ICALP 2019, https://arxiv.org/abs/1812.02531) shows multiplicity obstructions exist *in principle* but gives no construction for perm vs det. **No partition $\lambda$ with the claimed strict gap is known to exist for perm vs. det.** The Layer 1 premise is itself an open problem of GCT, not a usable tool.

## Q5

**Killed (equivalence): the Layer-1 multiplicity-gap requirement is equivalent to the central open problem of GCT for permanent vs. determinant.** Producing such a $\lambda$ would already imply $\mathrm{VP}_{ws} \neq \mathrm{VNP}$ (Mulmuley–Sohoni, https://arxiv.org/abs/cs/9810005; see also Bürgisser et al. survey https://arxiv.org/abs/1101.5380). The proposal assumes its hardest input as a hypothesis. Even granting Layer 1, the RPCP problem is not standardly known to be NP-hard in the required uniform sense (see Q7).

## Q6

Not killed by a direct refutation of RPCP-based separation; the specific framing (RPCP + bounded arithmetic + multiplicity obstruction) has not been refuted verbatim. But the *combination* of Layer 1 (open) with Layer 2 reductions does not appear in the literature in a way that gives a known impossibility.

## Q7

**Killed by Pich–Santhanam, FOCS 2021** (https://eccc.weizmann.ac.il/report/2020/152/), and related: their results show that strong nondeterministic lower bounds for NP cannot be feasibly proved from natural-style hypotheses. The proposal claims a bounded-arithmetic non-provability statement, but Pich–Santhanam show that the kind of $V^1_2$-witnessing extraction the proposal needs to *force* contradiction tends to require precisely the kind of feasible-constructive structure the proposal disclaims. More directly: **the proposal needs subexponential NTIME for RPCP to be *formalizable* in $V^1_2$ in a way that extracts an explicit GL-equivariant homomorphism**. Pich 2015 (https://www.sciencedirect.com/science/article/pii/S0168007215000408) formalizes circuit reasoning in $V^1_2$, but no result extracts representation-theoretic homomorphisms from $V^1_2$ proofs — this extraction step (Layer 2) has no published precedent and likely conflates semantic algebraic-geometric content with syntactic feasibility.

## Q8

**Killed by Grochow, "Unifying Known Lower Bounds via Geometric Complexity Theory" (CCC 2014 / https://arxiv.org/abs/1304.6333) combined with Bürgisser–Ikenmeyer–Panova 2019**: Grochow shows that virtually all classical algebraic LB techniques can be rephrased in GCT terms — meaning GCT is at least as hard as the classical techniques. BIP19 then shows the most natural GCT route (occurrence) fails. The multiplicity route is not known to bypass this. Furthermore, **Ikenmeyer–Panova, "Rectangular Kronecker coefficients and plethysms in geometric complexity theory" (Adv. Math. 2017, https://arxiv.org/abs/1512.03798) shows the relevant Kronecker/plethysm coefficients in the perm-vs-det regime do not vanish in ways usable for separation.** Specifically for the perm-vs-det orbit-closure setting, no published multiplicity gap exists, and BIP-style "stretching" arguments suggest similar obstructions to multiplicity routes.

## Final verdict

Layer 1 of the proposal is exactly an unsolved central problem of GCT (Q4, Q5, Q8), and the literature actively documents (BIP19, IP17) that the natural representation-theoretic candidates do not deliver the required gap. Layer 2 (extracting GL-equivariant homomorphisms from $V^1_2$ proofs) has no published analogue and conflicts with the spirit of Pich–Santhanam (Q7). The proposal does not merely assume a hard lemma — it *renames* the perm-vs-det multiplicity question as a "prerequisite" and bundles it with a speculative bounded-arithmetic extraction step.

LIT_RED

VERDICT: LIT_RED