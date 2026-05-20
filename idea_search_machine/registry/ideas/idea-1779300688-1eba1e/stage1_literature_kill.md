## Q1

Not killed by Baker-Gill-Solovay 1975, because the route explicitly invokes arithmetic encoding of cryptographic primitives (PRG security reductions) which do not relativize — relativization barriers don't apply to constructions that use the code of the cryptographic object. See https://doi.org/10.1137/0204037. The author's claim of non-relativization is plausible on its face.

## Q2

Conditional kill: Razborov-Rudich JCSS 1997 (https://www.sciencedirect.com/science/article/pii/S0022000097914940), applies under the assumption that the underlying property is in fact "constructive + large." The author argues SAT-solving is not testable in poly(2^n) and holds on measure-zero, which would evade naturalness. However, **Razborov-Rudich themselves note** that any lower-bound proof against P/poly under strong OWF assumptions must be non-natural, and historically every attempt to leverage "non-naturalness via cryptographic gadgets" has either (a) collapsed back into a natural property when made concrete, or (b) failed to actually prove a lower bound. The route does not exhibit a concrete reason the property remains non-natural after the KPT protocol is unfolded — the Student-Teacher transcript induces a poly-time test on truth tables of the gadget, which is suspicious. Not a hard kill, but a serious warning.

## Q3

Not killed by Aaronson-Wigderson 2009 (https://doi.org/10.1145/1490270.1490272), because factoring hardness is not known to algebrize and the route uses it essentially. However, A-W explicitly observe that any non-algebrizing technique must use properties of the specific computational problem beyond its low-degree extension — the route claims this via the PRG-security reduction, which is acceptable as a non-algebrizing ingredient.

## Q4

**Killed by Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam-style locality/magnification results, specifically Chen et al. JACM 2022 ("Beyond Natural Proofs: Hardness Magnification and Locality")** https://doi.org/10.1145/3538391, because the locality barrier shows that current magnification-style routes — which is structurally what a "gadget-specific witnessing collapse drives a SAT lower bound" argument is — cannot lift past a sharp threshold (typically n^{1+ε} sized circuits for restricted problems), and they exhibit a barrier showing that the magnification-style argument applied to gadget constructions like the ones proposed gets blocked by a "locality" property that the Goldreich-local-PRG gadget *exactly* satisfies (locality is the *defining* feature of Goldreich's PRG). The route's choice of a *local* PRG as the gadget walks directly into the locality barrier of Chen et al.

Additionally, **OPS19** (Oliveira-Pich-Santhanam, CCC 2019, "Hardness magnification near state-of-the-art lower bounds", https://drops.dagstuhl.cz/opus/volltexte/2019/10849/) establishes threshold-gap barriers for exactly the kind of "small gadget → big lower bound" amplification this route relies on.

## Q5

Conditional kill: The witnessing-collapse target is essentially equivalent to "S^1_2 does not prove SAT ∈ P/poly," which is the central open problem of Cook's program in bounded arithmetic. **Krajíček-Pudlák 1989/1995** (Bounded Arithmetic monograph) and **Pich 2015** (https://doi.org/10.1016/j.apal.2014.10.007) show that proving such non-provability results is itself equivalent to or strictly harder than the corresponding circuit lower bound in standard cases. So the "transfer" is suspected to be a tautology, not a transfer.

## Q6

Not found after search. No direct refutation of the specific KPT-witnessing-vs-Goldreich-PRG instantiation exists. Searches: Google Scholar "KPT witnessing Goldreich PRG", "bounded arithmetic Tseitin expander SAT lower bound", arXiv cs.CC + math.LO 2015-2024.

## Q7

**Killed by OPS19 threshold considerations** (https://drops.dagstuhl.cz/opus/volltexte/2019/10849/) combined with the fact that Goldreich-PRG-on-expander gadgets are exactly in the regime where known magnification gives sub-threshold conclusions. The Ben-Sasson-Wigderson Tseitin-over-expander hardness (https://doi.org/10.1145/375827.375835) is a **Resolution** lower bound — restricted-model — and the route gives no mechanism to lift it past Resolution / Res(log) to P/poly. The gadget hardness is below the magnification threshold for P/poly.

## Q8

**Killed by Krajíček-Pudlák 1998 JSL** ("Some consequences of cryptographical conjectures for S^1_2 and EF," https://doi.org/10.2307/2586566) read together with **Razborov 1995** ("Unprovability of lower bounds on circuit size in certain fragments of bounded arithmetic," Izvestiya): these papers establish that cryptographic hardness gives *unprovability of circuit lower bounds in bounded arithmetic*, **not** a route from "SAT ∈ P/poly" to a witnessing contradiction. The direction the route attempts ("SAT in P/poly ⇒ S^1_2 proves something ⇒ cryptographic contradiction") inverts the established direction; KP98 specifically warns that OWF assumptions block proofs *in* S^1_2 rather than enabling reductio arguments *from* uniform circuit families. Furthermore, **Pich-Santhanam "Why are Proof Complexity Lower Bounds Hard?"** (FOCS 2019, https://arxiv.org/abs/1906.10895) explicitly argues that this style of route — using bounded arithmetic to transfer cryptographic hardness to circuit lower bounds — faces a meta-barrier: such proofs would themselves have to be unformalizable in the very theories they invoke.

## Final verdict

Multiple hard kills: (Q4) the choice of a *local* Goldreich PRG as the gadget walks directly into the Chen et al. JACM 2022 locality barrier; (Q7) the gadget hardness sits below the OPS19 magnification threshold; (Q8) the KP98 + Pich-Santhanam framework indicates the transfer direction is inverted and meta-barred. Q2 and Q5 add further conditional pressure.

LIT_RED

VERDICT: LIT_RED