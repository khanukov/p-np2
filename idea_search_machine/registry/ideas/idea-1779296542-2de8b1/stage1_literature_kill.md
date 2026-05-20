## Q1

Not killed by Baker-Gill-Solovay 1975, because the proposal explicitly invokes number-theoretic content (Deligne's bound for LPS graphs via Ramanujan conjecture on GL_2) which is non-relativizing. The authors anticipate this barrier and design the τ-formula encoding to embed LPS spectral data that does not survive oracle substitution. See BGS, https://doi.org/10.1137/0204037 — but the route is not obviously relativizing.

## Q2

**Killed by Razborov-Rudich, "Natural Proofs", JCSS 1997**, https://doi.org/10.1006/jcss.1997.1494, because — despite the author's claim that the "τ-formula from LPS-NW instance" property is measure-zero and non-constructive — the *underlying* circuit lower bound being established is "L_NW ∉ P/poly" for an NP language whose hardness, if proved via feasible interpolation against any Boolean circuit C, induces a P/poly-computable property (the property "C fails to compute L_NW on inputs of length n") that is largeness-violating in the standard sense. More pointedly: Razborov's own 2015 paper on NW-generators hard for k-DNF resolution (which this proposal extends) is *itself* known to face the natural proofs barrier when pushed to strong proof systems where feasible interpolation against P/poly would suffice — Krajíček "On the proof complexity of the Nisan-Wigderson generator" and follow-ups make this explicit. The proposal's "measure-zero / non-constructive" caveat is about *which τ-formula is selected*, not about the *distinguisher property* the lower bound argument constructs, which is the relevant naturalness object.

**Conditional kill**: applies unless the authors exhibit a concrete non-constructivity or non-largeness witness for the distinguisher property — which they do not.

## Q3

Conditional kill: Aaronson-Wigderson, "Algebrization", TOCT 2009, https://doi.org/10.1145/1490270.1490272, applies under the assumption that feasible interpolation is being invoked in a manner that commutes with low-degree extensions. The LPS spectral input is number-theoretic and arguably non-algebrizing (it depends on GL_2 representation theory, not generic polynomial identities), so the route may evade algebrization. However, the *transfer step* (proof-LB → circuit-LB via feasible interpolation) is a generic syntactic argument that does algebrize, which is precisely why feasible interpolation is known to fail for strong proof systems (see Q6).

## Q4

Killed by **Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality"**, JACM 2022 / ITCS 2020, https://doi.org/10.1145/3538391, and by **Oliveira-Pich-Santhanam (OPS19), "Hardness magnification near state-of-the-art lower bounds"**, CCC 2019, https://doi.org/10.4230/LIPIcs.CCC.2019.27, because: the proposal sits squarely in the regime where a structured NP problem (τ-formula tautology / NW range-avoidance) is supposed to bootstrap a general P/poly lower bound. The locality barrier shows that any lower-bound argument that proceeds by local/sensitivity-style reductions on such structured problems faces a generic obstacle, and OPS19 shows there is a threshold gap that the proposal's "push from resolution / AC^0-Frege to Extended Frege" must cross — but no known technique crosses it. The route relies on "Pich-Santhanam-style switching with LPS-graph-specific switching lemmas" without any indication it evades the locality barrier identified in Chen et al.

## Q5

Killed by equivalence to a well-known open problem: establishing **feasible interpolation for Extended Frege** (or even for `AC^0`-Frege with the strength required here) is itself open and would imply P ≠ NP-style separations directly. Krajíček-Pudlák, "Some consequences of cryptographical conjectures for S^1_2 and EF", Information and Computation 1998, https://doi.org/10.1006/inco.1998.2746, and Bonet-Pitassi-Raz, "No feasible interpolation for TC^0-Frege", FOCS 1997, https://doi.org/10.1109/SFCS.1997.646129, show feasible interpolation **fails** for TC^0-Frege and stronger systems under standard cryptographic assumptions. So Layer 3 of the proposal asks for an open ingredient at least as hard as the conclusion.

## Q6

**Killed by Bonet-Pitassi-Raz, "No feasible interpolation for TC^0-Frege"**, FOCS 1997 / JSL 2000, https://doi.org/10.1109/SFCS.1997.646129, and **Bonet-Domingo-Gavaldà-Maciel-Pitassi, "Non-automatizability of bounded-depth Frege proofs"**, Computational Complexity 2004, because: feasible interpolation provably **fails** for proof systems at and above TC^0-Frege (assuming RSA / DDH / factoring is hard). Since the proposal's Layer 3 requires feasible interpolation at "Extended Frege (or weaker, depending on what we can prove)" — and the proof-complexity lower bound the authors hope to establish needs to be at a system strong enough to encode P/poly circuits, which is at least TC^0-Frege — feasible interpolation is **provably unavailable** under standard cryptographic assumptions. This is a direct refutation of the transfer mechanism.

## Q7

Killed by being **below the magnification threshold**: the τ-formulas associated with NW-generators are known to admit proofs in proof systems just above the lower-bound frontier (see Razborov 2015 Annals, https://annals.math.princeton.edu/2015/181-2/p01, and Pich APAL 2015), and pushing the lower bound to the regime where it implies NP ⊄ P/poly via feasible interpolation crosses the magnification threshold identified in OPS19/Chen et al. (Q4). The known lower bounds for NW τ-formulas are in resolution and polynomial calculus — well below what is needed. See also Krajíček "Proof Complexity", Cambridge 2019, Chapters 19-21.

## Q8

**Killed by Pich-Santhanam, "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly"**, STOC 2021, https://doi.org/10.1145/3406325.3451117 — which the proposal *cites as a prerequisite* but which actually says **the opposite of what the proposal needs**: it shows that strong NP lower bounds (of the form the proposal wants: NP ⊄ P/poly) **cannot be proved in feasible fragments of arithmetic such as `PV_1` or `S^1_2`** under standard hypotheses. The proposal's Layer 3 mechanism — "P/poly upper bound for L_NW yields a short PV_1/S^1_2 proof of τ_n via feasible interpolation, contradicting Layer 2" — is precisely the direction Pich-Santhanam closes off: if such a transfer worked, it would constitute a feasible proof of an NP lower bound, which their theorem rules out conditionally. The proposal misreads its own prerequisite.

Additional: **Krajíček, "Proof Complexity", Cambridge 2019**, Chapter 27-29, explicitly discusses why the NW-τ-formula → circuit-LB route via feasible interpolation has been blocked by the Bonet-Pitassi-Raz line.

## Final verdict

Multiple hard kills:
- Q6: Feasible interpolation provably fails at the required strength (Bonet-Pitassi-Raz).
- Q8: Pich-Santhanam directly rules out the transfer mechanism the proposal relies on.
- Q4/Q5: Locality barrier and equivalence to open feasible-interpolation problem.
- Q2: Natural proofs barrier inadequately addressed.

The proposal's central transfer mechanism (Layer 3) is refuted by the very paper listed as a prerequisite.

LIT_RED

VERDICT: LIT_RED