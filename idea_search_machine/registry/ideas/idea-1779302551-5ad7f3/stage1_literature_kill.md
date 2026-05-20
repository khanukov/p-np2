## Q1

**Is this relativizing?**

Not killed by Baker-Gill-Solovay 1975 (https://epubs.siam.org/doi/10.1137/0204037), because the proposed mechanism uses a specific combinatorial/geometric encoding (Robinson tilings, Mozes substitutions, block-gluing) that does not obviously relativize — oracle access would have to be plumbed into the SFT alphabet, and the entropy invariant is not defined oracle-relative in the usual sense. However, this is **not a positive feature**: it merely means BGS is not the right kill. The construction in (b) does diagonalize against polynomial-time approximators, which is a relativizing technique, so a conditional concern exists. Conditional kill: BGS applies under the assumption that step (b)'s diagonalization is carried out by a Turing-machine simulation argument — which it must be, since "polynomial-time approximation schedule" is defined relative to TM computation. The diagonal real α is constructed by a TM-style argument against poly-time approximators, which **does** relativize, so applied to oracles where P=NP (e.g., PSPACE-complete oracle) the same construction would falsely separate P^A from NP^A.

Conditional kill: Baker-Gill-Solovay 1975, applies under the assumption that step (b)'s diagonalization against poly-time approximators relativizes (it does — it is a direct TM diagonalization).

## Q2

**Is this natural?**

Conditional kill: Razborov-Rudich JCSS 1997 (https://www.sciencedirect.com/science/article/pii/S0022000097914940), applies under the assumption that the property "circuit family {C_n} induces an SFT X(C) whose entropy admits a poly-time approximation schedule" is (i) constructive, (ii) large, and (iii) useful in their sense. Constructivity: yes — given a circuit, the Mozes substitution is computable, and the entropy approximation schedule is computed in polynomial time by hypothesis. Largeness: the property is presumably satisfied by a constant fraction of small circuits since random small circuits give low-complexity SFTs with computable entropy approximants. Usefulness: trivially, since it is the contrapositive of an NP lower bound. Under standard one-way function assumptions, this is killed.

Conditional kill: Razborov-Rudich JCSS 1997, applies under standard cryptographic assumptions (subexponentially hard PRGs) and if the entropy-approximability property is constructive+large.

## Q3

**Is this algebrizing?**

Not killed by Aaronson-Wigderson 2009 (https://dl.acm.org/doi/10.1145/1490270.1490272), because the construction is combinatorial/topological-dynamical and does not use low-degree extensions or arithmetization. Algebrization barrier does not directly apply. (Again, this is not positive evidence the proof works.)

## Q4

**Is this a known hardness-magnification dead end?**

Not killed by Chen et al. JACM 2022 locality barrier (https://dl.acm.org/doi/10.1145/3538391) directly, because the proof does not proceed via hardness magnification — it is a direct circuit lower bound via an invariant, not a gap amplification of a weak lower bound. OPS19 (https://drops.dagstuhl.de/opus/volltexte/2019/10849/) similarly does not directly apply. Not killed by these specific papers.

## Q5

**Is this equivalent to a known open lower bound?**

The "entropy approximation rate as a function of circuit size" framing is, as far as published literature shows, not equivalent to a named open lower bound, but the core diagonal in (b) — producing a Π₁-real with no poly-time approximation schedule — is essentially a time-hierarchy diagonalization. The step from "L_tile yes-instances embed subshift Y of entropy α" to "circuits computing L_tile must approximate α in poly time" is the load-bearing step, and it is **exactly equivalent** to: "deciding L_tile in P implies poly-time approximating α." If that implication holds it would be a direct P vs. NP-via-diagonalization, which is known to be insufficient by the relativization barrier (see Q1).

Not killed by a named equivalence, but the implication "circuit decides L → entropy poly-approximable" is the entire content of the claim and is unsupported by any published bridge theorem.

## Q6

**Is this already proved impossible?**

Not killed by direct refutation. Hochman-Meyerovitch (https://annals.math.princeton.edu/2010/171-3/p20) characterizes SFT entropies as right-r.e. reals but does **not** provide a quantitative correspondence between the *computational complexity* of the entropy approximation and the *size* of any computational device — it provides only computability, not complexity. Step (a)'s claim that |C_n| ≤ n^c implies a poly-time entropy approximation schedule is **not** a theorem of Hochman-Meyerovitch; their construction has tower-of-exponentials overhead from the Robinson hierarchical simulation. This is a misuse of the theorem rather than a refuted claim, but Gangloff-Sablik and follow-ups (e.g., Gangloff, "Quantified block gluing for multidimensional subshifts of finite type", Ergodic Theory Dynam. Systems 2019, https://arxiv.org/abs/1804.07581) show that the entropy-computation overhead in Mozes/Hochman-Meyerovitch is super-polynomial and in fact related to the mixing rate, not the circuit size.

Conditional kill: Gangloff (arXiv:1804.07581) and the original Hochman-Meyerovitch construction itself, applies because the conversion from a computable approximation schedule to an SFT presentation incurs at least exponential overhead in the Robinson hierarchy depth, falsifying step (a)'s polynomial conversion claim.

## Q7

**Is this already known to be too weak?**

Not directly addressed; the claim is at the level of P vs. NP, not below a magnification threshold.

## Q8

**Is there a paper that directly says "this type of route does not work"?**

The general program of separating complexity classes via symbolic-dynamics invariants has been explored (e.g., Simpson, "Medvedev degrees of two-dimensional subshifts of finite type", Ergodic Theory Dynam. Systems 34 (2014), https://www.math.psu.edu/simpson/papers/2dim.pdf), and the connection between effective subshifts and computability classes is well-mapped, but no paper claims this yields complexity-class separations because the bridge from circuit size to entropy approximation rate is missing in all published work — the Hochman-Meyerovitch correspondence is at the level of computability, not complexity. Aaronson's "Is P versus NP formally independent?" (Bull. EATCS 2003, https://www.scottaaronson.com/papers/pnp.pdf) and Aaronson's "P=?NP" survey (https://www.scottaaronson.com/papers/pnp-survey.pdf) explicitly catalog "diagonalization-style" approaches and dismiss them via BGS — and step (b) here is precisely a TM diagonalization in disguise. See also the Razborov "On provably disjoint NP-pairs" line. Not a direct "this exact route fails" paper, but the relativization barrier directly applies to step (b).

## Final verdict

Three conditional kills landed:
- **Q1 (relativization)**: step (b)'s diagonal against poly-time approximators is a relativizing TM diagonalization, killing the route under BGS.
- **Q2 (naturalization)**: the induced property on circuits is plausibly constructive+large+useful, hitting Razborov-Rudich.
- **Q6 (misuse of Hochman-Meyerovitch)**: the claimed polynomial circuit-size → polynomial entropy-approximation conversion in step (a) contradicts the known super-polynomial overhead in Mozes/Robinson hierarchical simulation (Gangloff arXiv:1804.07581), and Hochman-Meyerovitch is a computability theorem with no quantitative complexity content.

The Q6 issue is the hardest: the load-bearing step (a) is simply not what Hochman-Meyerovitch proves. Combined with the Q1 relativization kill on step (b), the route has at least one effectively-hard kill.

LIT_RED

VERDICT: LIT_RED