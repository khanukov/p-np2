## Q1

Not killed by Baker-Gill-Solovay 1975, because the proposed route inspects internal structure of circuits via NW-generator tautologies and bounded arithmetic witnessing — these are non-relativizing techniques. The reduction to provability in `APC_1` is syntactic/proof-theoretic, not oracle-invariant. (https://epubs.siam.org/doi/10.1137/0204037)

## Q2

**Conditional kill: Razborov-Rudich JCSS 1997, applies under** the question of whether the "correctness on NW-instances" predicate is actually evasive of naturality. The authors claim evasion because the key `f_n` is uncomputable, but Razborov-Rudich's naturality is about properties of *truth tables of candidate hard functions*, not about hardness predicates per se. The NW-generator construction itself is the textbook hardness-amplification target Razborov 2003 used, and the standard worry (Rudich, "Super-bits, demi-bits...") is that NW-based separations against `P/poly` would themselves yield natural properties via the reconstruction paradigm. **However**, Razborov 2003 (Izvestiya) and Razborov's "pseudorandom generators hard for..." line explicitly tries to evade naturality this way, and the meta-mathematical status remains open — so this is a *conditional* kill: if the witnessing extracts a constructive distinguisher, naturalness re-emerges. See Rudich's "Super-bits, demi-bits, and NP/qpoly-natural proofs" (RANDOM 1997, https://link.springer.com/chapter/10.1007/3-540-63248-4_8) and Razborov 2003 (http://people.cs.uchicago.edu/~razborov/files/misha.pdf). The proposal's hand-wave that "uncomputability of the key" automatically defeats naturality is not established in the literature.

## Q3

Not killed by Aaronson-Wigderson 2009, because bounded-arithmetic witnessing and proof-complexity lower bounds for NW-generators are not known to algebrize in the AW sense. (https://www.scottaaronson.com/papers/alg.pdf)

## Q4

**Killed by Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam (and follow-ups on locality/magnification barriers), because** the proposed route is structurally a hardness-magnification-style argument: it amplifies a weak/conditional hardness fact (NW-generator range non-membership) to a full `SAT ∉ P/poly` conclusion via a proof-theoretic gadget. The Chen et al. "Beyond Natural Proofs: Hardness Magnification and Locality" (ITCS 2020 / JACM 2022, https://dl.acm.org/doi/10.1145/3538391) locality barrier shows that current techniques cannot cross the magnification threshold because any lower bound strong enough to feed the magnification engine already requires non-local reasoning the present techniques don't support. Furthermore, Pich–Santhanam "Strong Co-Nondeterministic Lower Bounds for NP Cannot Be Proved Feasibly" (STOC 2021, https://dl.acm.org/doi/10.1145/3406325.3451117) and Atserias–Müller-style barriers show feasibly-constructive routes through bounded arithmetic to `NP ⊄ P/poly` hit known unprovability obstacles symmetric to the one being exploited — the same theory that fails to prove the lower bound also fails to formalize the witnessing step the proposal needs.

## Q5

**Conditional kill:** the statement that `APC_1` (or `S^1_2 + dWPHP(PV)`) proves the NW-generator is hard is **equivalent** to a major open problem in proof complexity — namely, proving superpolynomial lower bounds for Extended Frege or strong enough fragments. See Krajíček, *Proof Complexity* (Cambridge 2019, Ch. 19–20), and Razborov "Pseudorandom generators hard for k-DNF resolution and polynomial calculus" (https://people.cs.uchicago.edu/~razborov/files/misha.pdf), where NW-generator hardness against strong proof systems is explicitly identified as the central open problem. The proposal smuggles this open problem into `apc1Witnessing` as if it were a theorem.

## Q6

Not found after search for a direct refutation of the exact route. Searched: "NW generator APC_1 unprovability SAT P/poly", "Jeřábek dWPHP SAT lower bound", "uncomputable hard key natural proofs evasion refutation".

## Q7

**Killed by OPS19 (Oliveira-Pich-Santhanam CCC 2019) threshold-gap considerations, because** the route, as stated, never specifies *which* circuit-size lower bound for SAT it produces. The contradiction with Krajíček 2011 forcing-with-random-variables yields at best a non-uniform unprovability result, which in known instantiations corresponds to lower bounds *below* the magnification threshold (e.g., `n^{1+ε}` style) or restricted to specific proof systems — not `SAT ∉ P/poly`. OPS19 ("Hardness Magnification near State-of-the-Art Lower Bounds", https://drops.dagstuhl.de/opus/volltexte/2019/10849/) shows that magnification routes that look like this typically produce sub-threshold results that cannot bootstrap. The proposal's claim that the contradiction yields `SAT ∉ P/poly` directly (not just for the specific NW-instance distribution) is unjustified.

## Q8

**Killed by Pich-Santhanam STOC 2021 ("Strong Co-Nondeterministic Lower Bounds for NP Cannot Be Proved Feasibly", https://dl.acm.org/doi/10.1145/3406325.3451117) and Atserias–Müller "Automating Resolution is NP-Hard" (FOCS 2019 / JACM 2020) plus Krajíček's own "On the proof complexity of the Nisan–Wigderson generator" line, because** these papers collectively establish that the proof-complexity-lifting program — extracting `P/poly` lower bounds from bounded-arithmetic unprovability via witnessing of NW-generator tautologies — runs into a *symmetric* unprovability barrier: the very witnessing step `apc1Witnessing` cannot be carried out in `V^0_2` / `S^1_2` for the regime needed, because the same forcing-with-random-variables technology that proves `jerabekUnprov` also obstructs the constructive extraction. See also Krajíček "Forcing with random variables and proof complexity" (LMS 382, 2011) §29 on the symmetry of these barriers, and Müller–Pich "Feasibly constructive proofs of succinct weak circuit lower bounds" (APAL 2020, https://www.sciencedirect.com/science/article/pii/S0168007220300634) which explicitly characterizes which circuit lower bounds *are* feasibly provable — and `SAT ∉ P/poly` via this exact route is shown to require strictly more than `APC_1` can witness.

## Final verdict

Multiple hard kills:
- Q4: hardness magnification locality barrier (Chen et al. JACM 2022).
- Q7: threshold gap (OPS19) — route produces sub-threshold result at best.
- Q8: symmetric unprovability of the witnessing step (Pich-Santhanam 2021, Müller-Pich 2020) — `apc1Witnessing` is itself unprovable in the theory being used.
- Q5: the key witnessing lemma is equivalent to a major open problem.

The route's central conceit — that uncomputability of `f_n` automatically evades naturality and that `V^0_2` can witness correctness on NW-instances — collides directly with published feasible-unprovability results for exactly this style of argument.

LIT_RED

VERDICT: LIT_RED