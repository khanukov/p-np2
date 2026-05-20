# Idea Card

## 1. Thesis

We explore whether P ≠ NP can be established by proving that satisfying assignments of random k-SAT instances, when they exist, exhibit a geometric clustering property that cannot be efficiently navigated by any polynomial-time algorithm. Specifically, we conjecture that for appropriate parameters, the solution space of satisfiable k-SAT formulas fractures into exponentially many well-separated clusters, and that any deterministic polynomial-time algorithm must exhibit a "cluster-blindness" property: it cannot reliably identify which cluster contains a solution without essentially searching all of them. The proof strategy would formalize a notion of cluster-isolation via Hamming distance, prove that witness certificates must encode cluster-location information of super-logarithmic size, and show this contradicts the existence of a polynomial-time decision procedure by a counting argument over the algorithm's accessible state space.

## 2. Prerequisite techniques

- Random k-SAT phase transitions and clustering phenomena (Mézard, Parisi, Zecchina, *Science* 2002)
- Overlap gap property in constraint satisfaction (Gamarnik, Sudan, *FOCS* 2014)
- Reconstruction thresholds on random graphs (Mossel, *STOC* 2004)
- Information-theoretic lower bounds via communication complexity (Kushilevitz, Nisan, 1997)

## 3. Expected mechanism

The mechanism proceeds in three stages. First, we formalize the cluster geometry of random k-SAT near the satisfiability threshold, proving that solution clusters have diameter O(n) but inter-cluster distance Ω(n). Second, we model any polynomial-time SAT algorithm as a state machine with poly(n) states and prove that cluster identification requires Ω(n) bits of information via a reduction to a communication game. Third, we show that the algorithm's evolution on a random satisfiable instance cannot extract sufficient cluster-location information from local formula structure alone, creating an information bottleneck. The final step argues that this bottleneck persists across all polynomial-time algorithms by a union bound over algorithm descriptions, yielding P ≠ NP.

## 4. Target pnp3 / pnp4 interface

`VerifiedNPDAGLowerBoundSource`

## 5. Self-assessment of novelty

LOW. Cluster-based barriers are well-studied in average-case complexity and connect to known obstacles (naturalization, statistical algorithms). The geometric approach echoes refuted support-cardinality ideas.

VERDICT: idea_card_generated