# Idea Card

## 1. Thesis

We explore whether NP-complete problems admit a *persistent homology signature* that distinguishes them from P. Specifically, we construct a filtration over the solution space of SAT instances by gradually relaxing clause satisfaction requirements, yielding a simplicial complex at each threshold. The Betti numbers of these complexes capture topological features of the solution landscape. The thesis is that for instances requiring superpolynomial time, the persistent homology exhibits specific growth patterns in its barcode structure—particularly in the birth-death intervals of 1-dimensional holes—that cannot be computed by polynomial-time algorithms. This would manifest as a lower bound: any algorithm computing these topological invariants for hard SAT instances must perform superpolynomial work, and since the invariants correlate with hardness, this implies P ≠ NP.

## 2. Prerequisite techniques

- Persistent homology and barcode stability (Edelsbrunner, Letscher, Zomorodian, 2002)
- Čech and Vietoris-Rips complex constructions over discrete metric spaces (Ghrist, 2008)
- Hardness of computing Betti numbers for simplicial complexes (Anai, Hara, Yokoyama, 2009)
- Solution graph geometry for constraint satisfaction problems (Achlioptas, Coja-Oghlan, 2008)

## 3. Expected mechanism

For a SAT formula φ with n variables, define a filtration by parameter ε ∈ [0,1]: at level ε, include all partial assignments satisfying at least (1-ε) fraction of clauses. Construct a simplicial complex where k-simplices correspond to (k+1)-cliques of "compatible" partial assignments under Hamming distance. Compute persistent homology across the filtration. The mechanism hypothesizes that hard instances exhibit exponentially many persistent 1-cycles (loops) whose birth-death intervals have specific entropy properties. The lower bound would come from proving that extracting these barcode features requires traversing an exponential portion of the solution space, formalized via a reduction showing that any polynomial-time topological computation could be inverted to solve SAT efficiently—a contradiction.

## 4. Target pnp3 / pnp4 interface

`ResearchGapWitness`

## 5. Self-assessment of novelty

MEDIUM. Persistent homology has been applied to algorithm analysis and data, but using topological invariants of solution-space filtrations as a *complexity separator* for NP-completeness is an uncommon cross-domain approach.

VERDICT: idea_card_generated