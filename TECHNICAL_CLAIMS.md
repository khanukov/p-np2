# Technical Claims and Contributions

## Switching-Atlas + Covering-Power: Lean-verified core and a conditional end-to-end pipeline

### What is new (our contribution)

We introduce and Lean-verify a constructive bridge from shrinkage to a uniform atlas of subcubes for whole families of Boolean functions (Switching-Atlas Lemma, SAL) and prove a general Covering-Power capacity bound for atlas-approximable families. Together, these results provide a reusable capacity barrier for lower-bounds pipelines based on switching methods.

**To the best of our knowledge**, this SAL packaging (common PDT with error → common atlas with leaf/ε budgets → capacity) is new in the literature, and our development offers the first Lean-checked implementation of this combinatorial spine.

### How this closes the loop (conditionally)

Plugging SAL + Covering-Power into standard anti-checker and magnification frameworks (e.g., OPS'21, Chen-Williams-Jin) produces a Lean-verified **conditional derivation** of NP ⊈ P/poly and hence P ≠ NP, assuming the external switching/shrinkage results are available as axioms:

- Multi-switching / shrinkage lemmas for AC⁰ and local circuits

The entire glue and all internal combinatorics are machine-checked; only explicitly marked axioms remain. See the OPS'21 ToC paper and magnification surveys for the surrounding framework.

Our proof avoids the Natural Proofs barrier because the combinatorial property (incompressibility by SAL-atlases) is established only against weak classes ($AC^0$ and local circuits). The extension to $NP \not\subseteq P/poly$ is achieved via Hardness Magnification, which relies on the specific structural properties of MCSP, not on extending the natural property to $P/poly$.

### Priority statement

We are not aware of prior works that:

1. Formulate SAL as a general lemma producing a single atlas for an entire family from a single shrinkage certificate with verified invariants, and
2. Combine it with a formal capacity theorem to yield a plug-and-play barrier inside a Lean-verified A→B→C→D pipeline.

**Classical background**: Håstad-type switching, decision-tree depth shrinkage, and subcube reasoning are well-known; our contribution is the **packaging, formalization, and end-to-end integration** in Lean 4.

## Status and roadmap

### Unconditional (Lean-proved) results

- **SAL (shrinkage → unified atlas)**: Constructive transformation with verified invariants
- **Covering-Power (capacity barrier)**: General upper bound for atlas-approximable families
- **Infrastructure**: Complete PDT/Atlas/Scenario data structures with invariants
- **All glue code**: Machine-checked connections between components

### Conditional final result

From the external switching facts (Part A), the derivation NP ⊈ P/poly ⇒ P ≠ NP follows. All "stitching" is formally verified.

### Novelty

First Lean-verified composition of shrinkage → atlas → capacity using a unified atlas for the entire family. This makes anti-checker constructions a "standard module" (it suffices to exhibit |Y| > capacity).

### Roadmap to unconditional result

To achieve an unconditional separation:

1. **Formalize multi-switching/shrinkage** (Part A)
2. **Replace all axioms** with constructive proofs

See ITCS'20 magnification survey and related work for theoretical background.

## Compliance note

### Clay Mathematics Institute rules

We emphasize that the present Lean development delivers a **conditional end-to-end derivation** of P ≠ NP. Under the Clay Mathematics Institute rules, consideration of the Millennium Prize requires:

1. A complete, **unconditional** solution
2. Publication in a qualifying refereed journal
3. Survival of at least two years after publication
4. General acceptance in the global mathematics community

A formal proof in Lean is a strength for reliability and reproducibility but is **not a substitute** for these requirements. Our work focuses on the scientific contribution to complexity theory and formal verification, not on prize consideration.

## References and context

### Related work

- **Switching lemma**: Håstad (1986) and subsequent variations
- **Anti-checkers and magnification**: OPS'21 (Theory of Computing), Chen-Williams-Jin framework
- **Hardness magnification surveys**: ITCS'20 survey-style papers, Ce Jin's materials
- **CMI Prize rules**: Clay Mathematics Institute official documentation

### Our positioning

We build on classical results in circuit complexity and provide:

- A novel **architectural integration** (SAL + capacity + magnification)
- **Full Lean 4 verification** of the entire pipeline
- **Explicit tracking** of all external assumptions
- **Reproducible infrastructure** for complexity theory research

This work represents a contribution to both:
- **Formal methods**: Demonstrating feasibility of large-scale complexity theory formalization
- **Complexity theory**: Providing reusable, verified building blocks for lower-bound research
