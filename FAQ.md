# Frequently Asked Questions

## For reviewers and researchers

### Q: What is the technical novelty of the Switching-Atlas Lemma (SAL)?

**A:** The novelty lies in the constructive transition from a single shrinkage witness (a common PDT with global ε) to a unified atlas for an entire family with controlled budgets (depth, leaf count, error). This "plugs in" directly to a general capacity estimate and then to anti-checker/magnification frameworks, with **all steps mechanically verified in Lean**.

Classical switching lemmas provide depth shrinkage for individual formulas. SAL provides a **universal structural approximation for families**, which is a different level of packaging suitable for counting arguments.

### Q: How does SAL relate to the classical switching lemma?

**A:** SAL uses the classical shrinkage property (from switching) as "raw material," but produces a universal structural approximation for a family (an atlas), not just a residual depth estimate for a single formula.

**Key differences:**
- Classical switching: One formula → depth reduction
- SAL: Entire family + shrinkage certificate → unified atlas with budgets
- SAL provides an **interface for counting** and capacity arguments

### Q: What is the role of anti-checkers and magnification?

**A:** We use them as external interfaces following the contemporary framework (OPS'21 and related work). This is the standard modern "pipeline" from weak lower bounds to strong separations, e.g., NP ⊈ P/poly.

**Current status:**
- Anti-checker and magnification interfaces are **axiomatized**
- The pipeline glue is **fully verified in Lean**
- Roadmap: Formalize the external results to remove axioms

### Q: Why is this a "conditional" result?

**A:** The derivation P ≠ NP relies on several external results that are currently axiomatized in Lean:

1. **Multi-switching lemmas** for AC⁰ circuits (Håstad-style)
2. **Anti-checker existence** for MCSP-like problems
3. **Magnification triggers** (locality lifts, hardness amplification)

These results are well-established in the literature but not yet formalized in Lean. Our contribution is the **verified infrastructure** that connects these pieces.

### Q: What does "to the best of our knowledge" mean?

**A:** We have conducted a thorough literature review and are not aware of prior work that:

1. Formulates SAL as a general lemma with verified invariants
2. Combines it with formal capacity theorems
3. Integrates everything into a Lean-verified pipeline

We use this phrasing to remain scientifically conservative. If prior work exists, we welcome references and will update our claims accordingly.

### Q: Is this claim for the Clay Millennium Prize?

**A:** **No.** This is a scientific contribution to complexity theory and formal verification. The Clay Mathematics Institute has specific requirements:

- Unconditional solution (ours is conditional)
- Publication in qualifying journal
- Two years of community review
- General acceptance

Our work is currently a conditional derivation with axioms. We focus on the **scientific and methodological contributions**, not prize consideration.

### Q: What are "subcubes" and "atlases"?

**A:** In Boolean function analysis:

- **Subcube**: A partial assignment fixing some variables, representing a lower-dimensional Boolean space
- **Atlas**: A collection of subcubes that collectively "cover" or approximate a family of functions
- **SAL provides**: A constructive method to build atlases from shrinkage witnesses

This is analogous to how subcube-partition complexity differs from decision-tree complexity in computational complexity theory.

### Q: Why Lean 4? Why formal verification?

**A:** Formal verification provides:

1. **Mathematical certainty**: Machine-checked proofs eliminate human error
2. **Reproducibility**: Anyone can run `lake build` and verify our claims
3. **Modularity**: Clear interfaces between components
4. **Transparency**: All assumptions are explicitly tracked as axioms

For a result as significant as P ≠ NP, even conditionally, this level of rigor is appropriate.

### Q: What is the current axiom count?

**A:** See `AXIOM_ANALYSIS_FINAL.md` for detailed breakdown. Summary:

- **5 critical axioms** in the direct path to P_ne_NP_final
- **11 additional axioms** in alternative paths
- **0 sorry/admit** statements in active code
- All axioms are **explicitly documented and categorized**

### Q: Can I reproduce your results?

**A:** Yes! Complete instructions:

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone repository
git clone https://github.com/khanukov/p-np2.git
cd p-np2

# Build
lake exe cache get  # Download mathlib cache
lake build          # Build project

# Verify main theorem
lean --run pnp3/Magnification/FinalResult.lean
```

The entire development is open source and self-contained.

### Q: What is the relationship to prior PNP1/PNP2 work?

**A:** This repository contains three iterations:

- **PNP1/PNP2**: Family Collision-Entropy (FCE) Lemma approach (archived in the legacy library)
- **PNP3**: Current SAL-based approach (active in `pnp3/`)

The shift reflects lessons learned during 2025 audit. PNP2 files remain available for historical context and reproducibility, but active development focuses on PNP3.

### Q: How can I contribute?

**A:** We welcome contributions in several areas:

1. **Formalizing axioms**: Help remove axioms by formalizing external results
2. **Code review**: Check proofs and suggest improvements
3. **Documentation**: Improve explanations and examples
4. **Testing**: Verify builds on different platforms

See `TODO.md` for current priorities. All contributions should maintain the scientific rigor and conservative tone of the project.

### Q: Where can I learn more about the theoretical background?

**A:** Key references:

- **Switching lemmas**: Håstad (1986), Beame (1994), various surveys
- **Anti-checkers**: Oliveira-Pich-Santhanam (ToC 2021)
- **Magnification**: Chen-Williams (various), ITCS'20 survey materials
- **Complexity theory**: Arora-Barak textbook, modern surveys

See `pnp3/Docs/` for detailed bibliographic references and milestone documentation.
