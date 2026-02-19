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
- Anti-checker and magnification interfaces are **proved in Lean**
- The remaining external inputs are **switching/shrinkage** witnesses (Part A)
- Roadmap: Formalize the witness constructions to remove external inputs

### Q: Why is this a "conditional" result?

**A:** The derivation P ≠ NP currently relies on external switching/shrinkage results that are represented as witness-backed theorems in Lean:

1. **Multi-switching/shrinkage lemmas** for AC⁰ and local circuits (Håstad-style)

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

Our work is currently a conditional derivation with external inputs. We focus on the **scientific and methodological contributions**, not prize consideration.

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
4. **Transparency**: All assumptions are explicitly tracked as external inputs

For a result as significant as P ≠ NP, even conditionally, this level of rigor is appropriate.

### Q: What is the current axiom count?

**A:** See `AXIOMS_FINAL_LIST.md` for detailed breakdown. Summary:

- **1 active axiom** in the live `pnp3/` tree:
  `localizedFamilyWitness_partial`
  (in `pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`)
- **`P_ne_NP_final` cone (audited by `#print axioms`)** includes only
  `localizedFamilyWitness_partial` as a project-specific axiom
- **No placeholder axioms** in `pnp3/AC0/MultiSwitching/Encoding.lean`
- **0 sorry/admit** statements in active code
- Switching/shrinkage inputs are **witness-backed theorems**, with witnesses
  still supplied externally

You can also run `scripts/check.sh` to rebuild and smoke-test. For raw axiom
inventory use `rg "^axiom " -g"*.lean" pnp3` (currently expected to show 1 line).

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


### Q: How can I contribute?

**A:** We welcome contributions in several areas:

1. **Formalizing witnesses**: Help remove external inputs by formalizing witness constructions
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
