# Pnp2 Documentation Archive

> **Status (2025-10-23)**: This directory contains historical documentation from the **Family Collision-Entropy (FCE) Lemma** programme (Pnp2 era). These documents are kept for reference and reproducibility but are no longer actively maintained.

## About This Archive

The Pnp2 iteration of the P≠NP formalization effort was based on the **FCE-Lemma** approach, which aimed to prove that families of Boolean functions with low collision entropy can be covered by a subexponential number of monochromatic subcubes.

In September 2025, the project transitioned to a new approach based on the **Switching-Atlas Lemma (SAL)** and hardness magnification, now developed in the `pnp3/` directory. The SAL approach aligns better with contemporary lower-bound techniques and offers a clearer path to hardness results.

## Document Categories

### FCE-Lemma Core Documents
- `fce_lemma_proof.md` - Main FCE lemma statement and constructive proof outline
- `Task_description.md` - Original research plan and motivation for FCE approach
- `fce_counterexample_catalog.md` - Catalog of families that contradict FCE bounds
- `fce_parity_counterexample.md` - Parity family counterexample analysis
- `fce_lemma_modernization.md` - Notes on modernizing FCE approach
- `collision_entropy_solution.md` - Collision entropy handling

### Cover Construction
- `buildCover_card_bound_outline.md` - Cover cardinality bound outline
- `decisionTree_cover_plan.md` - Decision tree cover construction plan
- `canonical_eq_proof_plan.md` - Canonical form equivalence proof
- `asymptotic_cover_estimates.md` - Asymptotic analysis of cover bounds
- `sunflower_next.md` - Sunflower lemma applications

### Lemma B Series
- `lemma_B_plan.md` - Lemma B proof plan
- `lemma_B5_plan.md` - Detailed Lemma B5 plan
- `b3_b5_details.md` - Technical details for B3 and B5

### P ⊆ P/poly Bridge
- `PsubsetPpoly_status.md` - Status of P ⊆ P/poly formalization (completed in Pnp2)

### Status Reports (Historical)
Multiple status reports from October 2025 documenting the transition period:
- `Complete_Axioms_And_Sorry_Inventory_2025-10-22.md`
- `Depth2_Progress_Report_2025-10-22.md`
- `PNP_Proof_Audit_2025-10-22.md`
- And various other progress snapshots

### Roadmaps and Plans
- `E1_roadmap.md` - Early roadmap
- `FullPlan.md` - Comprehensive plan (obsolete)
- `master_blueprint.md` - Master blueprint (obsolete)
- `shrinkage_ac0_roadmap.md` - AC⁰ shrinkage roadmap
- `np_not_p_poly_sketch.md` - NP ⊄ P/poly sketch

## Current Development

For active development and current documentation, see:
- **Main README**: `/README.md` - Project overview and current status
- **PNP3 Documentation**: `/pnp3/Docs/PLAN.md` - SAL approach plan and progress
- **PNP3 README**: `/pnp3/README.md` - PNP3 module structure
- **Current TODO**: `/TODO.md` - Active task tracking

## Why This Transition?

The shift from FCE to SAL reflects lessons learned during development:

1. **Parity Counterexample**: The parity family $F = \{p, \bar{p}\}$ showed that any common cover requires at least $2^{n-1}$ subcubes, contradicting hoped-for subexponential bounds.

2. **Better Alignment**: SAL-based magnification aligns with contemporary circuit lower bound techniques (switching lemma → circuit bounds → hardness magnification).

3. **Clearer Path**: The magnification approach provides clearer intermediate milestones and connects better with existing literature.

## Pnp2 Achievements

Despite the transition, Pnp2 delivered significant results:

- ✅ **Constructive P ⊆ P/poly proof**: Complete formalization of Turing machine → circuit simulation
- ✅ **Cover construction machinery**: Robust framework for subcube covers
- ✅ **Combinatorial lemmas**: Many reusable lemmas about subcubes, entropy, and Boolean functions
- ✅ **Decision tree framework**: PDT infrastructure that is reused in PNP3

These results are preserved in the `Pnp2/*.lean` files and continue to be referenced by the PNP3 development.

---

*For historical context and detailed proofs, consult the Lean files in the parent `Pnp2/` directory. For current work, see `pnp3/`.*
