# To-Do
> **Status (2025-12-26)**: The combinatorial cover is fully formalised. PNP3 has no active axioms; the items below track legacy axioms and quality-of-life improvements.

## Complexity bridge (no-PH roadmap)

- [x] **[classic]** Develop the standard simulation of polynomial-time Turing machines by polynomial-size circuit families (`TM/Encoding.lean`, `Circuit/Family.lean`, `PsubsetPpoly.lean`) and replace the axiom `P_subset_Ppoly` in `ComplexityClasses.lean` with the constructive theorem `P_subset_Ppoly`. (Implemented in the legacy constructive library.)
  - [x] Introduce an explicit single-tape TM model with configurations (`TM/Encoding.lean`).
  - [x] Add basic circuit bookkeeping (`Circuit/Family.lean`) and initialise the configuration-circuit framework (`PsubsetPpoly.lean`).
  - [x] Tighten the gate-count bounds so that `gatePolyBound` is dominated by a genuine polynomial and discharge the checklist in `docs/PsubsetPpoly_status.md` (linear recursion, final domination, axiom removal). (Handled within the legacy constructive modules.)
  - [x] Seal the complexity bridge by exporting the theorem in `ComplexityClasses.lean` and eliminating the axiom `P_subset_Ppoly`. (Available via the archival constructive proofs.)
- [ ] **[models]** Define circuit models for the magnification theorems (`Circuit/Depth.lean`, `Circuit/Oracle.lean` for the MMW’19 route, or `Circuit/General.lean` for OPS’21).
- [ ] **[mcsp]** Introduce the decision/search/gap variants of `MCSP` (`MCSP/Core.lean`, `MCSP/Search.lean`, `MCSP/Gap.lean`).
- [ ] **[bridge]** Strengthen the cover/locality files (`table_locality.lean`, `sat_cover.lean`, `acc_mcsp_sat.lean`) and derive lower bounds for (search-)`MCSP` (`MCSP/LowerBoundsFromCovers.lean`).
- [ ] **[magnif]** Formalise the appropriate magnification theorem (`Magnification/MMW19.lean` or `Magnification/OPS21.lean`) and remove the axiom `magnification_AC0_MCSP`.
- [ ] **[finish]** Replace the placeholder `FCE_implies_MCSP` with the constructive bridge and complete the final derivation of `P ≠ NP` via `NP ⊄ P/poly` + `P ⊆ P/poly`.

## Cover pipeline refinements (optional)

- [ ] Strengthen the coarse numeric bound in the archival `cover_numeric` module (`buildCover_card = 2^n`) once sharper combinatorial estimates are available.
- [ ] Provide a constructive variant of `firstUncovered` in the archival `Cover/Uncovered` module if executable tooling becomes a priority.  The current classical search is sufficient for the Prop-level results.

## Remaining axioms (as of 2025-09-24)

- `NPSeparation.magnification_AC0_MCSP`
- `NPSeparation.FCE_implies_MCSP`

## Outstanding `sorry`s (as of 2025-09-24)

- None – the Lean sources compile without placeholders.
