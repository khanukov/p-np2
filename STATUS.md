# Project Status (current)

This document is the **single source of truth** for the active state of the
repository.

## ✅ Active pipeline

**Pipeline**: PNP3 (Switching‑Atlas Lemma → Covering‑Power → anti‑checker → magnification)  
**Target**: **Partial MCSP**

Key entry points:
- `pnp3/Magnification/FinalResult.lean` — final conditional statement `P_ne_NP_final`.
- `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` — partial‑pipeline bridge.
- `pnp3/LowerBounds/` — anti‑checker and lower‑bound core.
- `pnp3/AC0/MultiSwitching/` — switching/encoding infrastructure (constructive).

## 🔒 External inputs (current)

**Active axiom**:
- `ppoly_circuit_locality` in `pnp3/ThirdPartyFacts/PpolyFormula.lean`

**Witness‑backed theorems** (external witnesses required, no axioms):
- `partial_shrinkage_for_AC0`
- `shrinkage_for_localCircuit`

All downstream glue and magnification theorems are Lean‑checked.

## 🧭 Where to start

Start with:
- `README.md` — project overview and build instructions
- `TECHNICAL_CLAIMS.md` — what is proven vs conditional
- `AXIOM_ANALYSIS_FINAL.md` — explicit axiom/witness inventory
- `TODO.md` — active plan and remaining technical tasks
