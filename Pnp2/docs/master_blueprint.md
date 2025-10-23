> **Status (2025-10-04)**: Parity counterexample invalidates the current formulation of the FCE-lemma; every reference to a common subcube cover of size $2^{o(n)}$ rests on a false statement.【F:docs/fce_parity_counterexample.md†L1-L78】 Весь раздел о «завершённом комбинаторном ядре» следует воспринимать как план к пересмотру.

# Master Blueprint 2025 → 20XX

This note summarises the long-term plan towards a formal proof that `P ≠ NP`.  После обнаружения контрпримера паритета мы больше не можем утверждать, что комбинаторное ядро завершено: FCE-лемма в текущей формулировке ложна, поэтому Lean-разработку необходимо пересмотреть, явно отделив проверенные факты от гипотетических модулей.【F:docs/fce_parity_counterexample.md†L8-L78】

## 0. Foundation

* Maintain the Lean library of Boolean functions, subcubes, entropy, and sunflower technology.  ✅ Completed in `Pnp2/`.
* Record outstanding axioms explicitly (`NPSeparation.magnification_AC0_MCSP`, `NPSeparation.FCE_implies_MCSP`).
* **New remediation (2025-10-04).** Перечислить все участки кода и документации, где используется покрытие общими подкубами, и либо удалить, либо обособить их как гипотезы до тех пор, пока не появится корректная альтернатива FCE-лемме.【F:docs/fce_parity_counterexample.md†L40-L78】
* **Counterexample catalogue (2025-10-05).** Зафиксирован набор базовых тестов (см. [каталог контрпримеров](fce_counterexample_catalog.md)), который должна проходить любая новая формулировка FCE-леммы, прежде чем её результаты будут интегрированы в код и документацию.

## 1. From restricted to general models

Strengthen known lower bounds for `MCSP` in restricted circuit classes to depth `o(log N)` with exponent `1+ε`.  This remains an open mathematical problem; the Lean repository provides infrastructure for experimenting with the combinatorial side (decision-tree covers, entropy bounds).  Требуется проверить, какие зависимости от FCE-леммы присутствуют в текущих формальных наработках, чтобы исключить скрытые противоречия.【F:docs/fce_parity_counterexample.md†L40-L78】

## 2. Trigger magnification

Formalise the magnification theorem that converts the improved `MCSP` bound into `NP ⊄ P/poly`.  This step is currently modelled by the axiom `magnification_AC0_MCSP`.

## 3. Break algebrisation / relativisation

Develop a meet-in-the-middle SAT algorithm for compositions `ACC⁰ ∘ MCSP`, or argue that the previous steps already bypass known barriers.  `Algorithms/SatCover.lean` and `acc_mcsp_sat.lean` provide stubs for future work; they compile and expose constructive interfaces but still rely on exponential enumeration.

## 4. Uniformisation

Convert the non-uniform separation into `P ≠ NP` through the classical implication `NP ⊄ P/poly` + `P ⊆ P/poly`.  The set-theoretic deduction is now formalised; after the constructive proof of `P ⊆ P/poly` the bridge waits only for the magnification/cover axioms to be discharged.  The groundwork for the uniform side lives in `TM/Encoding.lean`, `Circuit/Family.lean`, and `PsubsetPpoly.lean`.

## 5. Proof-complexity lock-in (optional)

As an alternative route, pursue strong lower bounds for Extended Frege proofs, leveraging the formalised cover technology.

## 6. Cryptographic connection (optional)

Explore connections between `MCSP` hardness, pseudorandom generators, and one-way functions.  These directions are not yet reflected in the Lean code but can reuse the combinatorial infrastructure.

## 7. Verification and publication

* `Cover/BuildCover.lean` now implements the well-founded recursion with proofs of coverage and a universal cardinal bound. ⚠️ Проверить, не опирается ли доказательство на ложную оценку FCE-леммы; до прояснения вопроса результаты из этого файла следует считать условными.【F:docs/fce_parity_counterexample.md†L40-L78】
* `family_entropy_cover.lean` packages the cover with the explicit `mBound` estimate required by downstream arguments. ⚠️ Содержимое больше не подтверждено из-за контрпримера паритета и должно быть помечено как гипотеза.【F:docs/fce_parity_counterexample.md†L40-L78】
* `low_sensitivity_cover.lean` completes the decision-tree cover, including the low-sensitivity fallback, without any axioms.
* `Cover/Compute.lean` and `Algorithms/SatCover.lean` provide executable enumerators for experimentation.
* Documentation (`docs/*.md`) has been refreshed to reflect the September 2025 state.

### Current snapshot

* ⚠️ `buildCover` recursion, coverage, and cardinality bound (`Cover/BuildCover.lean`) — требует ревизии после контрпримера.【F:docs/fce_parity_counterexample.md†L40-L78】
* ✅ Sunflower lemma (`Sunflower/Sunflower.lean`) and agreement lemmas (`Agreement.lean`).
* ✅ Entropy monotonicity and bounds (`entropy.lean`, `bound.lean`, `cover_numeric.lean`).
* ✅ Low-sensitivity decision-tree cover (`low_sensitivity_cover.lean`).
* ⚠️ Pending: replace the axioms in `NP_separation.lean` with constructive proofs (magnification and the cover→`MCSP` bridge).

The blueprint remains a living document; contributors should update this file whenever milestones are reached or research priorities shift.
