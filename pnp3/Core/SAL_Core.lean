/--
# Switching-Atlas Lemma (ядро)

Здесь будет оформлена композиция `shrinkage_to_common_PDT` и `PDT_to_atlas`.

*Текущие планы*:
- определить предпосылку `Shrinkage` для семейства функций;
- построить общий PDT и оценить его глубину;
- преобразовать PDT в атлас и получить оценку размера словаря;
- связать шаги в единую теорему `SAL_Core`.

Пока что файл содержит только аксиоматические заглушки, чтобы зафиксировать целевые сигнатуры.
-/

namespace Pnp3

/-- TODO: формальное определение условия shrinkage. -/
axiom Shrinkage (n : ℕ) : Type

/-- TODO: лемма shrinkage_to_common_PDT. -/
axiom shrinkage_to_common_PDT {n : ℕ} : Shrinkage n → PDT n

/-- TODO: лемма PDT_to_atlas. -/
axiom PDT_to_atlas {n : ℕ} : PDT n → Atlas n

/-- TODO: главная лемма SAL_Core. -/
axiom SAL_Core {n : ℕ} : Shrinkage n → Atlas n

end Pnp3
