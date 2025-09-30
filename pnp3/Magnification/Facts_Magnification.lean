/--
# Внешние факты для магнификации

Содержит формулировки (в качестве аксиом) результатов OPS’21 и обзора JACM’22, необходимых для перехода от нижних оценок по GapMCSP к разделению `NP ⊄ P/poly`.

*Запланированные теоремы*:
- `OPS_trigger_general`
- `OPS_trigger_formulas`
- `Locality_barrier`

Каждая теорема будет сопровождаться ссылкой на источник и комментариями о параметрах, которые должны быть удовлетворены.
-/

namespace Pnp3

/-- TODO: формализовать триггер OPS для общих схем. -/
axiom OPS_trigger_general : Prop

/-- TODO: формализовать триггер OPS для формул. -/
axiom OPS_trigger_formulas : Prop

/-- TODO: формализовать утверждение о барьере локальности из JACM’22. -/
axiom Locality_barrier : Prop

end Pnp3
