import Core.BooleanBasics

/-!
  pnp3/ThirdPartyFacts/BaseSwitching.lean

  После реструктуризации определения для switching-леммы живут в ядре проекта
  (`Core.BooleanBasics`).  Этот модуль оставлен как совместимый фасад: он
  импортирует `Core` и переэкспортирует базовые определения/леммы в пространстве
  имён `ThirdPartyFacts`, чтобы остальной код, опирающийся на прежние имена,
  продолжал компилироваться.  По мере появления доказательства базовой
  switching-леммы именно здесь будет сформулировано итоговое утверждение.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Core

abbrev Literal := Core.Literal
namespace Literal
  export Core.Literal
    (eval holds eval_eq_true_iff eval_eq_false_iff holds_of_eval_true
      eval_true_of_holds)
end Literal

abbrev CnfClause := Core.CnfClause
namespace CnfClause
  export Core.CnfClause
    (width eval holds eval_eq_true_iff eval_eq_false_iff holds_of_mem_eval_true)
end CnfClause

abbrev CNF := Core.CNF
namespace CNF
  export Core.CNF (eval holds eval_eq_true_iff eval_eq_false_iff failureProbability)
end CNF

abbrev DnfTerm := Core.DnfTerm
namespace DnfTerm
  export Core.DnfTerm (eval holds eval_eq_true_iff eval_eq_false_iff)
end DnfTerm

abbrev DNF := Core.DNF
namespace DNF
  export Core.DNF (eval holds eval_eq_true_iff eval_eq_false_iff)
end DNF

abbrev Restriction := Core.Restriction
namespace Restriction
  export Core.Restriction
    (free optionChoices override compatible compatible_iff override_mem
      override_eq_of_mem compatible_iff_override_eq override_idem assign
      assign_mask_eq assign_override_eq freeIndicesList mem_freeIndicesList
      freeCount freeCount_le restrict restrict_agree_of_compatible
      restrict_override isConstantOn isConstantOn_iff hasDecisionTreeOfDepth
      hasDecisionTreeOfDepth_zero weight enumerate)
end Restriction

end ThirdPartyFacts
end Pnp3
