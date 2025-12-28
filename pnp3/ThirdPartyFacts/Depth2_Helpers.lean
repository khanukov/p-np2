/-!
  pnp3/ThirdPartyFacts/Depth2_Helpers.lean

  Helper lemmas for Depth-2 constructive switching proofs.
  These lemmas provide small Bool rewrites used by the constructive proofs.

  Примечание: леммы про `errU` уже доступны в `Core/BooleanBasics.lean`.
  Здесь мы их не дублируем, чтобы не возникало конфликтов имён.
-/
import Core.BooleanBasics

namespace Pnp3
namespace Core

variable {n : Nat}

/--
For a Boolean value b, b = (b == true) is always true.
-/
lemma bool_eq_beq_true (b : Bool) : b = (b == true) := by
  cases b <;> rfl

/--
For a Boolean value b, !b = (b == false) is always true.
-/
lemma bool_not_eq_beq_false (b : Bool) : !b = (b == false) := by
  cases b <;> rfl

end Core
end Pnp3
