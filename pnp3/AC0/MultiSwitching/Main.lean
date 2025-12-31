import AC0.MultiSwitching.Encoding

/-!
  pnp3/AC0/MultiSwitching/Main.lean

  Центральная точка входа для будущего multi-switching доказательства.

  Сейчас здесь собраны только "комбинаторные" шаги:
  как из encoding получить существование хорошей рестрикции.
  Реальное построение CCDT и глубинная индукция будут добавлены поверх
  этих лемм в следующих итерациях.

  TODO (bridge):
  определить здесь теорему, которую затем будет использовать
  `ThirdPartyFacts.Facts_Switching.ac0AllSubcubes_length_le_polylog_of_multi_switching`.
  Эта теорема должна выдавать polylog‑оценку на `ac0AllSubcubes` на основе
  полного multi‑switching доказательства (CCDT + encoding/injection + counting).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n k ℓ t : Nat} {F : FormulaFamily n k}

/-!
### Существование хорошей рестрикции

Это минимальный шаг "counting → ∃".  Он будет использоваться
после построения реального encoding/injection.
-/

lemma exists_good_restriction_of_aux_encoding_main
    (A : CCDTAlgorithm n k ℓ t F) (s t' k' m : Nat)
    (witness :
      EncodingWitness (A := A) (s := s)
        (codes := (R_s (n := n) t').product (auxCodes n t k' m)))
    (hcodes :
      (R_s (n := n) t').card * (2 * n * k' * m) ^ t
        < (R_s (n := n) s).card) :
    ∃ ρ ∈ R_s (n := n) s, ¬ BadEvent (A := A) ρ := by
  exact exists_good_restriction_of_aux_encoding
    (A := A) (s := s) (t' := t') (k' := k') (m := m) witness hcodes

end MultiSwitching
end AC0
end Pnp3
