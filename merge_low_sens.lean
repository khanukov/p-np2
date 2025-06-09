import Boolcube

namespace Boolcube

/--
Combines the cover obtained from low-sensitivity functions with the
subexponential cover from the family entropy lemma.  This statement is a
stub meant to capture the intended interface; a full constructive proof
is left for future work.
-/
axiom mergeLowSensitivityCover
  {n : ℕ} (F : Family n) (h : ℝ) (hH : Entropy.H₂ F ≤ h) :
  Cover F

end Boolcube
