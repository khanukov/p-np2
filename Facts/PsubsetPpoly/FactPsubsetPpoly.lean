import Facts.PsubsetPpoly.Proof.Complexity.PsubsetPpoly

/-!
# Fact: `P ⊆ P/poly`

This lightweight module exposes the proposition and witness packaged by the
standalone fact development.  The implementation of the constructive proof
lives in the dedicated `Facts/PsubsetPpoly` package; here we only re-export the
result so that downstream projects can depend on a stable interface without
pulling in the underlying simulation files.
-/

namespace Facts
namespace PsubsetPpoly

open Complexity

/-- Proposition representing the inclusion `P ⊆ P/poly`. -/
abbrev Statement : Prop := P ⊆ Ppoly

/-- Proof witness for the fact `P ⊆ P/poly`. -/
theorem complexity_P_subset_Ppoly : Statement :=
  Proof.complexity_P_subset_Ppoly

end PsubsetPpoly
end Facts
