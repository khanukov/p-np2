import Pnp.ComplexityClasses
import Mathlib.Data.Real.Basic

/-!
This file contains axioms relating an MCSP lower bound to standard
complexity separations.  The actual results are omitted.
-/

axiom MCSP_lower_bound : ℝ → Prop

axiom magnification_AC0_MCSP :
  (∃ ε > 0, MCSP_lower_bound ε) → Prop

axiom PH_collapse : Prop
axiom karp_lipton : (NP ⊆ Ppoly) → PH_collapse

axiom P_ne_NP_of_MCSP_bound :
  (∃ ε > 0, MCSP_lower_bound ε) → P ≠ NP
