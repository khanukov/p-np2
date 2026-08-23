import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]

/-!
## Initial configurations of sequential programs

**Progress classification:** Infrastructure.  This module proves an exact
configuration identity used to start a sequential program from its real input
configuration.  It supplies no verifier, lower bound, padding construction, or
clock discipline, and makes no `P ≠ NP` claim.
-/

/-- The real initial configuration of `seq P Q` is exactly the embedding of
the real initial configuration of its left operand.  Equality includes the
full dependent state, head, and every cell of the widened tape. -/
theorem initialConfig_seq_eq_embedSeqConfig_initialConfig
    (P Q : ConstStatePhasedProgram S) {n : Nat}
    (x : Boolcube.Point n) :
    (seq P Q).toPhased.toTM.initialConfig x =
      embedSeqConfig P Q (P.toPhased.toTM.initialConfig x) := by
  have hstate :
      ((seq P Q).toPhased.toTM.initialConfig x).state =
        (embedSeqConfig P Q (P.toPhased.toTM.initialConfig x)).state := by
    have hfst :
        ((seq P Q).toPhased.toTM.initialConfig x).state.fst =
          (embedSeqConfig P Q (P.toPhased.toTM.initialConfig x)).state.fst :=
      Fin.ext rfl
    exact Sigma.ext hfst (by rw [hfst]; exact heq_of_eq rfl)
  have hhead :
      ((seq P Q).toPhased.toTM.initialConfig x).head =
        (embedSeqConfig P Q (P.toPhased.toTM.initialConfig x)).head :=
    Fin.ext rfl
  have htape :
      ((seq P Q).toPhased.toTM.initialConfig x).tape =
        (embedSeqConfig P Q (P.toPhased.toTM.initialConfig x)).tape := by
    funext i
    by_cases hi : i.val < n
    · simp [TM.initialConfig, embedSeqConfig, hi]
      omega
    · simp [TM.initialConfig, embedSeqConfig, hi]
  cases hL : (seq P Q).toPhased.toTM.initialConfig x with
  | mk sL headL tapeL =>
    cases hR : embedSeqConfig P Q (P.toPhased.toTM.initialConfig x) with
    | mk sR headR tapeR =>
      rw [hL] at hstate hhead htape
      rw [hR] at hstate hhead htape
      have hs : sL = sR := by simpa only using hstate
      have hh : headL = headR := by simpa only using hhead
      have ht : tapeL = tapeR := by simpa only using htape
      subst sR
      subst headR
      subst tapeR
      rfl

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
