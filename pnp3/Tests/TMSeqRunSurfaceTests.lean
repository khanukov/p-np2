import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRun

namespace Pnp3.Tests.TMSeqRunSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]

/-- Pin the reusable two-program theorem's configuration flow and semantic
postcondition surface. -/
def check_seq_run_full
    (P1 P2 : ConstStatePhasedProgram S) {n : Nat}
    (c1 : Configuration (M := P1.toPhased.toTM) n)
    (Post1 : Configuration (M := P1.toPhased.toTM) n → Prop)
    (Post2 : Configuration (M := P2.toPhased.toTM) n → Prop)
    (hLen : P1.toPhased.toTM.tapeLength n ≤ P2.toPhased.toTM.tapeLength n)
    (spec1 : RunSpec P1 c1 Post1)
    (spec2 :
      let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
      let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
        Nat.lt_of_lt_of_le c1Final.head.isLt hLen
      RunSpec P2 (liftP1ToP2 P1 P2 c1Final hHead) Post2) :
    let c1Final := runConfig (M := P1.toPhased.toTM) c1 (P1.timeBound n)
    let hHead : c1Final.head.val < P2.toPhased.toTM.tapeLength n :=
      Nat.lt_of_lt_of_le c1Final.head.isLt hLen
    let c2Init := liftP1ToP2 P1 P2 c1Final hHead
    let c2Final := runConfig (M := P2.toPhased.toTM) c2Init (P2.timeBound n)
    runConfig (M := (seq P1 P2).toPhased.toTM)
        (embedSeqConfig P1 P2 c1) ((seq P1 P2).timeBound n) =
      embedSeqP2Config P1 P2 c2Final ∧
    Post1 c1Final ∧ Post2 c2Final :=
  seq_run_full P1 P2 c1 Post1 Post2 hLen spec1 spec2

/-- Pin that the concrete theorem needs only the first gate's tape bound; the
second follows from ordered destinations. -/
def check_gateConstCS_seq_run_full
    (b1 b2 : Bool) (d1 d2 : Nat) (hD : d1 ≤ d2) {n : Nat}
    (c1 : Configuration
      (M := (Pnp3.Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS b1 d1).toPhased.toTM) n)
    (hPhase : c1.state.fst.val = 0)
    (hState : c1.state.snd = (false, false))
    (hBound1 : (c1.head : Nat) + d1 <
      (Pnp3.Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS b1 d1).toPhased.toTM.tapeLength n) :=
  Pnp3.Internal.PsubsetPpoly.TM.GateEvalCS.gateConstCS_seq_run_full
    b1 b2 d1 d2 hD c1 hPhase hState hBound1

end Pnp3.Tests.TMSeqRunSurface
