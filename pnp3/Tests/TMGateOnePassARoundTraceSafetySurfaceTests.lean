import Complexity.TMVerifier.TuringToolkit.GateOnePassARoundTraceSafety

/-!
# GN-3B2e1b one-round pass-A trace safety surface (2026-09-01)

Definitions receive `#check` pins.  Every public source theorem has one exact
named wrapper rooted directly in that theorem.  No driver, terminal repair or
full-gate surface is exported here.
-/

namespace Pnp3.Tests.TMGateOnePassARoundTraceSafetySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

#check @g1ASeekRevAdvance
#check @g1ASeekRevComplete
#check @G1ASeekStop
#check @G1ASeekOutSkip
#check @G1ASeekInSkip
#check @g1AWalkRoundSteps
#check @G1PassATraceProbes.reqA

theorem check_g1ASeek_reverseFrame_runSafe {W base : Nat}
    (tape : Fin (G1M.tapeLength W) -> Bool) (mode : G1Mode) (ctx : G1Ctx)
    (hmode : G1ASeekMode mode) (hroom : base + 4 < gnLocalSpan W)
    (hfinal : 0 < base ∨
      G1ASeekStop (g1ASeekRevComplete mode (tape ⟨base, by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 1, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 2, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩)
        (tape ⟨base + 3, by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)⟩))) :
    G1RunSafe
      (g1AlignedConfig W (base + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W)) tape
        mode .p3 false false false ctx) 4 :=
  g1ASeek_reverseFrame_runSafe tape mode ctx hmode hroom hfinal

theorem check_g1ASeek_revSkip_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (mode : G1Mode)
    (ctx : G1Ctx) (hmode : G1ASeekMode mode)
    (hskip : ∀ f, f ∈ skipped -> g1ASeekRevAdvance mode f = mode)
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) mode .p3 false false false ctx)
      (4 * skipped.length) :=
  g1ASeek_revSkip_runSafe pre marker skipped suffix mode ctx hmode hskip hword

theorem check_g1ASeekOut_revSkip_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1ASeekOutSkip f)
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) .aSeekOut .p3 false false false ctx)
      (4 * skipped.length) :=
  g1ASeekOut_revSkip_runSafe pre marker skipped suffix ctx hskip hword

theorem check_g1ASeekIn_revSkip_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1ASeekInSkip f)
    (hword : 4 * (pre.length + skipped.length) + 8 < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * (pre.length + skipped.length) + 3) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: skipped ++ suffix).flatMap
          G1Frame.bits)) .aSeekIn .p3 false false false ctx)
      (4 * skipped.length) :=
  g1ASeekIn_revSkip_runSafe pre marker skipped suffix ctx hskip hword

theorem check_g1ASeek_acrossBoundary_runSafe {W : Nat} (pre : List G1Frame)
    (marker : G1Frame) (inner outer suffix : List G1Frame) (ctx : G1Ctx)
    (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hstop : G1ASeekStop (g1ASeekRevAdvance .aSeekIn marker))
    (hword : 4 * (pre.length + (inner.length + outer.length + 1)) + 8 <
      gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W
        (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ marker :: inner ++ .argSep :: outer ++ suffix).flatMap
          G1Frame.bits)) .aSeekOut .p3 false false false ctx)
      (4 * (inner.length + outer.length + 1) + 4) :=
  g1ASeek_acrossBoundary_runSafe pre marker inner outer suffix ctx houter hinner
    hstop hword

theorem check_g1CS_aWalk_seek_index_runSafe {W : Nat}
    (pre inner outer suffix : List G1Frame) (ctx : G1Ctx)
    (houter : ∀ f ∈ outer, G1ASeekOutSkip f)
    (hinner : ∀ f ∈ inner, G1ASeekInSkip f)
    (hword : 4 * (pre.length + (inner.length + outer.length + 1)) + 8 <
      gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W
        (4 * (pre.length + (inner.length + outer.length + 1)) + 3) (by
          exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape ((pre ++ .index :: inner ++ .argSep :: outer ++ suffix).flatMap
          G1Frame.bits)) .aSeekOut .p3 false false false ctx)
      (4 * (inner.length + outer.length + 1) + 4) :=
  g1CS_aWalk_seek_index_runSafe pre inner outer suffix ctx houter hinner hword

theorem check_g1CS_aWalk_fwd_to_cursor_runSafe {W : Nat}
    (pre skipped suffix : List G1Frame) (ctx : G1Ctx)
    (hskip : ∀ f ∈ skipped, G1AWalkSkip f)
    (hroom : 4 * (pre.length + skipped.length + 1) < gnLocalSpan W) :
    G1RunSafe
      (g1AlignedConfig W (4 * pre.length) (by
        exact lt_of_lt_of_le (by omega) (gnLocalSpan_le_g1_tapeLength W))
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .aFwd .p0 false false false ctx) (4 * (skipped.length + 1)) :=
  g1CS_aWalk_fwd_to_cursor_runSafe pre skipped suffix ctx hskip hroom

theorem check_g1CS_aWalk_round_runSafe (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    G1RunSafe
      (g1AWalkConfig r b j (by omega) (by omega) v hv)
      (g1AWalkRoundSteps r j) :=
  g1CS_aWalk_round_runSafe r b j hj1 hnext v v' hv hv'

theorem check_g1CS_aWalk_round_trace_safe (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    G1RunSafe
        (g1AWalkConfig r b j (by omega) (by omega) v hv)
        (g1AWalkRoundSteps r j) ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig r b j (by omega) (by omega) v hv)
          (g1AWalkRoundSteps r j) =
        g1AWalkConfig r b (j + 1) (by omega) hnext v' hv' :=
  g1CS_aWalk_round_trace_safe r b j hj1 hnext v v' hv hv'

theorem check_g1CS_readA_binary_one_round_from_initial_trace_safe
    (r : G1Request) (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bA' bB : Bool) (rest : List Bool) (harg : 0 < r.arg1)
    (hB : r.vals[r.arg2]? = some bB) (hv : r.vals = bA :: rest)
    (hv' : r.vals[1]? = some bA') :
    G1RunSafe (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r + g1AWalkRoundSteps r 0) ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ABinaryCursorSteps r + g1AWalkRoundSteps r 0) =
        g1AWalkConfig r bB 1 (by omega) (g1ALength_pos_of_get hv') bA' hv' :=
  g1CS_readA_binary_one_round_from_initial_trace_safe r hc ht bA bA' bB rest
    harg hB hv hv'

theorem check_literal_round_trace_safe :
    G1RunSafe
        (g1AWalkConfig G1PassATraceProbes.reqA true 0
          (by decide) (by decide) true (by decide)) 53 ∧
      TM.runConfig (M := G1M)
          (g1AWalkConfig G1PassATraceProbes.reqA true 0
            (by decide) (by decide) true (by decide)) 53 =
        g1AWalkConfig G1PassATraceProbes.reqA true 1
          (by decide) (by decide) true (by decide) :=
  G1PassATraceProbes.literal_round_trace_safe

theorem check_literal_one_round_from_initial_trace_safe :
    G1RunSafe
        (G1M.initialConfig (g1Point (encodeG1 G1PassATraceProbes.reqA))) 423 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 G1PassATraceProbes.reqA))) 423 =
        g1AWalkConfig G1PassATraceProbes.reqA true 1
          (by decide) (by decide) true (by decide) :=
  G1PassATraceProbes.literal_one_round_from_initial_trace_safe

end Pnp3.Tests.TMGateOnePassARoundTraceSafetySurface
