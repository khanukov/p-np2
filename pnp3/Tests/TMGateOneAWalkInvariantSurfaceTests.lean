import Complexity.TMVerifier.TuringToolkit.GateOneAWalkInvariant

/-!
# S5 operand-A invariant surface (2026-08-29)

Definitions are checked only.  Every public S5 theorem has one exact named
wrapper.  This surface contains no anonymous examples and adds no proof fact.
-/

namespace Pnp3.Tests.TMGateOneAWalkInvariantSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

#check @g1AWalkOperand1
#check @g1AWalkOperand2
#check @g1AWalkTail
#check @g1AWalkFrames
#check @g1AWalkFramesMarked
#check @g1AWalkFramesRestored
#check @g1AWalkCursor
#check @g1AWalkDataFrames
#check @g1AWalkInvariantCursorPre
#check @g1AWalkCtx
#check @g1AWalkOuterRun
#check @g1AWalkInnerRun
#check @g1AWalkFwdRun
#check @g1AWalkCursorPre
#check @g1AWalkProbePre
#check @g1AWalkConfig

theorem check_g1AGetn {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) (hj : j < l.length) : l[j] = v :=
  g1AGetn h hj

theorem check_g1ALength_pos_of_get {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) : j < l.length := g1ALength_pos_of_get h

theorem check_g1AWalkCtx_vB (r : G1Request) (b v : Bool) :
    (g1AWalkCtx r b v).vB = v := g1AWalkCtx_vB r b v

theorem check_g1AWalkCtx_res (r : G1Request) (b v : Bool) :
    (g1AWalkCtx r b v).res = g1Residual r.tag b := g1AWalkCtx_res r b v

theorem check_g1AWalkCtx_withVB (r : G1Request) (b v v' : Bool) :
    (g1AWalkCtx r b v).withVB v' = g1AWalkCtx r b v' :=
  g1AWalkCtx_withVB r b v v'

theorem check_g1AWalkFrames_fields (r : G1Request) (j : Nat) :
    g1AWalkFrames r j =
      g1TagRouteFrames r ++ g1AWalkOperand1 r j ++ [.argSep] ++
        g1AWalkOperand2 r ++ [.separator] ++
        (r.vals.take j).map G1Frame.data ++ [.cursor] ++
        (r.vals.drop (j + 1)).map G1Frame.data ++
        [.output false, .finish, .blank] := g1AWalkFrames_fields r j

theorem check_g1AWalkOperand2_eq (r : G1Request) :
    g1AWalkOperand2 r = List.replicate r.arg2 .index :=
  g1AWalkOperand2_eq r

theorem check_g1AWalkOperand1_count_index (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r j).count .index = r.arg1 - j :=
  g1AWalkOperand1_count_index r j

theorem check_g1AWalkOperand1_count_spent (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r j).count .spent = j :=
  g1AWalkOperand1_count_spent r j

theorem check_g1AWalkOperand1_count_cursor (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r j).count .cursor = 0 :=
  g1AWalkOperand1_count_cursor r j

theorem check_g1AWalkOperand1_length (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) : (g1AWalkOperand1 r j).length = r.arg1 :=
  g1AWalkOperand1_length r j hj1

theorem check_g1AWalkOperand2_count_index (r : G1Request) :
    (g1AWalkOperand2 r).count .index = r.arg2 :=
  g1AWalkOperand2_count_index r

theorem check_g1AWalkOperand2_count_spent (r : G1Request) :
    (g1AWalkOperand2 r).count .spent = 0 := g1AWalkOperand2_count_spent r

theorem check_g1AWalkOperand2_count_cursor (r : G1Request) :
    (g1AWalkOperand2 r).count .cursor = 0 := g1AWalkOperand2_count_cursor r

theorem check_g1AWalkOperand2_length (r : G1Request) :
    (g1AWalkOperand2 r).length = r.arg2 := g1AWalkOperand2_length r

theorem check_g1AWalkFrames_count_cursor (r : G1Request) (j : Nat) :
    (g1AWalkFrames r j).count .cursor = 1 := g1AWalkFrames_count_cursor r j

theorem check_g1AWalkFrames_count_spent (r : G1Request) (j : Nat) :
    (g1AWalkFrames r j).count .spent = j := g1AWalkFrames_count_spent r j

theorem check_g1AWalkFrames_count_index (r : G1Request) (j : Nat) :
    (g1AWalkFrames r j).count .index = (r.arg1 - j) + r.arg2 :=
  g1AWalkFrames_count_index r j

theorem check_g1AWalkDataFrames_length (r : G1Request) (j : Nat)
    (hj : j < r.vals.length) :
    (g1AWalkDataFrames r j).length = r.vals.length - 1 :=
  g1AWalkDataFrames_length r j hj

theorem check_g1AWalkDataFrames_count (r : G1Request) (j : Nat) (v : Bool) :
    (g1AWalkDataFrames r j).count (.data v) =
      (r.vals.take j).count v + (r.vals.drop (j + 1)).count v :=
  g1AWalkDataFrames_count r j v

theorem check_g1AWalkFramesRestored_count_cursor (r : G1Request) (j : Nat) :
    (g1AWalkFramesRestored r j).count .cursor = 0 :=
  g1AWalkFramesRestored_count_cursor r j

theorem check_g1AWalkFramesRestored_data (r : G1Request) (j : Nat) :
    g1AWalkFramesRestored r j =
      g1TagRouteFrames r ++ g1AWalkOperand1 r (j + 1) ++ [.argSep] ++
        g1AWalkOperand2 r ++ [.separator] ++ r.vals.map G1Frame.data ++
        [.output false, .finish, .blank] := g1AWalkFramesRestored_data r j

theorem check_g1AWalkFramesRestored_count_spent (r : G1Request) (j : Nat) :
    (g1AWalkFramesRestored r j).count .spent = j + 1 :=
  g1AWalkFramesRestored_count_spent r j

theorem check_g1AWalkFramesRestored_count_index (r : G1Request) (j : Nat) :
    (g1AWalkFramesRestored r j).count .index = (r.arg1 - j - 1) + r.arg2 :=
  g1AWalkFramesRestored_count_index r j

theorem check_g1AWalkFramesRestored_operand1_count_index
    (r : G1Request) (j : Nat) :
    (g1AWalkOperand1 r (j + 1)).count .index = r.arg1 - j - 1 :=
  g1AWalkFramesRestored_operand1_count_index r j

theorem check_g1AWalkFrames_length (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    (g1AWalkFrames r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 :=
  g1AWalkFrames_length r j hj1 hj

theorem check_g1AWalkFrames_length_eq_validation (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    (g1AWalkFrames r j).length =
      (encodeG1Frames r ++ [G1Frame.blank]).length :=
  g1AWalkFrames_length_eq_validation r j hj1 hj

theorem check_g1AWalkFrames_cursor_split (r : G1Request) (j : Nat) :
    g1AWalkInvariantCursorPre r j ++ .cursor :: g1AWalkTail r j =
      g1AWalkFrames r j := g1AWalkFrames_cursor_split r j

theorem check_g1AWalkInvariantCursorPre_length (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    (g1AWalkInvariantCursorPre r j).length = g1AWalkCursor r j :=
  g1AWalkInvariantCursorPre_length r j hj1 hj

theorem check_g1AWalkFrames_cursor_at (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    (g1AWalkFrames r j)[g1AWalkCursor r j]? = some .cursor :=
  g1AWalkFrames_cursor_at r j hj1 hj

theorem check_g1AWalkFrames_physical_length (r : G1Request) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) :
    ((g1AWalkFrames r j).flatMap G1Frame.bits).length =
      (encodeG1 r).length + 4 := g1AWalkFrames_physical_length r j hj1 hj

theorem check_g1AWalkFrames_physical_length_lt_capacity
    (r : G1Request) (j : Nat) (hj1 : j ≤ r.arg1)
    (hj : j < r.vals.length) :
    ((g1AWalkFrames r j).flatMap G1Frame.bits).length <
      G1M.tapeLength (encodeG1 r).length :=
  g1AWalkFrames_physical_length_lt_capacity r j hj1 hj

theorem check_g1AWalkTape_ext (r : G1Request) (j : Nat)
    (tape : Fin (G1M.tapeLength (encodeG1 r).length) → Bool)
    (hcell : ∀ i, tape i =
      g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) i) :
    tape = g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) :=
  g1AWalkTape_ext r j tape hcell

theorem check_g1AWalkTape_eq_of_frames_eq (r : G1Request) (j : Nat)
    (frames : List G1Frame) (hframes : frames = g1AWalkFrames r j) :
    g1ListTape (n := (encodeG1 r).length) (frames.flatMap G1Frame.bits) =
      g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) :=
  g1AWalkTape_eq_of_frames_eq r j frames hframes

theorem check_g1AWalkFramesRestored_length (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    (g1AWalkFramesRestored r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 :=
  g1AWalkFramesRestored_length r j hj1

theorem check_g1AWalkOuterRun_skip (r : G1Request) (j : Nat) :
    ∀ f ∈ g1AWalkOuterRun r j, G1ASeekOutSkip f :=
  g1AWalkOuterRun_skip r j

theorem check_g1AWalkOuterRun_no_argSep (r : G1Request) (j : Nat) :
    G1Frame.argSep ∉ g1AWalkOuterRun r j := g1AWalkOuterRun_no_argSep r j

theorem check_g1AWalkInnerRun_skip (j : Nat) :
    ∀ f ∈ g1AWalkInnerRun j, G1ASeekInSkip f := g1AWalkInnerRun_skip j

theorem check_g1AWalkInnerRun_no_index (j : Nat) :
    G1Frame.index ∉ g1AWalkInnerRun j := g1AWalkInnerRun_no_index j

theorem check_g1AWalkInnerRun_no_argSep (j : Nat) :
    G1Frame.argSep ∉ g1AWalkInnerRun j := g1AWalkInnerRun_no_argSep j

theorem check_g1AWalkFwdRun_skip (r : G1Request) (j : Nat) :
    ∀ f ∈ g1AWalkFwdRun r j, G1AWalkSkip f := g1AWalkFwdRun_skip r j

theorem check_g1AWalkFwdRun_no_cursor (r : G1Request) (j : Nat) :
    G1Frame.cursor ∉ g1AWalkFwdRun r j := g1AWalkFwdRun_no_cursor r j

theorem check_g1AWalkInnerRun_length (j : Nat) :
    (g1AWalkInnerRun j).length = j := g1AWalkInnerRun_length j

theorem check_g1AWalkOuterRun_length (r : G1Request) (j : Nat)
    (hj : j ≤ r.vals.length) :
    (g1AWalkOuterRun r j).length = r.arg2 + j + 1 :=
  g1AWalkOuterRun_length r j hj

theorem check_g1AWalkFwdRun_length (r : G1Request) (j : Nat)
    (hj : j ≤ r.vals.length) :
    (g1AWalkFwdRun r j).length = 2 * j + r.arg2 + 2 :=
  g1AWalkFwdRun_length r j hj

theorem check_g1AWalkSplit_seek (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) .index) ++
        .index :: g1AWalkInnerRun j ++ .argSep :: g1AWalkOuterRun r j ++
        (.cursor :: g1AWalkTail r j) = g1AWalkFrames r j :=
  g1AWalkSplit_seek r j hj1

theorem check_g1AWalkSplit_mark (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) .index) ++
        .index :: (g1AWalkInnerRun j ++ .argSep ::
          (g1AWalkOuterRun r j ++ .cursor :: g1AWalkTail r j)) =
      g1AWalkFrames r j := g1AWalkSplit_mark r j hj1

theorem check_g1AWalkSplit_marked (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) .index) ++
        .spent :: (g1AWalkInnerRun j ++ .argSep ::
          (g1AWalkOuterRun r j ++ .cursor :: g1AWalkTail r j)) =
      g1AWalkFramesMarked r j := g1AWalkSplit_marked r j

theorem check_g1AWalkSplit_marked_fwd (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++ List.replicate (r.arg1 - j - 1) .index ++
        [.spent]) ++ g1AWalkFwdRun r j ++ .cursor :: g1AWalkTail r j =
      g1AWalkFramesMarked r j := g1AWalkSplit_marked_fwd r j

theorem check_g1AWalkSplit_marked_cursor (r : G1Request) (j : Nat) :
    g1AWalkCursorPre r j ++ .cursor :: g1AWalkTail r j =
      g1AWalkFramesMarked r j := g1AWalkSplit_marked_cursor r j

theorem check_g1AWalkSplit_restored_cursor (r : G1Request) (j : Nat)
    (v : Bool) (hj : j < r.vals.length) (hv : r.vals[j] = v) :
    g1AWalkCursorPre r j ++ .data v :: g1AWalkTail r j =
      g1AWalkFramesRestored r j := g1AWalkSplit_restored_cursor r j v hj hv

theorem check_g1AWalkSplit_restored_probe (r : G1Request) (j : Nat)
    (v' : Bool) (hj1 : j + 1 < r.vals.length) (hv' : r.vals[j + 1] = v') :
    g1AWalkProbePre r j ++ .data v' :: ((r.vals.drop (j + 2)).map
        G1Frame.data ++ [.output false, .finish, .blank]) =
      g1AWalkFramesRestored r j :=
  g1AWalkSplit_restored_probe r j v' hj1 hv'

theorem check_g1AWalkSplit_restored_oob (r : G1Request) (j : Nat)
    (hj1 : j + 1 = r.vals.length) :
    g1AWalkProbePre r j ++ .output false :: [.finish, .blank] =
      g1AWalkFramesRestored r j := g1AWalkSplit_restored_oob r j hj1

theorem check_g1AWalkSplit_succ (r : G1Request) (j : Nat) :
    g1AWalkProbePre r j ++ .cursor :: ((r.vals.drop (j + 2)).map
        G1Frame.data ++ [.output false, .finish, .blank]) =
      g1AWalkFrames r (j + 1) := g1AWalkSplit_succ r j

theorem check_g1AWalkMarkPre_length (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++
      List.replicate (r.arg1 - j - 1) G1Frame.index).length =
      r.tag.units + 2 + (r.arg1 - j - 1) := g1AWalkMarkPre_length r j

theorem check_g1AWalkFwdPre_length (r : G1Request) (j : Nat) :
    (g1TagRouteFrames r ++
      List.replicate (r.arg1 - j - 1) G1Frame.index ++
      [G1Frame.spent]).length = r.tag.units + 3 + (r.arg1 - j - 1) :=
  g1AWalkFwdPre_length r j

theorem check_g1AWalkCursorPre_length (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) :
    (g1AWalkCursorPre r j).length = g1AWalkCursor r j :=
  g1AWalkCursorPre_length r j hj1 hj

theorem check_g1AWalkProbePre_length (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) (hj : j + 1 ≤ r.vals.length) :
    (g1AWalkProbePre r j).length = g1AWalkCursor r j + 1 :=
  g1AWalkProbePre_length r j hj1 hj

theorem check_g1AWalkCursor_safe (r : G1Request) (j : Nat)
    (hj : j < r.vals.length) :
    4 * (g1AWalkCursor r j + 2) < G1M.tapeLength (encodeG1 r).length :=
  g1AWalkCursor_safe r j hj

theorem check_g1AWalkConfig_tape (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).tape =
      g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits) :=
  g1AWalkConfig_tape r b j hj1 hj v hv

theorem check_g1AWalkConfig_head (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    ((g1AWalkConfig r b j hj1 hj v hv).head : Nat) =
      4 * g1AWalkCursor r j - 1 := g1AWalkConfig_head r b j hj1 hj v hv

theorem check_g1AWalkConfig_state (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).state.snd =
      g1State .aSeekOut .p3 false false false (g1AWalkCtx r b v) :=
  g1AWalkConfig_state r b j hj1 hj v hv

theorem check_g1AWalkConfig_vB (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).state.snd.ctx.vB = v :=
  g1AWalkConfig_vB r b j hj1 hj v hv

theorem check_g1AWalkConfig_res (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkConfig r b j hj1 hj v hv).state.snd.ctx.res =
      g1Residual r.tag b := g1AWalkConfig_res r b j hj1 hj v hv

theorem check_g1AWalkConfig_walkMode (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j ≤ r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    G1AWalkMode (g1AWalkConfig r b j hj1 hj v hv).state.snd.mode :=
  g1AWalkConfig_walkMode r b j hj1 hj v hv

theorem check_g1AFirstCursorFrames_eq_sigma0 (r : G1Request) (v : Bool)
    (rest : List Bool) (hv : r.vals = v :: rest) :
    g1AFirstCursorFrames r = g1AWalkFrames r 0 :=
  g1AFirstCursorFrames_eq_sigma0 r v rest hv

theorem check_g1APostWriterConfig_eq_sigma0 (r : G1Request) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    g1APostWriterConfig r bA bB =
      g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
        (by rw [hv]; simp) := g1APostWriterConfig_eq_sigma0 r bA bB rest hv

theorem check_g1CS_aWalk_sigma0_exact (r : G1Request) (bA bB : Bool)
    (rest : List Bool) (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (g1AInstallConfig r bB) (g1ALiveInstallSteps r) =
      g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
        (by rw [hv]; simp) := g1CS_aWalk_sigma0_exact r bA bB rest hv

theorem check_g1CS_readA_sigma0_unary_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (v : Bool) (rest : List Bool) (hv : r.vals = v :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r) =
      g1AWalkConfig r false 0 (Nat.zero_le _) (by rw [hv]; simp) v
        (by rw [hv]; simp) := g1CS_readA_sigma0_unary_exact r hc ht v rest hv

theorem check_g1CS_readA_sigma0_binary_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or)
    (bA bB : Bool) (rest : List Bool) (hB : r.vals[r.arg2]? = some bB)
    (hv : r.vals = bA :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r) =
      g1AWalkConfig r bB 0 (Nat.zero_le _) (by rw [hv]; simp) bA
        (by rw [hv]; simp) :=
  g1CS_readA_sigma0_binary_exact r hc ht bA bB rest hB hv

theorem check_g1AWalk_unary_sigma0_steps_le_clock (r : G1Request) :
    g1AUnaryCursorSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AWalk_unary_sigma0_steps_le_clock r

theorem check_g1AWalk_binary_sigma0_steps_le_clock (r : G1Request) :
    g1ABinaryCursorSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AWalk_binary_sigma0_steps_le_clock r

theorem check_g1AWalk_sigma0_no_success_of_empty (r : G1Request)
    (hempty : r.vals = []) : ¬ ∃ v : Bool, r.vals[0]? = some v :=
  g1AWalk_sigma0_no_success_of_empty r hempty

theorem check_g1AWalk_binary_success_not_empty (r : G1Request) (b : Bool)
    (hB : r.vals[r.arg2]? = some b) : r.vals ≠ [] :=
  g1AWalk_binary_success_not_empty r b hB

theorem check_g1CS_readA_sigma0_unary_oob_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .input ∨ r.tag = .not)
    (hempty : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryOOBSteps r) = g1AInstallOOBConfig r false :=
  g1CS_readA_sigma0_unary_oob_exact r hc ht hempty

theorem check_g1AInstallOOBConfig_ne_sigma0 (r : G1Request) (bB v : Bool)
    (h0 : 0 < r.vals.length) (hv : r.vals[0]? = some v) :
    g1AInstallOOBConfig r bB ≠
      g1AWalkConfig r bB 0 (Nat.zero_le _) h0 v hv :=
  g1AInstallOOBConfig_ne_sigma0 r bB v h0 hv

theorem check_g1AWalk_unary_oob_steps_le_clock (r : G1Request) :
    g1AUnaryOOBSteps r ≤ g1Clock (encodeG1 r).length :=
  g1AWalk_unary_oob_steps_le_clock r

theorem check_input_false_sigma0_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqInputFalse))) 131 =
      g1AWalkConfig G1ALiveInstallExamples.reqInputFalse false 0
        (by decide) (by decide) false (by decide) :=
  G1AWalkInvariantExamples.input_false_sigma0_exact

theorem check_or_true_sigma0_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqOrTrue))) 236 =
      g1AWalkConfig G1ALiveInstallExamples.reqOrTrue true 0
        (by decide) (by decide) true (by decide) :=
  G1AWalkInvariantExamples.or_true_sigma0_exact

theorem check_input_empty_oob_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point
          (encodeG1 G1ALiveInstallExamples.reqInputOOB))) 118 =
      g1AInstallOOBConfig G1ALiveInstallExamples.reqInputOOB false :=
  G1AWalkInvariantExamples.input_empty_oob_exact

theorem check_input_empty_no_sigma0_success :
    ¬ ∃ v : Bool, G1ALiveInstallExamples.reqInputOOB.vals[0]? = some v :=
  G1AWalkInvariantExamples.input_empty_no_sigma0_success

end Pnp3.Tests.TMGateOneAWalkInvariantSurface
