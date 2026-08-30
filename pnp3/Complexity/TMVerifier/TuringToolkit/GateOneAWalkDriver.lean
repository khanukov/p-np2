import Complexity.TMVerifier.TuringToolkit.GateOneAWalkRound

/-!
# S7 exact operand-A induction and driver (2026-08-30)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

This module iterates S6's exact normal-round theorem from the merged `Σᴬ(0)`
invariant.  Round `j` costs exactly `16*j + 8*arg2 + 45`, hence the first `m`
rounds cost

`∑ j in [0,m), (16*j + 8*arg2 + 45)
  = 8*m^2 + (8*arg2 + 37)*m`.

There is no padding, advice or caller-selected budget.  The driver carries an
explicit value function and a `getElem?` witness for every slot `0..m`; its
endpoint is the exact S5/S6 configuration `Σᴬ(m)`, including tape, head,
control, residual, latest `vB`, cursor and count invariants.  Separate
capstones compose the real unary and successful-binary S5 prefixes.

At `m = arg1`, the driver appends S6's exact exhaustion seek to local `aExh`.
The S3b2b terminal macro is also composed: it returns to the cursor, restores
the hidden data bit, removes the cursor and stops exactly at the live
`aRepairStart` boundary.  S8b composes the next activation step separately.
A first-missing-successor theorem composes S6's data-OOB round.  No A-repair
sweep, result, output or acceptance theorem is added in this S7 module.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Exact accumulated schedule -/

/-- Exact cost of normal rounds `0, ..., m-1`. -/
def g1AWalkDriverSteps (r : G1Request) (m : Nat) : Nat :=
  8 * m ^ 2 + (8 * r.arg2 + 37) * m

@[simp] theorem g1AWalkDriverSteps_zero (r : G1Request) :
    g1AWalkDriverSteps r 0 = 0 := by simp [g1AWalkDriverSteps]

private theorem g1ADriverSq_succ (m : Nat) :
    (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by
  rw [Nat.pow_two, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
  omega

/-- Adding round `m` adds exactly S6's normal-round cost. -/
theorem g1AWalkDriverSteps_succ (r : G1Request) (m : Nat) :
    g1AWalkDriverSteps r (m + 1) =
      g1AWalkDriverSteps r m + g1AWalkRoundSteps r m := by
  simp only [g1AWalkDriverSteps, g1AWalkRoundSteps, g1ADriverSq_succ,
    Nat.mul_add, Nat.mul_one]
  omega

/-- Provenance identity: the closed form is the finite sum of S6 costs. -/
theorem g1AWalkDriverSteps_eq_sum (r : G1Request) (m : Nat) :
    g1AWalkDriverSteps r m =
      ((List.range m).map (fun j => 16 * j + 8 * r.arg2 + 45)).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ← ih,
        g1AWalkDriverSteps_succ]
      simp [g1AWalkRoundSteps]

/-! ## Exact induction and invariant projections -/

/-- **Exact caller-supplied driver.**  The function `v` and hypothesis `hv`
are explicit witnesses for every data slot `0..m`. -/
theorem g1CS_aWalk_driver_exact (r : G1Request) (b : Bool) (m : Nat)
    (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkDriverSteps r m) =
      g1AWalkConfig r b m hm1 hm (v m) (hv m (Nat.le_refl _)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m < r.vals.length := by omega
      rw [g1AWalkDriverSteps_succ, runConfig_add,
        ih (by omega) hm' (fun j hj => hv j (by omega))]
      exact g1CS_aWalk_round_exact r b m (by omega) hm (v m) (v (m + 1))
        (hv m (by omega)) (hv (m + 1) (Nat.le_refl _))

/-- The exact endpoint exposes every merged `Σᴬ(m)` invariant requested by the
driver: tape/head/control/context, latest value, unique cursor and both field
progress counts. -/
theorem g1CS_aWalk_driver_preservation (r : G1Request) (b : Bool) (m : Nat)
    (hm1 : m ≤ r.arg1) (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) :
    let out := TM.runConfig (M := G1M)
      (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
        (hv 0 (by omega))) (g1AWalkDriverSteps r m)
    out.tape = g1ListTape ((g1AWalkFrames r m).flatMap G1Frame.bits) ∧
      (out.head : Nat) = 4 * g1AWalkCursor r m - 1 ∧
      out.state.snd =
        g1State .aSeekOut .p3 false false false (g1AWalkCtx r b (v m)) ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v m ∧
      (g1AWalkFrames r m).count .cursor = 1 ∧
      (g1AWalkFrames r m).count .spent = m ∧
      (g1AWalkFrames r m).count .index = (r.arg1 - m) + r.arg2 ∧
      (g1AWalkOperand1 r m).count .index = r.arg1 - m := by
  dsimp only
  rw [g1CS_aWalk_driver_exact r b m hm1 hm v hv]
  exact ⟨rfl, rfl, rfl, g1AWalkConfig_res _ _ _ _ _ _ _, rfl,
    g1AWalkFrames_count_cursor _ _, g1AWalkFrames_count_spent _ _,
    g1AWalkFrames_count_index _ _, g1AWalkOperand1_count_index _ _⟩

/-! ## Real-initial S5 prefix compositions -/

/-- Exact real-initial unary prefix followed by `m` normal rounds. -/
theorem g1CS_readA_driver_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (m : Nat) (hm1 : m ≤ r.arg1)
    (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) (rest : List Bool)
    (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r + g1AWalkDriverSteps r m) =
      g1AWalkConfig r false m hm1 hm (v m) (hv m (Nat.le_refl _)) := by
  rw [runConfig_add,
    g1CS_readA_sigma0_unary_exact r hc ht (v 0) rest hvals]
  exact g1CS_aWalk_driver_exact r false m hm1 hm v hv

/-- Exact real-initial successful-binary prefix followed by `m` normal rounds.
The physically read operand-B witness remains explicit. -/
theorem g1CS_readA_driver_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (bB : Bool)
    (hB : r.vals[r.arg2]? = some bB) (m : Nat) (hm1 : m ≤ r.arg1)
    (hm : m < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ m → r.vals[j]? = some (v j)) (rest : List Bool)
    (hvals : r.vals = v 0 :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ABinaryCursorSteps r + g1AWalkDriverSteps r m) =
      g1AWalkConfig r bB m hm1 hm (v m) (hv m (Nat.le_refl _)) := by
  rw [runConfig_add,
    g1CS_readA_sigma0_binary_exact r hc ht (v 0) bB rest hB hvals]
  exact g1CS_aWalk_driver_exact r bB m hm1 hm v hv

/-! ## Polynomial provenance and unchanged-clock bounds -/

/-- A concrete S7-local quadratic in the request's encoded frame mass. -/
def g1AWalkDriverPoly (r : G1Request) : Nat :=
  64 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2

/-- The exact schedule is bounded by the local quadratic whenever the driver
stays inside operand A. -/
theorem g1AWalkDriverSteps_le_poly (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) : g1AWalkDriverSteps r m ≤ g1AWalkDriverPoly r := by
  let S := r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6
  have hmS : m ≤ S := by dsimp [S]; omega
  have haS : r.arg2 ≤ S := by dsimp [S]; omega
  have hsq : m ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hmS 2
  have hcross : r.arg2 * m ≤ S ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul haS hmS
  have hlin : m ≤ S ^ 2 := by
    have hSS : S ≤ S ^ 2 := by
      simpa [pow_two] using Nat.le_mul_of_pos_right S (by dsimp [S]; omega)
    exact hmS.trans hSS
  simp only [g1AWalkDriverSteps, g1AWalkDriverPoly]
  change 8 * m ^ 2 + (8 * r.arg2 + 37) * m ≤ 64 * S ^ 2
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

private theorem g1ADriverClock_quad (N : Nat) :
    g1Clock (4 * N) = 8192 * N ^ 2 + (4096 * N + 1024) := by
  rw [g1Clock, g1ADriverSq_succ, Nat.mul_pow,
    show (4 : Nat) ^ 2 = 16 from rfl]
  omega

/-- The S7-local quadratic itself fits the unchanged public clock. -/
theorem g1AWalkDriverPoly_le_clock (r : G1Request) :
    g1AWalkDriverPoly r ≤ g1Clock (encodeG1 r).length := by
  rw [encodeG1_length, g1ADriverClock_quad]
  simp only [g1AWalkDriverPoly]
  omega

theorem g1AWalkDriverSteps_le_clock (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) :
    g1AWalkDriverSteps r m ≤ g1Clock (encodeG1 r).length :=
  (g1AWalkDriverSteps_le_poly r m hm1).trans (g1AWalkDriverPoly_le_clock r)

/-- The exact unary S5 prefix plus the S7 accumulated schedule fits the same
unchanged public clock. -/
theorem g1AUnaryDriverSteps_le_clock (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) :
    g1AUnaryCursorSteps r + g1AWalkDriverSteps r m ≤
      g1Clock (encodeG1 r).length := by
  let S := r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6
  have hd := g1AWalkDriverSteps_le_poly r m hm1
  have hd' : g1AWalkDriverSteps r m ≤ 64 * S ^ 2 := by
    simpa only [g1AWalkDriverPoly, S] using hd
  have hS : S ≤ S ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_right S (by dsimp [S]; omega)
  have hlen := encodeG1_length r
  rw [hlen, g1ADriverClock_quad]
  simp only [g1AUnaryCursorSteps, g1ALiveInstallSteps, g1UActivatedSteps,
    g1UReadASteps, g1ReadARouteSteps, g1ReadBHandoffSteps,
    g1AUnaryRewindSteps, hlen]
  change _ ≤ 8192 * S ^ 2 + (4096 * S + 1024)
  omega

/-- The exact successful-binary S5 prefix plus the S7 accumulated schedule
also fits the unchanged public clock. -/
theorem g1ABinaryDriverSteps_le_clock (r : G1Request) (m : Nat)
    (hm1 : m ≤ r.arg1) :
    g1ABinaryCursorSteps r + g1AWalkDriverSteps r m ≤
      g1Clock (encodeG1 r).length := by
  let S := r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6
  have hd := g1AWalkDriverSteps_le_poly r m hm1
  have hd' : g1AWalkDriverSteps r m ≤ 64 * S ^ 2 := by
    simpa only [g1AWalkDriverPoly, S] using hd
  have hsq : 8 * r.arg2 ^ 2 ≤ 128 * S ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by dsimp [S]; omega) 2)
  have hS : S ≤ S ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_right S (by dsimp [S]; omega)
  have hlen := encodeG1_length r
  rw [hlen, g1ADriverClock_quad]
  simp only [g1ABinaryCursorSteps, g1ALiveInstallSteps, g1BActivatedSteps,
    g1BPassASteps, g1BReadSteps, g1InstallScanSteps, g1ZPassASteps,
    g1ReadBSteps, g1RepairSteps, g1ReadBHandoffSteps, hlen]
  change _ ≤ 8192 * S ^ 2 + (4096 * S + 1024)
  split_ifs <;> omega

/-! ## Exhaustion and first-missing-successor drivers -/

/-- Exact cost from `Σᴬ(0)` through all `arg1` normal rounds and the S6
operand-index exhaustion seek. -/
def g1AWalkExhaustDriverSteps (r : G1Request) : Nat :=
  g1AWalkDriverSteps r r.arg1 + g1AWalkExhaustSteps r

theorem g1CS_aWalk_exhaust_driver_exact (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _)
          (by omega) (v 0) (hv 0 (by omega)))
        (g1AWalkExhaustDriverSteps r) =
      g1AWalkExhaustConfig r b (v r.arg1) hlen
        (hv r.arg1 (Nat.le_refl _)) := by
  rw [g1AWalkExhaustDriverSteps, runConfig_add,
    g1CS_aWalk_driver_exact r b r.arg1 (Nat.le_refl _) hlen v hv]
  exact g1CS_aWalk_exhaust_exact r b (v r.arg1) hlen
    (hv r.arg1 (Nat.le_refl _))

/-- At the first absent successor, execute the preceding normal rounds and the
separate S6 OOB round; the endpoint is cursor-free `bOOB`, not `aExh`. -/
theorem g1CS_aWalk_oob_driver_exact (r : G1Request) (b : Bool) (t : Nat)
    (ht1 : t < r.arg1) (hlast : t + 1 = r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ t → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _) (by omega) (v 0)
          (hv 0 (by omega)))
        (g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t) =
      g1AWalkOOBConfig r b t ht1 (by omega) (v t)
        (hv t (Nat.le_refl _)) := by
  rw [runConfig_add,
    g1CS_aWalk_driver_exact r b t (by omega) (by omega) v hv]
  exact g1CS_aWalk_round_oob_exact r b t ht1 hlast (v t)
    (hv t (Nat.le_refl _))

theorem g1AWalkExhaustDriverSteps_le_clock (r : G1Request) :
    g1AWalkExhaustDriverSteps r ≤ g1Clock (encodeG1 r).length := by
  let S := r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6
  have hp := g1AWalkDriverSteps_le_poly r r.arg1 (Nat.le_refl _)
  have hp' : g1AWalkDriverSteps r r.arg1 ≤ 64 * S ^ 2 := by
    simpa only [g1AWalkDriverPoly, S] using hp
  have hS : S ≤ S ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_right S (by dsimp [S]; omega)
  rw [encodeG1_length, g1ADriverClock_quad]
  simp only [g1AWalkExhaustDriverSteps, g1AWalkExhaustSteps]
  change g1AWalkDriverSteps r r.arg1 + (8 * r.arg1 + 4 * r.arg2 + 12) ≤
    8192 * S ^ 2 + (4096 * S + 1024)
  omega

/-! ## S3b2b terminal composition -/

/-- Cursor-free designated word at the live A-repair handoff. -/
def g1AWalkDoneFrames (r : G1Request) : List G1Frame :=
  g1TagRouteFrames r ++ g1AWalkOperand1 r r.arg1 ++ [G1Frame.argSep] ++
    g1AWalkOperand2 r ++ [G1Frame.separator] ++ r.vals.map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- Exact S3b2b tail cost from local `aExh` to `aRepairStart`. -/
def g1AWalkTerminalSteps (r : G1Request) : Nat :=
  8 * r.arg1 + 4 * r.arg2 + 24

/-- The accumulated rounds, exhaustion seek and S3b2b terminal tail together
still fit the unchanged public clock. -/
theorem g1AWalkFullDriverSteps_le_clock (r : G1Request) :
    g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r ≤
      g1Clock (encodeG1 r).length := by
  let S := r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6
  have hp := g1AWalkDriverSteps_le_poly r r.arg1 (Nat.le_refl _)
  have hp' : g1AWalkDriverSteps r r.arg1 ≤ 64 * S ^ 2 := by
    simpa only [g1AWalkDriverPoly, S] using hp
  have hS : S ≤ S ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_right S (by dsimp [S]; omega)
  rw [encodeG1_length, g1ADriverClock_quad]
  simp only [g1AWalkExhaustDriverSteps, g1AWalkExhaustSteps,
    g1AWalkTerminalSteps]
  change g1AWalkDriverSteps r r.arg1 + (8 * r.arg1 + 4 * r.arg2 + 12) +
    (8 * r.arg1 + 4 * r.arg2 + 24) ≤
      8192 * S ^ 2 + (4096 * S + 1024)
  omega

set_option linter.unusedVariables false in
def g1AWalkRepairStartConfig (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length (4 * (g1AWalkCursor r r.arg1 + 1))
    (by have h := g1AWalkCursor_safe r r.arg1 hj; omega)
    (g1ListTape ((g1AWalkDoneFrames r).flatMap G1Frame.bits))
    .aRepairStart .p0 false false false (g1AWalkCtx r b v)

@[simp] theorem g1AWalkRepairStartConfig_tape (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).tape =
      g1ListTape ((g1AWalkDoneFrames r).flatMap G1Frame.bits) := rfl

@[simp] theorem g1AWalkRepairStartConfig_head (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    ((g1AWalkRepairStartConfig r b v hj hv).head : Nat) =
      4 * (g1AWalkCursor r r.arg1 + 1) := rfl

@[simp] theorem g1AWalkRepairStartConfig_state (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).state.snd =
      g1State .aRepairStart .p0 false false false (g1AWalkCtx r b v) := rfl

@[simp] theorem g1AWalkRepairStartConfig_res (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).state.snd.ctx.res =
      g1Residual r.tag b := by simp [g1AWalkRepairStartConfig, g1State]

@[simp] theorem g1AWalkRepairStartConfig_vB (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkRepairStartConfig r b v hj hv).state.snd.ctx.vB = v := rfl

private theorem g1ADriverDrop_cons (l : List Bool) (j : Nat)
    (hj : j < l.length) : l.drop j = l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => exact ih j (by simpa using hj)

theorem g1AWalkSplit_done (r : G1Request) (v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    g1AWalkExhaustPre r ++ G1Frame.argSep ::
        g1AWalkFwdRun r r.arg1 ++ G1Frame.data v :: g1AWalkTail r r.arg1 =
      g1AWalkDoneFrames r := by
  have hdv : r.vals[r.arg1] = v := g1AGetn hv hj
  have hd : r.vals.map G1Frame.data =
      (r.vals.take r.arg1).map G1Frame.data ++ G1Frame.data v ::
        (r.vals.drop (r.arg1 + 1)).map G1Frame.data := by
    conv_lhs => rw [← List.take_append_drop r.arg1 r.vals]
    rw [List.map_append, g1ADriverDrop_cons r.vals r.arg1 hj, hdv]
    simp
  rw [g1AWalkDoneFrames, g1AWalkExhaustPre, g1AWalkFwdRun,
    g1AWalkInnerRun, g1AWalkOuterRun, g1AWalkTail, g1TagRouteFrames,
    g1AWalkOperand1, Nat.sub_self, hd]
  simp [List.append_assoc]

/-- The exhaustion word in the exact `g1AWalkFwdRun` spelling consumed by the
S3b2b terminal macro. -/
theorem g1AWalkSplit_exhaust_fwd (r : G1Request) :
    g1AWalkExhaustPre r ++ G1Frame.argSep ::
        g1AWalkFwdRun r r.arg1 ++ G1Frame.cursor :: g1AWalkTail r r.arg1 =
      g1AWalkFrames r r.arg1 := by
  simpa [g1AWalkFwdRun, List.append_assoc] using g1AWalkSplit_exhaust r

@[simp] theorem g1AWalkDoneFrames_count_cursor (r : G1Request) :
    (g1AWalkDoneFrames r).count .cursor = 0 := by
  have h := g1AWalkFramesRestored_count_cursor r r.arg1
  simpa [g1AWalkDoneFrames, g1AWalkFramesRestored] using h

set_option maxHeartbeats 4000000 in
theorem g1CS_aWalk_terminal_from_exhaust_exact (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M) (g1AWalkExhaustConfig r b v hj hv)
        (g1AWalkTerminalSteps r) =
      g1AWalkRepairStartConfig r b v hj hv := by
  have hlen := g1AWalkFwdRun_length r r.arg1 (by omega)
  have hsafe := g1AWalkCursor_safe r r.arg1 hj
  have h := g1CS_aWalk_terminal_exact (encodeG1 r).length
    (g1AWalkExhaustPre r) (g1AWalkFwdRun r r.arg1)
    (g1AWalkTail r r.arg1) (g1AWalkCtx r b v)
    (g1AWalkFwdRun_skip r r.arg1) (by
      rw [g1AWalkExhaustPre_length, hlen]
      simp only [g1AWalkCursor] at hsafe ⊢
      omega)
  rw [g1AWalkSplit_exhaust_fwd] at h
  simp only [g1AWalkCtx_vB] at h
  rw [g1AWalkSplit_done r v hj hv] at h
  simp only [g1AWalkExhaustPre_length, hlen,
    show 4 * (2 * r.arg1 + r.arg2 + 2 + 4) =
      8 * r.arg1 + 4 * r.arg2 + 24 by omega,
    show 4 * (r.tag.units + 1 + (2 * r.arg1 + r.arg2 + 2 + 2)) =
      4 * (g1AWalkCursor r r.arg1 + 1) by
        simp only [g1AWalkCursor]; omega] at h
  exact h

/-- Full caller-supplied S7 execution through exhaustion and the exact
cursor-free S3b2b live handoff boundary. -/
theorem g1CS_aWalk_full_driver_exact (r : G1Request) (b : Bool)
    (hlen : r.arg1 < r.vals.length) (v : Nat → Bool)
    (hv : ∀ j, j ≤ r.arg1 → r.vals[j]? = some (v j)) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b 0 (Nat.zero_le _)
          (by omega) (v 0) (hv 0 (by omega)))
        (g1AWalkExhaustDriverSteps r + g1AWalkTerminalSteps r) =
      g1AWalkRepairStartConfig r b (v r.arg1) hlen
        (hv r.arg1 (Nat.le_refl _)) := by
  rw [runConfig_add, g1CS_aWalk_exhaust_driver_exact r b hlen v hv]
  exact g1CS_aWalk_terminal_from_exhaust_exact r b (v r.arg1)
    hlen
    (hv r.arg1 (Nat.le_refl _))

/-! ## Literal driver probes -/

namespace G1AWalkDriverExamples

def reqDriver : G1Request := ⟨.input, 2, 0, [false, true, false]⟩
def reqZero : G1Request := ⟨.input, 0, 0, [true]⟩

theorem requests_canonical : reqDriver.Canonical ∧ reqZero.Canonical := by decide

theorem zero_round_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig reqDriver false 0 (by decide) (by decide) false (by decide))
      0 =
    g1AWalkConfig reqDriver false 0 (by decide) (by decide) false
      (by decide) := by rfl

theorem one_round_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig reqDriver false 0 (by decide) (by decide) false (by decide))
      45 =
    g1AWalkConfig reqDriver false 1 (by decide) (by decide) true
      (by decide) := by
  simpa [g1AWalkDriverSteps, reqDriver] using
    g1CS_aWalk_driver_exact reqDriver false 1 (by decide) (by decide)
      (fun j => [false, true, false][j]!) (by decide)

theorem two_round_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig reqDriver false 0 (by decide) (by decide) false (by decide))
      106 =
    g1AWalkConfig reqDriver false 2 (by decide) (by decide) false
      (by decide) := by
  simpa [g1AWalkDriverSteps, reqDriver] using
    g1CS_aWalk_driver_exact reqDriver false 2 (by decide) (by decide)
      (fun j => [false, true, false][j]!) (by decide)

theorem exhaustion_driver_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig reqDriver false 0 (by decide) (by decide) false (by decide))
      134 =
    g1AWalkExhaustConfig reqDriver false false (by decide) (by decide) := by
  simpa [g1AWalkExhaustDriverSteps, g1AWalkDriverSteps,
    g1AWalkExhaustSteps, reqDriver] using
    g1CS_aWalk_exhaust_driver_exact reqDriver false (by decide)
      (fun j => [false, true, false][j]!) (by decide)

/-- Nonvacuous `arg1 = 0`: zero normal rounds, then the 12-step exhaustion. -/
theorem zero_operand_exhaustion_exact :
    TM.runConfig (M := G1M)
      (g1AWalkConfig reqZero false 0 (by decide) (by decide) true (by decide))
      12 =
    g1AWalkExhaustConfig reqZero false true (by decide) (by decide) := by
  simpa [g1AWalkExhaustDriverSteps, g1AWalkDriverSteps,
    g1AWalkExhaustSteps, reqZero] using
    g1CS_aWalk_exhaust_driver_exact reqZero false (by decide)
      (fun _ => true) (by decide)

theorem two_round_from_initial_exact :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 reqDriver)))
      277 =
    g1AWalkConfig reqDriver false 2 (by decide) (by decide) false
      (by decide) := by
  simpa [g1AUnaryCursorSteps, g1UActivatedSteps, g1UReadASteps,
    g1ReadARouteSteps, g1ReadBHandoffSteps, g1AUnaryRewindSteps,
    g1ALiveInstallSteps, g1AWalkDriverSteps, reqDriver] using
    g1CS_readA_driver_unary_exact reqDriver requests_canonical.1 (Or.inl rfl)
      2 (by decide) (by decide) (fun j => [false, true, false][j]!)
      (by decide) [true, false] rfl

end G1AWalkDriverExamples

end Pnp3.Internal.PsubsetPpoly.TM
