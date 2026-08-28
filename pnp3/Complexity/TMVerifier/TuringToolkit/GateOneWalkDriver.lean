import Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariant

/-!
# G1 cursor walk: the driver, the terminal and the positive-index operand-2 read

**Progress classification: Infrastructure.**

PR3c.  `GateOneWalkInvariant` states the cursor-walk invariant `Σ(j)`, reaches
`Σ(0)` from the real initial configuration and executes exactly **one** round.
This module **iterates** that round, closes the walk at `j = arg2` and turns the
result into the first **arbitrary positive-index operand-2 read** of the G1
machine.  No new mode, no new state field, no new `Nat`, and `g1Clock` is
unchanged; every step composes merged atoms and the transition table is never
unfolded.  Throughout, `u = tag.units`, `a1 = arg1`, `a = arg2`,
`m = vals.length`.

## The loop clock and the three executed capstones

`g1BLoopSteps k = 8k² + 29k` is the cumulative cost of the first `k` rounds,
with the recurrence `g1BLoopSteps_succ` (`= g1BLoopSteps k + (16k + 37)`,
exactly the cost of `g1CS_walk_iteration_exact` at `j = k`) and the closed form
`g1BLoopSteps_eq_sum` (`= ∑_{j<k} (16j + 37)`).

* `g1CS_walk_loop_exact` — the **induction**.  For every `k ≤ a` with `k < m`
  and `hv : r.vals[k]? = some v`, exactly `g1WalkInstallSteps r +
  g1BLoopSteps k` genuine steps run `G1M.initialConfig` to `Σ(r, k, v)` — the
  invariant **with `hv` itself as its hidden-bit argument**, so the latch
  relation is not weakened along the iteration.  The base case *is*
  `g1CS_walk_install_exact`; the successor composes one exact `16k + 37` round,
  generating the prior round's proof `r.vals[k]? = some r.vals[k]` from `k < m`.
* `g1CS_walk_terminal_exact` — the **successful terminal** at `k = a < m`.
  `Σ(a)` has `index⁰`, so the reverse seek exhausts into `bExh` at the `argSep`
  opening the field instead of marking: `(8a + 8) + (8a + 12) + 4 + 4 =
  16a + 28` steps run `g1CS_walk_seek_exhaust`, `g1CS_walk_exh_to_cursor`,
  `g1CS_walk_turn_fin` and `g1CS_walk_fin_restore` and land in
  `readAResetStart`, head `4 * (g1WalkCursor r a + 1)`, data region exactly
  `vals`, **no cursor**, operand-2 field `spent^a`, `vB = vals[a]`.
* `g1CS_readB_positive_exact` — the **public arbitrary positive-index read**:
  for `0 < a` and `r.vals[a]? = some b`, exactly `g1BReadSteps r =
  g1WalkInstallSteps r + 8a² + 45a + 28 = g1InstallScanSteps r + 8a² + 45a + 37`
  genuine steps take `G1M.initialConfig` to that pass-A reset handoff with
  `G1Ctx.vB = b`.  The value is the **actual** `r.vals[r.arg2]`, read out of the
  unannotated data region and never supplied to the machine.

## The aggregated out-of-range branch

`g1BSpentFrames r s` is the one **repair-pending** layout family both outcomes
end on: operand 2 split as `index^(a-s) · spent^s`, data region exactly `vals`,
**no cursor**.  `g1WalkFramesRestored r j = g1BSpentFrames r (j+1)`, the
terminal tape is `g1BSpentFrames r a`, the out-of-range tape
`g1BSpentFrames r m` — which for `m = 0` is *bit-for-bit the initial word*.
`g1CS_readB_positive_oob_exact` aggregates both out-of-range branches of a
positive index (`m ≤ a`) into one exact configuration equality with the single
count `g1BOOBSteps r = g1InstallScanSteps r + 8m² + 29m + 4`: `m = 0` is the
empty-data installation branch (`+4`), `m > 0` composes the installation,
`g1BLoopSteps (m-1)` and the `16(m-1) + 32` out-of-range round; the context is
`g1BOOBCtx r` — `g1Ctx0` when `vals = []`, `g1Ctx0.withVB vals[m-1]` otherwise.

`m ≤ a` and `a < m` are exhaustive and the two endpoints differ
(`g1CS_readB_positive_oob_ne_success`), so exactly **one** public capstone
applies to every data region.  `g1BReadSteps_le_clock` and
`g1BOOBSteps_le_clock` keep both totals inside the **unchanged** `g1Clock` and
are proved before the public capstones; every summand is a concrete polynomial
in the request's own fields — no pad, no advice, no free budget parameter.

## Explicit deferrals

The `spent ↦ index` **repair sweep** is not started *here*: both endpoints of
this module leave the operand-2 field consumed, so neither final tape is the
canonical word and no theorem of this module claims otherwise.  The sweep that
restores the successful one is `GateOneRepairDriver` (Repair-2a), which composes
behind `g1CS_readB_positive_exact`; the out-of-range endpoint stays unrepaired
there too.  Also absent and claimed nowhere: **pass A**, the
**combine** step, the **output write**, `TM.accepts`, a full-clock theorem,
gate-semantics correctness, the acceptance gate, multi-gate composition, the
specification-level bridge, and non-canonical or padded tapes.  Reaching `bOOB`
is a boundary, not a verdict.  Every execution statement is scoped to
`encodeG1 r`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Small `getElem?`, list and configuration helpers -/

private theorem g1BLength_pos_of_get {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) : j < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact Option.noConfusion h

private theorem g1BGetn {l : List Bool} {j : Nat} {v : Bool}
    (h : l[j]? = some v) (hj : j < l.length) : l[j] = v := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

private theorem g1BDrop_cons (l : List Bool) (j : Nat) (hj : j < l.length) :
    l.drop j = l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => exact ih j (by simpa using hj)

/-- Two aligned configurations with provably equal heads and tapes are equal;
the safety proofs are irrelevant.  This is the only place the driver moves
between two spellings of one endpoint, never touching state or context. -/
private theorem g1BAligned_congr (n h h' : Nat)
    (hh : h < G1M.tapeLength n) (hh' : h' < G1M.tapeLength n) (heq : h = h')
    (tape tape' : Fin (G1M.tapeLength n) → Bool) (hteq : tape = tape')
    (mode : G1Mode) (position : G1FramePosition) (b0 b1 b2 : Bool)
    (ctx : G1Ctx) :
    g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx =
      g1AlignedConfig n h' hh' tape' mode position b0 b1 b2 ctx := by
  subst heq; subst hteq; rfl

/-! ## The loop clock `8k² + 29k` -/

/-- **The cumulative cost of the first `k` cursor-walk rounds.**  Round `j`
costs `16j + 37` steps, so `k` rounds cost `∑_{j<k} (16j + 37) = 8k² + 29k`. -/
def g1BLoopSteps (k : Nat) : Nat := 8 * k ^ 2 + 29 * k

@[simp] theorem g1BLoopSteps_zero : g1BLoopSteps 0 = 0 := by
  simp [g1BLoopSteps]

private theorem g1BSq_succ (k : Nat) : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by
  rw [Nat.pow_two, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
  omega

/-- **The recurrence.**  One more round of the walk costs exactly the
`16k + 37` of `g1CS_walk_iteration_exact`. -/
theorem g1BLoopSteps_succ (k : Nat) :
    g1BLoopSteps (k + 1) = g1BLoopSteps k + (16 * k + 37) := by
  simp only [g1BLoopSteps, g1BSq_succ]
  omega

/-- **The closed form really is the sum** of the individual round costs. -/
theorem g1BLoopSteps_eq_sum (k : Nat) :
    g1BLoopSteps k = ((List.range k).map (fun j => 16 * j + 37)).sum := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ← ih,
        g1BLoopSteps_succ]
      simp

/-! ## The induction: `Σ(0) → Σ(k)` from the real initial configuration -/

/-- **The cursor-walk driver.**  For a canonical `and`/`or` request with a
positive operand-2 index, for **every** `k ≤ arg2` with `k < vals.length` and
`hv : r.vals[k]? = some v`, exactly `g1WalkInstallSteps r + g1BLoopSteps k`
genuine steps run `G1M.initialConfig` to `Σ(r, k, v)` — formed with **that same
`hv`**, so the endpoint carries the hidden-bit relation explicitly and no round
weakens it.  Base case `g1CS_walk_install_exact`; successor one exact
`16k + 37` round, whose start needs the *prior* proof
`r.vals[k]? = some r.vals[k]`, generated from `k < vals.length`.  Both numeric
side conditions of `Σ` travel with the induction. -/
theorem g1CS_walk_loop_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k0 : Nat) (h2 : r.arg2 = k0 + 1) :
    ∀ (k : Nat) (hk2 : k ≤ r.arg2) (hk : k < r.vals.length) (v : Bool)
      (hv : r.vals[k]? = some v),
      TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1WalkInstallSteps r + g1BLoopSteps k) =
        g1WalkConfig r k hk2 hk v hv := by
  intro k
  induction k with
  | zero =>
      intro hk2 hk v hv
      rw [show g1WalkInstallSteps r + g1BLoopSteps 0 = g1WalkInstallSteps r from
        by simp]
      exact g1CS_walk_install_exact r hc ht k0 h2 v hv
  | succ k ih =>
      intro hk2 hk v hv
      have hkk : k < r.vals.length := by omega
      have hvk : r.vals[k]? = some r.vals[k] := List.getElem?_eq_getElem hkk
      rw [show g1WalkInstallSteps r + g1BLoopSteps (k + 1) =
            (g1WalkInstallSteps r + g1BLoopSteps k) + (16 * k + 37) from by
          rw [g1BLoopSteps_succ]; omega,
        runConfig_add, ih (by omega) hkk r.vals[k] hvk]
      exact g1CS_walk_iteration_exact r k (by omega) hk r.vals[k] v hvk hv

/-! ## The repair-pending layout family both endpoints land on

The canonical word with operand 2 split as `index^(arg2-s) · spent^s`, data
region **exactly `vals`**, **no cursor**.  For `s > 0` it is *not* the canonical
word: the repair is deferred.  Its semantic domain is `s ≤ arg2`; outside that
domain the unrestricted definition is only a syntactic Nat-subtraction identity. -/

/-- The walk's **repair-pending** layout after `s` consumed operand-2 units. -/
def g1BSpentFrames (r : G1Request) (s : Nat) : List G1Frame :=
  g1FieldRouteFrames r ++ List.replicate (r.arg2 - s) G1Frame.index ++
    List.replicate s G1Frame.spent ++ [G1Frame.separator] ++
    r.vals.map G1Frame.data ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

/-- **The one-round out-of-range tape is this family.** -/
theorem g1BSpentFrames_eq_restored (r : G1Request) (j : Nat) :
    g1WalkFramesRestored r j = g1BSpentFrames r (j + 1) := by
  rw [g1WalkFramesRestored, g1BSpentFrames, Nat.sub_sub]

/-- **At `s = 0` the family is the initial word**: with `vals = []`,
`g1BSpentFrames r 0` is literally `encodeG1Frames r ++ [.blank]`. -/
theorem g1BSpentFrames_empty (r : G1Request) (hv : r.vals = []) :
    g1BSpentFrames r 0 = encodeG1Frames r ++ [G1Frame.blank] := by
  simp only [g1BSpentFrames, encodeG1Frames, g1FieldRouteFrames, hv,
    Nat.sub_zero, List.replicate_zero, List.map_nil]
  simp [List.append_assoc]

theorem g1BSpentFrames_length (r : G1Request) (s : Nat) (hs : s ≤ r.arg2) :
    (g1BSpentFrames r s).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 := by
  simp only [g1BSpentFrames, List.length_append, g1FieldRouteFrames_length,
    List.length_replicate, List.length_map, List.length_cons, List.length_nil]
  omega

/-- **The endpoint word's length**: no frame is invented and none is lost. -/
theorem g1BSpentFrames_length_eq_validation (r : G1Request) (s : Nat)
    (hs : s ≤ r.arg2) :
    (g1BSpentFrames r s).length =
      (encodeG1Frames r ++ [G1Frame.blank]).length := by
  rw [g1BSpentFrames_length r s hs]
  simp only [List.length_append, encodeG1Frames_length, List.length_cons,
    List.length_nil]

private theorem g1BCount_replicate_ne (f g : G1Frame) (m : Nat) (h : f ≠ g) :
    (List.replicate m g).count f = 0 :=
  List.count_eq_zero.2 (fun hmem => h (List.eq_of_mem_replicate hmem))

private theorem g1BCount_data_run (f : G1Frame) (l : List Bool)
    (hf : ∀ v : Bool, f ≠ G1Frame.data v) : (l.map G1Frame.data).count f = 0 :=
  List.count_eq_zero.2 (fun hmem => by
    obtain ⟨v, -, hv⟩ := List.mem_map.1 hmem
    exact hf v hv.symm)

private theorem g1BFieldRoute_count_spent (r : G1Request) :
    (g1FieldRouteFrames r).count G1Frame.spent = 0 := by
  simp [g1FieldRouteFrames, List.count_append,
    g1BCount_replicate_ne G1Frame.spent G1Frame.tag r.tag.units (by decide),
    g1BCount_replicate_ne G1Frame.spent G1Frame.index r.arg1 (by decide)]

private theorem g1BFieldRoute_count_cursor (r : G1Request) :
    (g1FieldRouteFrames r).count G1Frame.cursor = 0 := by
  simp [g1FieldRouteFrames, List.count_append,
    g1BCount_replicate_ne G1Frame.cursor G1Frame.tag r.tag.units (by decide),
    g1BCount_replicate_ne G1Frame.cursor G1Frame.index r.arg1 (by decide)]

private theorem g1BFieldRoute_count_index (r : G1Request) :
    (g1FieldRouteFrames r).count G1Frame.index = r.arg1 := by
  simp [g1FieldRouteFrames, List.count_append,
    g1BCount_replicate_ne G1Frame.index G1Frame.tag r.tag.units (by decide)]

/-- **No cursor survives on the walk's terminal tapes.** -/
theorem g1BSpentFrames_count_cursor (r : G1Request) (s : Nat) :
    (g1BSpentFrames r s).count G1Frame.cursor = 0 := by
  simp [g1BSpentFrames, List.count_append, g1BFieldRoute_count_cursor,
    g1BCount_replicate_ne G1Frame.cursor G1Frame.index (r.arg2 - s) (by decide),
    g1BCount_replicate_ne G1Frame.cursor G1Frame.spent s (by decide),
    g1BCount_data_run G1Frame.cursor r.vals (by decide)]

/-- **Exactly `s` operand-2 units are consumed.** -/
theorem g1BSpentFrames_count_spent (r : G1Request) (s : Nat) :
    (g1BSpentFrames r s).count G1Frame.spent = s := by
  simp [g1BSpentFrames, List.count_append, g1BFieldRoute_count_spent,
    g1BCount_replicate_ne G1Frame.spent G1Frame.index (r.arg2 - s) (by decide),
    g1BCount_data_run G1Frame.spent r.vals (by decide)]

/-- **The operand-2 field is not repaired**: `arg2 - s` units remain. -/
theorem g1BSpentFrames_count_index (r : G1Request) (s : Nat) :
    (g1BSpentFrames r s).count G1Frame.index = r.arg1 + (r.arg2 - s) := by
  simp [g1BSpentFrames, List.count_append, g1BFieldRoute_count_index,
    g1BCount_replicate_ne G1Frame.index G1Frame.spent s (by decide),
    g1BCount_data_run G1Frame.index r.vals (by decide)]

/-! ## The successful terminal at `j = arg2`

The operand-2 field is `index⁰ · spent^arg2`, so the reverse seek finds no
`index` and stops on the `argSep` that **opens** the field.  Four merged macros
close the walk: `g1CS_walk_seek_exhaust` (`8a + 8`), `g1CS_walk_exh_to_cursor`
(`8a + 12`), `g1CS_walk_turn_fin` (`4`), `g1CS_walk_fin_restore` (`4`). -/

/-- Everything left of the `argSep` that opens the operand-2 field: the prefix
the exhaustion seek stops in front of and never reads past. -/
def g1ExhPre (r : G1Request) : List G1Frame :=
  G1Frame.bof :: (List.replicate r.tag.units G1Frame.tag ++
    G1Frame.argSep :: List.replicate r.arg1 G1Frame.index)

@[simp] theorem g1ExhPre_length (r : G1Request) :
    (g1ExhPre r).length = r.tag.units + r.arg1 + 2 := by
  simp only [g1ExhPre, List.length_cons, List.length_append,
    List.length_replicate]
  omega

/-- **The opening `argSep` is the last frame of the field route.** -/
theorem g1ExhPre_argSep (r : G1Request) :
    g1ExhPre r ++ [G1Frame.argSep] = g1FieldRouteFrames r := by
  simp [g1ExhPre, g1FieldRouteFrames, List.append_assoc]

private theorem g1BSkipRun_length (r : G1Request) (j : Nat)
    (hj : j ≤ r.vals.length) :
    (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
      (r.vals.take j).map G1Frame.data).length = 2 * j + 1 := by
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.length_map, List.length_take]
  omega

private theorem g1BFinPre_length (r : G1Request) (hm : r.arg2 ≤ r.vals.length) :
    (g1ExhPre r ++ G1Frame.argSep :: (List.replicate r.arg2 G1Frame.spent ++
      [G1Frame.separator] ++ (r.vals.take r.arg2).map G1Frame.data)).length =
      g1WalkCursor r r.arg2 := by
  simp only [List.length_append, List.length_cons, g1ExhPre_length,
    List.length_replicate, List.length_nil, List.length_map, List.length_take,
    g1WalkCursor]
  omega

private theorem g1BWalkSplit_exh (r : G1Request) :
    (g1ExhPre r ++ G1Frame.argSep :: (List.replicate r.arg2 G1Frame.spent ++
        [G1Frame.separator] ++ (r.vals.take r.arg2).map G1Frame.data)) ++
        (G1Frame.cursor :: ((r.vals.drop (r.arg2 + 1)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank])) =
      g1WalkFrames r r.arg2 := by
  rw [g1WalkFrames, Nat.sub_self, ← g1ExhPre_argSep r]
  simp [List.append_assoc]

/-- **The terminal restore writes back exactly the hidden bit.**  Where the
invariant's relation at `j = arg2` is consumed: the `data v` frame the restore
writes re-creates `vals` precisely because `v` is `vals[arg2]`. -/
private theorem g1BWalkSplit_done (r : G1Request) (v : Bool)
    (hm : r.arg2 < r.vals.length) (hv : r.vals[r.arg2] = v) :
    (g1ExhPre r ++ G1Frame.argSep :: (List.replicate r.arg2 G1Frame.spent ++
        [G1Frame.separator] ++ (r.vals.take r.arg2).map G1Frame.data)) ++
        (G1Frame.data v :: ((r.vals.drop (r.arg2 + 1)).map G1Frame.data ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank])) =
      g1BSpentFrames r r.arg2 := by
  have hd : r.vals.map G1Frame.data =
      (r.vals.take r.arg2).map G1Frame.data ++
        G1Frame.data v :: (r.vals.drop (r.arg2 + 1)).map G1Frame.data := by
    conv_lhs => rw [← List.take_append_drop r.arg2 r.vals]
    rw [List.map_append, g1BDrop_cons r.vals r.arg2 hm, hv]
    simp
  rw [g1BSpentFrames, Nat.sub_self, hd, ← g1ExhPre_argSep r]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **The successful terminal of the cursor walk.**  For `arg2 < vals.length`
and `hv : r.vals[arg2]? = some v`, the machine runs from `Σ(r, arg2, v)` into
the pass-A reset handoff in exactly `16 * arg2 + 28` genuine steps: `(8a + 8)`
seek-exhaust, `(8a + 12)` exhaustion scan, `4` turn, `4` restore.  The endpoint
is exact: control `readAResetStart`, head `4 * (g1WalkCursor r arg2 + 1)`,
context still carrying the latched `vB = vals[arg2]`, and tape
`g1BSpentFrames r arg2`, whose **data region is fully restored to `vals` and
carries no `cursor`** while the operand-2 field is `spent^arg2` — a
repair-pending tape, not the canonical word, and no repair is claimed. -/
theorem g1CS_walk_terminal_exact (r : G1Request) (hm : r.arg2 < r.vals.length)
    (v : Bool) (hv : r.vals[r.arg2]? = some v) :
    TM.runConfig (M := G1M)
        (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv) (16 * r.arg2 + 28) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
        (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
        (g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB v) := by
  have hTL := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
  have hTLe : 4 * (r.tag.units + r.arg1 + r.arg2 + r.arg2 + 4 + 2) <
      G1M.tapeLength (encodeG1 r).length := by
    simpa only [g1WalkCursor] using hTL
  have hdv : r.vals[r.arg2] = v := g1BGetn hv hm
  have hLskip := g1BSkipRun_length r r.arg2 (by omega)
  have hLfin := g1BFinPre_length r (by omega)
  -- Phase A: the reverse seek exhausts on the opening `argSep`.
  have hA : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r r.arg2 - 1)
        (by omega) (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        .bSeek .p3 false false false (g1Ctx0.withVB v)) (8 * r.arg2 + 8) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 2))
        (by omega)
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        .bExh .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_seek_exhaust (encodeG1 r).length (g1ExhPre r)
      (List.replicate r.arg2 G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take r.arg2).map G1Frame.data)
      (G1Frame.cursor :: ((r.vals.drop (r.arg2 + 1)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank]))
      (g1Ctx0.withVB v) (g1WalkSkipRun_mem r.arg2 r.vals)
      (by rw [g1ExhPre_length, hLskip]; omega)
    rw [g1BWalkSplit_exh r] at h
    simp only [g1ExhPre_length, hLskip,
      show 4 * (r.tag.units + r.arg1 + 2 + (2 * r.arg2 + 1)) + 3 =
        4 * g1WalkCursor r r.arg2 - 1 from by simp only [g1WalkCursor]; omega,
      show 4 * (2 * r.arg2 + 1) + 4 = 8 * r.arg2 + 8 from by omega] at h
    exact h
  -- Phase B: the exhaustion scan runs right to the cursor.
  have hB : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 2))
        (by omega)
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        .bExh .p0 false false false (g1Ctx0.withVB v)) (8 * r.arg2 + 12) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
        (by omega)
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        .bTurnFin .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_exh_to_cursor (encodeG1 r).length (g1ExhPre r)
      (List.replicate r.arg2 G1Frame.spent ++ [G1Frame.separator] ++
        (r.vals.take r.arg2).map G1Frame.data)
      ((r.vals.drop (r.arg2 + 1)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      (g1Ctx0.withVB v) (g1WalkSkipRun_mem r.arg2 r.vals)
      (by rw [g1ExhPre_length, hLskip]; omega)
    rw [g1BWalkSplit_exh r] at h
    simp only [g1ExhPre_length, hLskip,
      show r.tag.units + r.arg1 + 2 + (2 * r.arg2 + 1 + 2) =
        g1WalkCursor r r.arg2 + 1 from by simp only [g1WalkCursor]; omega,
      show 4 * (2 * r.arg2 + 1 + 2) = 8 * r.arg2 + 12 from by omega] at h
    exact h
  -- Phase C: the terminal turn back onto the cursor frame.
  have hC : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
        (by omega)
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        .bTurnFin .p0 false false false (g1Ctx0.withVB v)) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r r.arg2) (by omega)
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        (g1FinMode v) .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_turn_fin (encodeG1 r).length
      (4 * g1WalkCursor r r.arg2) (by omega)
      (g1ListTape (n := (encodeG1 r).length)
        ((g1WalkFrames r r.arg2).flatMap G1Frame.bits)) (g1Ctx0.withVB v)
    simpa only [show 4 * g1WalkCursor r r.arg2 + 4 =
      4 * (g1WalkCursor r r.arg2 + 1) from by omega, G1Ctx.withVB_vB] using h
  -- Phase D: the terminal restore, `cursor ↦ data vals[arg2]`.
  have hD : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1WalkCursor r r.arg2) (by omega)
        (g1ListTape ((g1WalkFrames r r.arg2).flatMap G1Frame.bits))
        (g1FinMode v) .p0 false false false (g1Ctx0.withVB v)) 4 =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
        (by omega)
        (g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB v) := by
    have h := g1CS_walk_fin_restore (encodeG1 r).length
      (g1ExhPre r ++ G1Frame.argSep :: (List.replicate r.arg2 G1Frame.spent ++
        [G1Frame.separator] ++ (r.vals.take r.arg2).map G1Frame.data))
      ((r.vals.drop (r.arg2 + 1)).map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank])
      v (g1Ctx0.withVB v) (by rw [hLfin]; omega)
    rw [g1BWalkSplit_exh r, g1BWalkSplit_done r v hm hdv] at h
    simp only [hLfin, show 4 * g1WalkCursor r r.arg2 + 4 =
      4 * (g1WalkCursor r r.arg2 + 1) from by omega] at h
    exact h
  simp only [g1WalkConfig]
  rw [show 16 * r.arg2 + 28 =
        (8 * r.arg2 + 8) + ((8 * r.arg2 + 12) + (4 + 4)) from by omega,
    runConfig_add, hA, runConfig_add, hB, runConfig_add, hC, hD]

/-! ## The two totals, and the unchanged clock

Both are proved to fit the untouched `g1Clock` *before* any public capstone is
stated, and every summand is a concrete polynomial in the request's fields. -/

private theorem g1BClock_quad (N : Nat) :
    g1Clock (4 * N) = 8192 * N ^ 2 + (4096 * N + 1024) := by
  rw [g1Clock, g1BSq_succ, Nat.mul_pow, show (4 : Nat) ^ 2 = 16 from rfl]
  omega

/-- **The quadratic clock margin.**  Any total of the form
`g1InstallScanSteps r + c` with `c ≤ 8A² + 45A + 37` for an `A` inside the
canonical word's frame count fits the **unchanged** public clock. -/
private theorem g1BQuad_le_clock (r : G1Request) (A c : Nat)
    (hA : A ≤ r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6)
    (hc : c ≤ 8 * A ^ 2 + 45 * A + 37) :
    g1InstallScanSteps r + c ≤ g1Clock (encodeG1 r).length := by
  have hlen : (encodeG1 r).length =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :=
    encodeG1_length r
  have hsq : 8 * A ^ 2 ≤
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hA 2)
  have hIS : g1InstallScanSteps r ≤
      12 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) + 9 := by
    simp only [g1InstallScanSteps, g1ReadBHandoffSteps, hlen]
    omega
  rw [hlen, g1BClock_quad]
  omega

/-- Steps from `initialConfig` to the pass-A reset handoff of a **positive**
operand-2 index: installation, the `arg2` rounds, the terminal. -/
def g1BReadSteps (r : G1Request) : Nat :=
  g1InstallScanSteps r + (8 * r.arg2 ^ 2 + 45 * r.arg2 + 37)

/-- **The three-part decomposition of the read.** -/
theorem g1BReadSteps_eq (r : G1Request) :
    g1BReadSteps r =
      g1WalkInstallSteps r + g1BLoopSteps r.arg2 + (16 * r.arg2 + 28) := by
  simp only [g1BReadSteps, g1WalkInstallSteps, g1BLoopSteps]
  omega

/-- The same count relative to the installation step total. -/
theorem g1BReadSteps_eq_install (r : G1Request) :
    g1BReadSteps r =
      g1WalkInstallSteps r + (8 * r.arg2 ^ 2 + 45 * r.arg2 + 28) := by
  simp only [g1BReadSteps, g1WalkInstallSteps]
  omega

/-- **The positive-index read fits the unchanged public clock.** -/
theorem g1BReadSteps_le_clock (r : G1Request) :
    g1BReadSteps r ≤ g1Clock (encodeG1 r).length :=
  g1BQuad_le_clock r r.arg2 _ (by omega) (by omega)

/-- Steps to the aggregated out-of-range boundary of a positive index. -/
def g1BOOBSteps (r : G1Request) : Nat :=
  g1InstallScanSteps r + (g1BLoopSteps r.vals.length + 4)

theorem g1BOOBSteps_eq (r : G1Request) :
    g1BOOBSteps r =
      g1InstallScanSteps r +
        (8 * r.vals.length ^ 2 + 29 * r.vals.length + 4) := by
  simp only [g1BOOBSteps, g1BLoopSteps]

/-- **The out-of-range branch fits the unchanged public clock.** -/
theorem g1BOOBSteps_le_clock (r : G1Request) :
    g1BOOBSteps r ≤ g1Clock (encodeG1 r).length := by
  rw [g1BOOBSteps_eq]
  exact g1BQuad_le_clock r r.vals.length _ (by omega) (by omega)

/-! ## The public arbitrary positive-index operand-2 read -/

/-- **The G1 machine reads an arbitrary positive operand-2 index.**  For a
canonical `and`/`or` request with `0 < arg2` and `r.vals[arg2]? = some b`,
exactly `g1BReadSteps r = g1InstallScanSteps r + 8 * arg2² + 45 * arg2 + 37 =
g1WalkInstallSteps r + 8 * arg2² + 45 * arg2 + 28` genuine `TM.runConfig` steps
take `G1M.initialConfig` to `readAResetStart` with `G1Ctx.vB = b`.  Head,
control, context and tape are all pinned; the tape is `g1BSpentFrames r arg2` —
data region **restored exactly to `vals`**, **no cursor anywhere**, operand-2
field consumed to `spent^arg2`.  The bit `b` is the **actual** `r.vals[r.arg2]`,
resolved physically out of the unannotated data region: no value, target, cursor
or index annotation is supplied to the machine.  This is *only* the read — the
field is left unrepaired, and pass A, combine, the output write and
`TM.accepts` are untouched. -/
theorem g1CS_readB_positive_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BReadSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
        (by
          have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _)
            (g1BLength_pos_of_get hb)
          omega)
        (g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB b) := by
  have hm : r.arg2 < r.vals.length := g1BLength_pos_of_get hb
  rw [g1BReadSteps_eq, runConfig_add,
    g1CS_walk_loop_exact r hc ht (r.arg2 - 1) (by omega) r.arg2
      (Nat.le_refl _) hm b hb]
  exact g1CS_walk_terminal_exact r hm b hb

theorem g1CS_readB_positive_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BReadSteps r)).head : Nat) = 4 * (g1WalkCursor r r.arg2 + 1) := by
  rw [g1CS_readB_positive_exact r hc ht h2 b hb]; rfl

theorem g1CS_readB_positive_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BReadSteps r)).state.snd = g1ReadAResetState (g1Ctx0.withVB b) := by
  rw [g1CS_readB_positive_exact r hc ht h2 b hb]; rfl

/-- **The latched bit is `r.vals[r.arg2]`.** -/
theorem g1CS_readB_positive_vB (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BReadSteps r)).state.snd.ctx.vB = b := by
  rw [g1CS_readB_positive_exact r hc ht h2 b hb]; rfl

/-- The final tape is the **repair-pending** word: data region exactly `vals`,
no cursor, operand-2 field `spent^arg2`. -/
theorem g1CS_readB_positive_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BReadSteps r)).tape =
      g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits) := by
  rw [g1CS_readB_positive_exact r hc ht h2 b hb]; rfl

/-! ## The aggregated out-of-range branch -/

/-- The context the out-of-range boundary carries: the **last** data bit the
walk latched, or `g1Ctx0` on an empty data region, which never reaches a
latch. -/
def g1BOOBCtx (r : G1Request) : G1Ctx :=
  match r.vals.getLast? with
  | none => g1Ctx0
  | some b => g1Ctx0.withVB b

theorem g1BOOBCtx_nil (r : G1Request) (hv : r.vals = []) :
    g1BOOBCtx r = g1Ctx0 := by
  simp [g1BOOBCtx, hv]

theorem g1BOOBCtx_last (r : G1Request) (t : Nat) (v : Bool)
    (ht : t + 1 = r.vals.length) (hv : r.vals[t]? = some v) :
    g1BOOBCtx r = g1Ctx0.withVB v := by
  have h : r.vals.getLast? = some v := by
    rw [List.getLast?_eq_getElem?, show r.vals.length - 1 = t from by omega]
    exact hv
  simp [g1BOOBCtx, h]

private theorem g1BInit_tape_spent (r : G1Request) (hv : r.vals = []) :
    g1ListTape (n := (encodeG1 r).length)
        ((g1BSpentFrames r 0).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1BSpentFrames_empty r hv]
  exact g1ListTape_validation_eq_initial r

/-- **The empty-data out-of-range capstone, aggregated.**  With `vals = []` the
branch is the read-only installation scan plus the probe meeting the
`output false` destination: `g1InstallScanSteps r + 4` steps end in the stable
`bOOB` boundary, context `g1Ctx0`, tape **bit-for-bit the initial word**. -/
theorem g1CS_readB_positive_oob_nil (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (hv : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) := by
  have hlen : r.vals.length = 0 := by rw [hv]; rfl
  have hsteps : g1BOOBSteps r = g1WalkEmptyOOBSteps r := by
    simp only [g1BOOBSteps, g1WalkEmptyOOBSteps, hlen, g1BLoopSteps_zero]
  rw [hsteps, g1CS_walk_install_oob_exact r hc ht (r.arg2 - 1) (by omega) hv,
    g1BOOBCtx_nil r hv]
  refine g1BAligned_congr _ _ _ _ _ (by simp only [g1WalkCursor]; omega) _ _ ?_
    _ _ _ _ _ _
  rw [hlen]
  exact (g1BInit_tape_spent r hv).symm

/-- **The non-empty aggregated out-of-range capstone.**  For `0 < m ≤ arg2` the
walk installs, runs `m - 1` full rounds and aborts in the `m`-th round's probe,
reaching the stable `bOOB` boundary on `g1BSpentFrames r m` at head
`4 * (u + a1 + arg2 + m + 5)`, with the last latched bit `vals[m-1]` still in
`G1Ctx.vB`. -/
theorem g1CS_readB_positive_oob_cons (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (t : Nat)
    (hlen : t + 1 = r.vals.length) (hm : r.vals.length ≤ r.arg2) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) := by
  have htm : t < r.vals.length := by omega
  have ht2 : t < r.arg2 := by omega
  have hvt : r.vals[t]? = some r.vals[t] := List.getElem?_eq_getElem htm
  have hsteps : g1BOOBSteps r =
      (g1WalkInstallSteps r + g1BLoopSteps t) + (16 * t + 32) := by
    simp only [g1BOOBSteps, g1WalkInstallSteps, ← hlen, g1BLoopSteps,
      g1BSq_succ]
    omega
  rw [hsteps, runConfig_add,
    g1CS_walk_loop_exact r hc ht (r.arg2 - 1) (by omega) t (by omega) htm
      r.vals[t] hvt,
    g1CS_walk_oob_exact r t ht2 hlen r.vals[t] hvt,
    g1BOOBCtx_last r t r.vals[t] hlen hvt]
  refine g1BAligned_congr _ _ _ _ _ (by simp only [g1WalkCursor]; omega) _ _ ?_
    _ _ _ _ _ _
  rw [g1BSpentFrames_eq_restored r t, hlen]

/-- **The aggregated out-of-range branch of a positive operand-2 index.**  For
`0 < arg2` and `vals.length ≤ arg2` — the index points past the data region —
exactly `g1BOOBSteps r = g1InstallScanSteps r + 8m² + 29m + 4` genuine steps
take `G1M.initialConfig` to the stable out-of-range boundary, `m = vals.length`
covering **both** branches uniformly.  The endpoint is pinned exactly: control
`bOOB .p0`, head `4 * (u + a1 + arg2 + m + 5)`, context `g1BOOBCtx r`, and tape
`g1BSpentFrames r m` — data region **exactly `vals`**, **no cursor**, operand-2
field `index^(arg2-m) · spent^m`.  That tape is *not* repaired, and `bOOB` is a
boundary, not a verdict: no output write, rejection or `TM.accepts` claim is
made here. -/
theorem g1CS_readB_positive_oob_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) := by
  rcases Nat.eq_zero_or_pos r.vals.length with hlen | hpos
  · exact g1CS_readB_positive_oob_nil r hc ht h2
      (List.eq_nil_of_length_eq_zero hlen)
  · obtain ⟨t, hlen⟩ : ∃ t, r.vals.length = t + 1 := ⟨r.vals.length - 1, by omega⟩
    exact g1CS_readB_positive_oob_cons r hc ht t hlen.symm hm

/-- **The aggregated out-of-range boundary is stable.**  Every further step
keeps the configuration, so no later theorem can rewrite the unrepaired
operand-2 field by accident. -/
theorem g1CS_readB_positive_oob_stable (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) (k : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r + k) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) := by
  rw [runConfig_add, g1CS_readB_positive_oob_exact r hc ht h2 hm]
  exact g1CS_runConfig_oob_sink _ _ _ _ _ k

theorem g1CS_readB_positive_oob_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r)).head : Nat) =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5) := by
  rw [g1CS_readB_positive_oob_exact r hc ht h2 hm]; rfl

theorem g1CS_readB_positive_oob_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r)).state.snd = g1OOBState (g1BOOBCtx r) := by
  rw [g1CS_readB_positive_oob_exact r hc ht h2 hm]; rfl

theorem g1CS_readB_positive_oob_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r)).tape =
      g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits) := by
  rw [g1CS_readB_positive_oob_exact r hc ht h2 hm]; rfl

/-- **Success and out-of-range are different boundaries.**  The read ends in
`readAResetStart`, the out-of-range branch in the stable `bOOB`; `arg2 < m` and
`m ≤ arg2` are exhaustive, so exactly one of the two capstones applies. -/
theorem g1CS_readB_positive_oob_ne_success (ctx ctx' : G1Ctx) :
    g1OOBState ctx ≠ g1ReadAResetState ctx' := by
  intro h
  have hmode : G1Mode.bOOB = G1Mode.readAResetStart := congrArg G1State.mode h
  exact absurd hmode (by decide)

end Pnp3.Internal.PsubsetPpoly.TM
