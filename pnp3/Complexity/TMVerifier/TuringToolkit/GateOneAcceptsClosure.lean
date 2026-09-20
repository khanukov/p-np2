import Complexity.TMVerifier.TuringToolkit.GateOneOutputAccept

/-!
# S11 one-gate acceptance closure (2026-09-19)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**
No source obligation is reduced: nothing here touches
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.

`GateOneOutputAccept` supplies one direction of the G1 verdict — a canonical
request with a defined result accepts (`g1CS_accepts_of_spec_some`) — plus two
targeted operand-2 nonacceptance theorems.  This module closes the remaining
direction and assembles the **all-request** endpoint:

```lean
g1CS_accepts_eq_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      r.spec.isSome
```

## The transducer acceptance convention

G1 is a **transducer**, not a decision machine, and this module keeps main's
convention unchanged.  Acceptance means *the computation was defined*: both
`some true` and `some false` reach the single literal `g1AcceptState`, because
`GateOneControl` sends `.outputDoneFalse` and `.outputDoneTrue` to the same
successor.  The *value* lives on the output cell, exposed by
`g1CS_gate_accept_output`.  This mirrors the sibling T1 machine, whose endpoint
is `t1CS_accepts_eq_isSome` with the read value on the output cell.  A
`spec = some false` request therefore **accepts**; it is not a rejection, and
`g1CS_accepts_eq_isSome` is deliberately *not* a theorem about `some true`.

No transition row, no `g1Clock`, no `*Steps` definition, no head position and no
`GateN` declaration is touched or restated here.

## The three request classes

The `r.spec = none` half splits exhaustively, driven by main's own pure
predicates `G1Request.WellFormed`/`G1Request.operandsInBounds` and the bridge
`G1Request.spec_isSome_iff`:

* a **noncanonical** request is driven into the literal `g1RejectState` by the
  fixed `(encodeG1 r).length + 4`-step validation prefix
  (`g1CS_validate_noncanonical_reject_exact`), padded to the public clock by
  `g1_validate_le_clock` and `g1CS_runConfig_reject_state`;
* a canonical **`const`** request always has a value, so the class is empty;
* a canonical request with an **out-of-range operand** settles in a `bOOB`
  boundary: operand 2 through the pass-B boundaries
  (`g1CS_readB_zero_oob_stable`, `g1CS_readB_positive_oob_stable`), operand 1
  through the pass-A walk stopping at the first absent successor
  (`g1CS_aWalk_oob_driver_stable`), or — with empty data — at S4's install
  boundary (`g1CS_readA_sigma0_unary_oob_exact`).

`bOOB` is a **boundary, not a rejection**: its transition row is idle
(`g1Transition_bOOB_stable`), so such a run reaches neither literal sink.
`g1OOBState_ne_reject` records that separation.  Nothing here calls `bOOB` a
rejection.

## What is still not claimed

Acceptance is **exact-step, not halting**: the statements read the
configuration after exactly `g1Clock (encodeG1 r).length` steps.  Every
statement connecting the machine to `G1Request.spec` quantifies over the
standard encoded points `g1Point (encodeG1 r)`; nothing is claimed for a
physical word outside the image of `encodeG1`, so **this is not a
language-membership theorem**.  It is one gate: no multi-gate, `GateN`,
`GapMCSPVerifier` or content-verifier statement is made, and no resource claim
beyond the unchanged `g1Clock` is added.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## The validation prefix fits the public clock

`GateOneValidation` proves the noncanonical rejection after exactly
`(encodeG1 r).length + 4` steps but states no clock bound for it; every other
route this module pads already has one. -/

/-- **The validation prefix is inside the clock.**  Stated on the raw length, so
it applies to the `(encodeG1 r).length + 4` of
`g1CS_validate_noncanonical_reject_exact`. -/
theorem g1_validate_le_clock (n : Nat) : n + 4 ≤ g1Clock n := by
  have hsq : n + 1 ≤ (n + 1) ^ 2 := by
    have h2 : (n + 1) ^ 2 = (n + 1) * (n + 1) := by
      simp [Nat.pow_succ]
    rw [h2]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
  have hmul : 512 * (n + 1) ≤ 512 * (n + 1) ^ 2 := Nat.mul_le_mul_left _ hsq
  rw [g1Clock]
  omega

/-- **Padding a stable endpoint out to the full clock.**  If the run from the
real initial configuration sits in `c` from step `steps` on, for *every* further
budget, and `steps` fits the clock, then `c` is the configuration the machine is
in when its own `runTime` expires.  This is the only arithmetic step between an
exact route and a `TM.run` statement. -/
theorem g1CS_pad_to_clock {r : G1Request} {steps : Nat}
    {c : Configuration (M := G1M) (encodeG1 r).length}
    (hle : steps ≤ g1Clock (encodeG1 r).length)
    (h : ∀ k, TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (steps + k) = c) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length) = c := by
  have hk := h (g1Clock (encodeG1 r).length - steps)
  rwa [Nat.add_sub_cancel' hle] at hk

/-! ## The literal sinks, and what is distinct from the accepting one -/

/-- A control state whose mode is not `accept` is not the accepting sink. -/
theorem g1State_ne_accept_of_mode {q : G1State} (h : q.mode ≠ .accept) :
    q ≠ g1AcceptState := by
  intro hq
  exact h (congrArg G1State.mode hq)

/-- **The two literal sinks are distinct.** -/
theorem g1RejectState_ne_accept : g1RejectState ≠ g1AcceptState :=
  g1State_ne_accept_of_mode (by decide)

/-- **The out-of-range boundary is not the accepting sink**, in any context. -/
theorem g1OOBState_ne_accept (ctx : G1Ctx) : g1OOBState ctx ≠ g1AcceptState :=
  g1State_ne_accept_of_mode (show G1Mode.bOOB ≠ G1Mode.accept by decide)

/-- **The out-of-range boundary is not the reject sink either.**  `bOOB` is a
boundary and not a verdict: a canonical request with no value neither accepts
nor rejects, it idles. -/
theorem g1OOBState_ne_reject (ctx : G1Ctx) : g1OOBState ctx ≠ g1RejectState := by
  intro h
  exact absurd (congrArg G1State.mode h)
    (show G1Mode.bOOB ≠ G1Mode.reject by decide)

/-! ## Reject absorption from an arbitrary configuration

`g1CS_runConfig_reject_sink` needs the configuration in aligned shape; the
validation pass exposes only the control state, so this pair reads that. -/

/-- **One step out of the reject sink, from an arbitrary configuration.** -/
theorem g1CS_stepConfig_reject_state {n : Nat} (c : Configuration (M := G1M) n)
    (h : c.state.snd = g1RejectState) :
    (TM.stepConfig (M := G1M) c).state.snd = g1RejectState := by
  have hstep : (TM.stepConfig (M := G1M) c).state.snd =
      (g1Transition c.state.fst c.state.snd (c.tape c.head)).2.1 := rfl
  rw [hstep, h, g1Transition_reject_sink]

/-- **The reject sink is absorbing for every further budget**, from an arbitrary
configuration carrying it. -/
theorem g1CS_runConfig_reject_state {n : Nat} (c : Configuration (M := G1M) n)
    (h : c.state.snd = g1RejectState) (k : Nat) :
    (TM.runConfig (M := G1M) c k).state.snd = g1RejectState := by
  induction k with
  | zero => exact h
  | succ k ih =>
      rw [runConfig_add, runConfig_one]
      exact g1CS_stepConfig_reject_state _ ih

/-! ## From `TM.runConfig` at the clock to `TM.accepts` -/

/-- **The machine's own run is the run for `g1Clock` steps.**  Definitional:
`G1M.runTime = g1CS.timeBound = g1Clock`. -/
theorem g1CS_run_eq_runConfig {n : Nat} (x : Boolcube.Point n) :
    TM.run (M := G1M) (n := n) x =
      TM.runConfig (M := G1M) (G1M.initialConfig x) (g1Clock n) := rfl

/-- **Accepting is a local-state equation.**  `G1M` has a single phase, so the
dependent `Sigma` equality against `G1M.accept` carries no information beyond
its `G1State` component. -/
theorem g1CS_state_eq_accept_iff {n : Nat} (c : Configuration (M := G1M) n) :
    c.state = G1M.accept ↔ c.state.snd = g1AcceptState := by
  constructor
  · intro h
    exact congrArg Sigma.snd h
  · intro h
    have hfst : c.state.fst = (G1M.accept : G1M.state).fst := by
      have h1 : (c.state.fst : Nat) < 1 := c.state.fst.isLt
      have h2 : ((G1M.accept : G1M.state).fst : Nat) < 1 :=
        (G1M.accept : G1M.state).fst.isLt
      exact Fin.ext (by omega)
    exact Sigma.ext hfst (by rw [hfst]; exact heq_of_eq h)

/-- **`TM.accepts` at `G1M`, unfolded once.**  The machine accepts exactly when
the configuration after its own `g1Clock` budget carries the literal
`g1AcceptState`. -/
theorem g1CS_accepts_iff_state {n : Nat} (x : Boolcube.Point n) :
    TM.accepts (M := G1M) n x = true ↔
      (TM.runConfig (M := G1M) (G1M.initialConfig x)
        (g1Clock n)).state.snd = g1AcceptState := by
  unfold TM.accepts
  rw [decide_eq_true_iff, g1CS_run_eq_runConfig]
  exact g1CS_state_eq_accept_iff _

/-- **Nonacceptance from a distinct control state.**  The contrapositive form
used by every `spec = none` branch below. -/
theorem g1CS_not_accepts_of_state {n : Nat} (x : Boolcube.Point n)
    (h : (TM.runConfig (M := G1M) (G1M.initialConfig x)
      (g1Clock n)).state.snd ≠ g1AcceptState) :
    TM.accepts (M := G1M) n x = false := by
  cases hacc : TM.accepts (M := G1M) n x with
  | false => rfl
  | true => exact absurd ((g1CS_accepts_iff_state x).mp hacc) h

/-! ## A request with a value accepts, with no canonicality hypothesis -/

/-- **A request with a value is canonical.**  The contrapositive of
`G1Request.spec_eq_none_of_not_canonical`, used to drop the canonicality
hypothesis from `g1CS_accepts_of_spec_some`. -/
theorem g1_canonical_of_spec_some {r : G1Request} {res : Bool}
    (hs : r.spec = some res) : r.Canonical := by
  by_contra hc
  rw [G1Request.spec_eq_none_of_not_canonical hc] at hs
  exact Option.noConfusion hs

/-- **A defined result accepts, hypothesis-free in canonicality.**  `res` may be
`false`: in main's transducer convention a completed computation accepts
whatever its value, and the value is read off the output cell by
`g1CS_gate_accept_output`. -/
theorem g1CS_accepts_true_of_spec_some (r : G1Request) (res : Bool)
    (hs : r.spec = some res) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true :=
  g1CS_accepts_of_spec_some r (g1_canonical_of_spec_some hs) res hs

/-! ## A noncanonical request: the literal reject sink -/

/-- **A noncanonical request ends its run in the literal reject state.**  The
validation prefix reaches `g1RejectState` after `(encodeG1 r).length + 4` steps
and the sink absorbs the rest of the clock. -/
theorem g1CS_noncanonical_clock_reject (r : G1Request) (hnc : ¬ r.Canonical) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1RejectState := by
  have hle : (encodeG1 r).length + 4 ≤ g1Clock (encodeG1 r).length :=
    g1_validate_le_clock _
  rw [show g1Clock (encodeG1 r).length =
        ((encodeG1 r).length + 4) +
          (g1Clock (encodeG1 r).length - ((encodeG1 r).length + 4)) from
      (Nat.add_sub_cancel' hle).symm,
    runConfig_add]
  exact g1CS_runConfig_reject_state _
    (g1CS_validate_noncanonical_reject_exact r hnc).1 _

/-- **The same statement as a `TM.run`.** -/
theorem g1CS_noncanonical_run_reject (r : G1Request) (hnc : ¬ r.Canonical) :
    (TM.run (M := G1M) (g1Point (encodeG1 r))).state.snd = g1RejectState := by
  rw [g1CS_run_eq_runConfig]
  exact g1CS_noncanonical_clock_reject r hnc

/-- **A noncanonical request does not accept.** -/
theorem g1CS_noncanonical_not_accepts (r : G1Request) (hnc : ¬ r.Canonical) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false := by
  refine g1CS_not_accepts_of_state (g1Point (encodeG1 r)) ?_
  rw [g1CS_noncanonical_clock_reject r hnc]
  exact g1RejectState_ne_accept

/-! ## Operand-domain projections of main's `operandsInBounds` -/

/-- A canonical `const` request never leaves the operand domain. -/
theorem g1_operandsInBounds_const {r : G1Request} (ht : r.tag = .const) :
    r.operandsInBounds := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht
  subst ht
  exact trivial

/-- The arity-1 operand domain is exactly "operand 1 selects". -/
theorem g1_operandsInBounds_unary {r : G1Request}
    (ht : r.tag = .input ∨ r.tag = .not) :
    r.operandsInBounds ↔ r.arg1 < r.vals.length := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht
  rcases ht with rfl | rfl <;> exact Iff.rfl

/-- The arity-2 operand domain is exactly "both operands select". -/
theorem g1_operandsInBounds_binary {r : G1Request}
    (ht : r.tag = .and ∨ r.tag = .or) :
    r.operandsInBounds ↔ (r.arg1 < r.vals.length ∧ r.arg2 < r.vals.length) := by
  rcases r with ⟨tag, a1, a2, vals⟩
  simp only at ht
  rcases ht with rfl | rfl <;> exact Iff.rfl

/-- **A canonical request with no value has an out-of-range operand.**  Stated
through main's `G1Request.spec_isSome_iff`, so the tag analysis happens once, in
the pure semantics, and not again here. -/
theorem g1_operands_oob_of_canonical_none (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = none) : ¬ r.operandsInBounds := by
  intro hob
  have hsome : r.spec.isSome = true :=
    (G1Request.spec_isSome_iff r).mpr ⟨hc, hob⟩
  rw [hs] at hsome
  exact Bool.noConfusion hsome

/-- **A canonical `const` request always has a value.**  The `const` class of
the `spec = none` split is empty; nothing about a `const` route is needed. -/
theorem g1_spec_ne_none_of_canonical_const (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) : r.spec ≠ none := by
  intro hs
  exact g1_operands_oob_of_canonical_none r hc hs (g1_operandsInBounds_const ht)

/-! ## The operand-1 out-of-range walk fits the unchanged clock

The first-absent-successor round is *cheaper* than the normal round it replaces
(`g1AWalkRoundOOBSteps = 16 * j + 8 * arg2 + 40` against
`g1AWalkRoundSteps = 16 * j + 8 * arg2 + 45`), so the whole out-of-range walk
fits inside the accumulated schedule of one more normal round and inherits the
existing clock bounds.  No new clock arithmetic and no new step definition is
introduced. -/

/-- **The data-OOB round costs no more than the normal round it replaces.** -/
theorem g1AWalkOOBRoute_le_driver (r : G1Request) (t : Nat) :
    g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t ≤
      g1AWalkDriverSteps r (t + 1) := by
  rw [g1AWalkDriverSteps_succ]
  simp only [g1AWalkRoundOOBSteps, g1AWalkRoundSteps]
  omega

/-- The unary operand-1 out-of-range route fits the unchanged public clock. -/
theorem g1AUnaryWalkOOBSteps_le_clock (r : G1Request) (t : Nat)
    (ht1 : t < r.arg1) :
    g1AUnaryCursorSteps r +
        (g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t) ≤
      g1Clock (encodeG1 r).length :=
  (Nat.add_le_add_left (g1AWalkOOBRoute_le_driver r t) _).trans
    (g1AUnaryDriverSteps_le_clock r (t + 1) (by omega))

/-- The binary operand-1 out-of-range route fits the unchanged public clock. -/
theorem g1ABinaryWalkOOBSteps_le_clock (r : G1Request) (t : Nat)
    (ht1 : t < r.arg1) :
    g1ABinaryCursorSteps r +
        (g1AWalkDriverSteps r t + g1AWalkRoundOOBSteps r t) ≤
      g1Clock (encodeG1 r).length :=
  (Nat.add_le_add_left (g1AWalkOOBRoute_le_driver r t) _).trans
    (g1ABinaryDriverSteps_le_clock r (t + 1) (by omega))

/-! ## The physical value witness for the data region -/

/-- The canonical `Nat → Bool` witness the S7 walk drivers ask for, read off the
request's own runtime value region. -/
def g1ValsWitness (r : G1Request) : Nat → Bool := fun j => r.vals[j]?.getD false

/-- In range, the witness is the selected value. -/
theorem g1ValsWitness_spec (r : G1Request) (j : Nat) (hj : j < r.vals.length) :
    r.vals[j]? = some (g1ValsWitness r j) := by
  rw [g1ValsWitness, List.getElem?_eq_getElem hj]
  rfl

/-- The witness at `0` is the head of a nonempty data region. -/
theorem g1ValsWitness_zero (r : G1Request) (a : Bool) (rest : List Bool)
    (hvals : r.vals = a :: rest) : g1ValsWitness r 0 = a := by
  rw [g1ValsWitness, hvals]
  rfl

/-! ## A canonical request with no value settles in a `bOOB` boundary -/

/-- **The arity-1 half of the out-of-range classification.**  Canonicality makes
`arg2` unused, so `spec = none` is exactly "operand 1 does not select".  Empty
data stops at S4's install boundary; otherwise the S7 walk stops at the first
absent successor, which is the last data slot. -/
theorem g1CS_canonical_none_clock_oob_unary (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (hs : r.spec = none) :
    ∃ ctx : G1Ctx,
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1OOBState ctx := by
  have hm : r.vals.length ≤ r.arg1 := by
    have hoob := g1_operands_oob_of_canonical_none r hc hs
    rw [g1_operandsInBounds_unary ht] at hoob
    omega
  rcases hvals : r.vals with _ | ⟨a, rest⟩
  · refine ⟨(g1Ctx0.withVB false).withRes (g1Residual r.tag false), ?_⟩
    have hstable : ∀ k,
        TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
            (g1AUnaryOOBSteps r + k) = g1AInstallOOBConfig r false := by
      intro k
      rw [runConfig_add, g1CS_readA_sigma0_unary_oob_exact r hc ht hvals,
        g1AInstallOOBConfig]
      exact g1CS_runConfig_oob_sink _ _ _ _ _ k
    rw [g1CS_pad_to_clock (g1AUnaryOOBSteps_le_clock r) hstable]
    rfl
  · have hpos : 0 < r.vals.length := by rw [hvals]; simp
    have ht1 : r.vals.length - 1 < r.arg1 := by omega
    have hlast : (r.vals.length - 1) + 1 = r.vals.length := by omega
    have hv : ∀ j, j ≤ r.vals.length - 1 →
        r.vals[j]? = some (g1ValsWitness r j) :=
      fun j hj => g1ValsWitness_spec r j (by omega)
    have hvals' : r.vals = g1ValsWitness r 0 :: rest := by
      rw [g1ValsWitness_zero r a rest hvals]; exact hvals
    refine ⟨g1AWalkCtx r false (g1ValsWitness r (r.vals.length - 1)), ?_⟩
    have hstable : ∀ k,
        TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
            (g1AUnaryCursorSteps r +
              (g1AWalkDriverSteps r (r.vals.length - 1) +
                g1AWalkRoundOOBSteps r (r.vals.length - 1)) + k) =
          g1AWalkOOBConfig r false (r.vals.length - 1) ht1 (by omega)
            (g1ValsWitness r (r.vals.length - 1))
            (hv (r.vals.length - 1) (Nat.le_refl _)) := by
      intro k
      rw [show g1AUnaryCursorSteps r +
            (g1AWalkDriverSteps r (r.vals.length - 1) +
              g1AWalkRoundOOBSteps r (r.vals.length - 1)) + k =
          g1AUnaryCursorSteps r +
            (g1AWalkDriverSteps r (r.vals.length - 1) +
              g1AWalkRoundOOBSteps r (r.vals.length - 1) + k) from by omega,
        runConfig_add,
        g1CS_readA_sigma0_unary_exact r hc ht (g1ValsWitness r 0) rest hvals']
      exact g1CS_aWalk_oob_driver_stable r false (r.vals.length - 1) ht1 hlast
        (g1ValsWitness r) hv k
    rw [g1CS_pad_to_clock
      (g1AUnaryWalkOOBSteps_le_clock r (r.vals.length - 1) ht1) hstable]
    rfl

/-- **The arity-2 half of the out-of-range classification.**  Operand 2 out of
range stops the run in pass B (`g1CS_readB_zero_oob_stable` at index `0`,
`g1CS_readB_positive_oob_stable` above it); otherwise operand 2 selects, so
operand 1 is the out-of-range one and the S7 walk stops at the last data
slot. -/
theorem g1CS_canonical_none_clock_oob_binary (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (hs : r.spec = none) :
    ∃ ctx : G1Ctx,
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1OOBState ctx := by
  rcases hb : r.vals[r.arg2]? with _ | bB
  · rcases Nat.eq_zero_or_pos r.arg2 with hz | hz
    · refine ⟨g1Ctx0, ?_⟩
      rw [g1CS_pad_to_clock (g1ReadBOOBSteps_le_clock r)
        (g1CS_readB_zero_oob_stable r hc ht hz hb)]
      rfl
    · have hm : r.vals.length ≤ r.arg2 := by
        by_contra hcon
        rw [List.getElem?_eq_getElem (by omega)] at hb
        exact Option.noConfusion hb
      refine ⟨g1BOOBCtx r, ?_⟩
      rw [g1CS_pad_to_clock (g1BOOBSteps_le_clock r)
        (g1CS_readB_positive_oob_stable r hc ht hz hm)]
      rfl
  · have h2 : r.arg2 < r.vals.length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hb
      exact Option.noConfusion hb
    have hm : r.vals.length ≤ r.arg1 := by
      have hoob := g1_operands_oob_of_canonical_none r hc hs
      rw [g1_operandsInBounds_binary ht] at hoob
      omega
    have hpos : 0 < r.vals.length := by omega
    have ht1 : r.vals.length - 1 < r.arg1 := by omega
    have hlast : (r.vals.length - 1) + 1 = r.vals.length := by omega
    have hv : ∀ j, j ≤ r.vals.length - 1 →
        r.vals[j]? = some (g1ValsWitness r j) :=
      fun j hj => g1ValsWitness_spec r j (by omega)
    have hne : r.vals ≠ [] := by
      intro hcase
      rw [hcase] at hpos
      simp at hpos
    obtain ⟨a, rest, hvals⟩ := List.exists_cons_of_ne_nil hne
    have hvals' : r.vals = g1ValsWitness r 0 :: rest := by
      rw [g1ValsWitness_zero r a rest hvals]; exact hvals
    refine ⟨g1AWalkCtx r bB (g1ValsWitness r (r.vals.length - 1)), ?_⟩
    have hstable : ∀ k,
        TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
            (g1ABinaryCursorSteps r +
              (g1AWalkDriverSteps r (r.vals.length - 1) +
                g1AWalkRoundOOBSteps r (r.vals.length - 1)) + k) =
          g1AWalkOOBConfig r bB (r.vals.length - 1) ht1 (by omega)
            (g1ValsWitness r (r.vals.length - 1))
            (hv (r.vals.length - 1) (Nat.le_refl _)) := by
      intro k
      rw [show g1ABinaryCursorSteps r +
            (g1AWalkDriverSteps r (r.vals.length - 1) +
              g1AWalkRoundOOBSteps r (r.vals.length - 1)) + k =
          g1ABinaryCursorSteps r +
            (g1AWalkDriverSteps r (r.vals.length - 1) +
              g1AWalkRoundOOBSteps r (r.vals.length - 1) + k) from by omega,
        runConfig_add,
        g1CS_readA_sigma0_binary_exact r hc ht (g1ValsWitness r 0) bB rest hb
          hvals']
      exact g1CS_aWalk_oob_driver_stable r bB (r.vals.length - 1) ht1 hlast
        (g1ValsWitness r) hv k
    rw [g1CS_pad_to_clock
      (g1ABinaryWalkOOBSteps_le_clock r (r.vals.length - 1) ht1) hstable]
    rfl

/-- **A canonical request with no value settles in a `bOOB` boundary.**  The tag
split is exhaustive: a canonical `const` request always has a value, an
`input`/`not` request is `g1CS_canonical_none_clock_oob_unary`, and `and`/`or`
is `g1CS_canonical_none_clock_oob_binary`.

`bOOB` is a boundary, **not** a rejection: its row is idle
(`g1Transition_bOOB_stable`), so it reaches neither sink, and this module adds
no transition. -/
theorem g1CS_canonical_none_clock_oob (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = none) :
    ∃ ctx : G1Ctx,
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1Clock (encodeG1 r).length)).state.snd = g1OOBState ctx := by
  rcases htag : r.tag with h | h | h | h | h
  · exact g1CS_canonical_none_clock_oob_unary r hc (Or.inl htag) hs
  · exact absurd hs (g1_spec_ne_none_of_canonical_const r hc htag)
  · exact g1CS_canonical_none_clock_oob_unary r hc (Or.inr htag) hs
  · exact g1CS_canonical_none_clock_oob_binary r hc (Or.inl htag) hs
  · exact g1CS_canonical_none_clock_oob_binary r hc (Or.inr htag) hs

/-- **The same statement as a `TM.run`**, at the level of the mode. -/
theorem g1CS_canonical_none_run_oob (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = none) :
    (TM.run (M := G1M) (g1Point (encodeG1 r))).state.snd.mode = G1Mode.bOOB := by
  obtain ⟨ctx, hctx⟩ := g1CS_canonical_none_clock_oob r hc hs
  rw [g1CS_run_eq_runConfig, hctx]
  rfl

/-- **A canonical request with no value does not accept.**  It does not reject
either: see `g1OOBState_ne_reject`. -/
theorem g1CS_canonical_none_not_accepts (r : G1Request) (hc : r.Canonical)
    (hs : r.spec = none) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false := by
  obtain ⟨ctx, hctx⟩ := g1CS_canonical_none_clock_oob r hc hs
  refine g1CS_not_accepts_of_state (g1Point (encodeG1 r)) ?_
  rw [hctx]
  exact g1OOBState_ne_accept ctx

/-- **No request without a value accepts**, canonical or not. -/
theorem g1CS_none_not_accepts (r : G1Request) (hs : r.spec = none) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false := by
  by_cases hc : r.Canonical
  · exact g1CS_canonical_none_not_accepts r hc hs
  · exact g1CS_noncanonical_not_accepts r hc

/-! ## The closing endpoints -/

/-- **Exact-clock acceptance on the standard encoded point is definedness of the
pure result.**  For **every** `r : G1Request` — canonical or not, with a value
or without one — the one fixed machine, started on the standard encoded point
`g1Point (encodeG1 r)` and read after exactly its own
`g1Clock (encodeG1 r).length` steps, carries the accepting control state exactly
when `r.spec` is a `some`.

This is main's transducer convention, the G1 instance of
`t1CS_accepts_eq_isSome`: **both** `some false` and `some true` accept, because
both output-done handoffs enter the same literal `g1AcceptState`; the result
*value* is on the output cell (`g1CS_gate_accept_output`), not in the verdict.

Acceptance here is exact-step, not halting, and the statement is scoped to the
image of `encodeG1`: a physical word outside that image is not covered, so this
is **not** a language-membership theorem.  Both directions are proved, from the
real `G1M.initialConfig` by the real `TM.runConfig` relation, and the three
classes of request are discharged separately: a value, a noncanonical word, and
a canonical word with an out-of-range operand.  Only the noncanonical class is a
rejection; the out-of-range class idles at a `bOOB` boundary. -/
theorem g1CS_accepts_eq_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      r.spec.isSome := by
  rcases hspec : r.spec with _ | res
  · rw [g1CS_none_not_accepts r hspec]
    rfl
  · rw [g1CS_accepts_true_of_spec_some r res hspec]
    rfl

/-- Propositional form of the acceptance theorem. -/
theorem g1CS_accepts_iff_spec_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true ↔
      r.spec.isSome = true := by
  rw [g1CS_accepts_eq_isSome r]

/-- **The verdict is well-formedness.**  Honest machine execution
(`g1CS_accepts_eq_isSome`) composed with main's pure domain characterization
`G1Request.spec_isSome_iff`: the one fixed machine, run on the standard encoded
word of `r` for exactly its own public clock, accepts exactly when `r` is
canonical *and* both its operands select.  Same scope as
`g1CS_accepts_eq_isSome` — the encoded points only, exact-step, not halting, not
a language theorem.  This is not a decidability wrapper: the `→` direction runs
the machine and the `←` direction runs it too, through the three route classes
above. -/
theorem g1CS_accepts_iff_wellFormed (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true ↔
      r.WellFormed := by
  rw [g1CS_accepts_eq_isSome r]
  exact G1Request.spec_isSome_iff r

/-- The Boolean form of `g1CS_accepts_iff_wellFormed`. -/
theorem g1CS_accepts_eq_decide_wellFormed (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      decide r.WellFormed := by
  cases hacc : TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r))
    with
  | true => exact (decide_eq_true ((g1CS_accepts_iff_wellFormed r).mp hacc)).symm
  | false =>
      refine (decide_eq_false ?_).symm
      intro hwf
      rw [(g1CS_accepts_iff_wellFormed r).mpr hwf] at hacc
      exact Bool.noConfusion hacc

/-- **Nonacceptance is exactly undefinedness.**  The complement of the
capstone, which keeps `spec = some false` on the accepting side. -/
theorem g1CS_not_accepts_iff_spec_none (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = false ↔
      r.spec = none := by
  constructor
  · intro hacc
    rcases hspec : r.spec with _ | res
    · rfl
    · rw [g1CS_accepts_true_of_spec_some r res hspec] at hacc
      exact Bool.noConfusion hacc
  · exact g1CS_none_not_accepts r

end Pnp3.Internal.PsubsetPpoly.TM
