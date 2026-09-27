import Complexity.Uniform.V1.AcceptMerge

/-!
Surface pins for the Part A G3g generic half: the accept merge `M.mergeAccept e` of a fixed
`UniformTM`, which retargets every row aiming at a second absorbing successful endpoint `e` to
`M.accept`, so that the landed `UniformTM.seq` routes both endpoints into the next machine's start.
Every public declaration is restated; `check_mergeState_pins` bundles the retargeting-map facts,
`check_mergeAccept_step` the three row equations and `check_mergeAccept_runs` the four run facts,
each bundled conjunct carrying exactly the hypotheses of the declaration it pins, so none of the
four hypothesis-free or one-hypothesis facts is restated under a stronger premise.

The literal probe.  `twin` has four states: on a blank it writes `some true`, moves right and
accepts; on `true` it stops in its second absorbing endpoint `e3 = ⟨3, _⟩`, neither verdict; on
`false` it rejects in place.  `merged = twin.mergeAccept e3`; `reader` accepts on a blank and
rejects otherwise; `pair = merged.seq reader` is the routed composition and `stuck = twin.seq
reader` the same composition *without* the merge, the negative control.  `check_merge_literal_probe`
reduces them by kernel computation: `merged`'s row out of `0` on `true` targets `1` where `twin`'s
targets `3`, and no merged row targets `3`; on `true` `twin` is in `3` after one step while
`merged` is in its accept; `pair` is in the reader's start `4` after **one** step on `true` — the
merged endpoint, routed — and `stuck` sticks in the dead left state `3`, in neither composed
verdict.

Not here: no concrete Part A machine, clock or budget, no first-arrival theorem for any concrete
machine, and no `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation` or
language-membership statement about a merged or composed machine. -/

namespace Pnp3.Tests.UniformV1AcceptMergeSurfaceTests
open Complexity.Uniform.V1

def check_mergeState (M : UniformTM) : Fin M.stateCount → Fin M.stateCount → Fin M.stateCount :=
  M.mergeState
def check_mergeAccept (M : UniformTM) : Fin M.stateCount → UniformTM := M.mergeAccept
def check_mergeConfig (M : UniformTM) (e : Fin M.stateCount) {n B : Nat} :
    Config M.stateCount n B → Config (M.mergeAccept e).stateCount n B := M.mergeConfig e

/-- The retargeting map, restated in full. -/
theorem check_mergeState_pins (M : UniformTM) (e q : Fin M.stateCount) (h : q ≠ e)
    (ha : e ≠ M.accept) :
    M.mergeState e e = M.accept ∧ M.mergeState e q = q ∧ M.mergeState e M.accept = M.accept ∧
      M.mergeState e q ≠ e :=
  ⟨M.mergeState_self e, M.mergeState_of_ne h, M.mergeState_accept e, M.mergeState_ne e ha q⟩

/-- The merged table, restated in full. -/
theorem check_mergeAccept_pins (M : UniformTM) (e : Fin M.stateCount) :
    (M.mergeAccept e).stateCount = M.stateCount ∧
      (M.mergeAccept e).start = M.mergeState e M.start ∧
      (M.mergeAccept e).accept = M.accept ∧ (M.mergeAccept e).reject = M.reject ∧
      (∀ q s, (M.mergeAccept e).rawStep q s =
        (M.mergeState e (M.rawStep q s).1, (M.rawStep q s).2.1, (M.rawStep q s).2.2)) :=
  M.mergeAccept_pins e

/-- The merged embedding, restated in full. -/
theorem check_mergeConfig_pins (M : UniformTM) (e : Fin M.stateCount) {n B : Nat}
    (c : Config M.stateCount n B) :
    (M.mergeConfig e c).state = M.mergeState e c.state ∧
      (M.mergeConfig e c).head = c.head ∧ (M.mergeConfig e c).tape = c.tape ∧
      (c.state = e ∨ c.state = M.accept →
        (M.mergeConfig e c).state = (M.mergeAccept e).accept) ∧
      (c.state ≠ e → (M.mergeConfig e c).state = c.state) :=
  M.mergeConfig_pins e c

/-- The rows of the merged public step, restated in full. -/
theorem check_mergeAccept_step (M : UniformTM) (e : Fin M.stateCount) {q : Fin M.stateCount}
    (ha : q ≠ M.accept) (hr : q ≠ M.reject) (he : e ≠ M.reject) (hea : e ≠ M.accept)
    (p : Fin M.stateCount) (s : Option Bool) :
    (M.mergeAccept e).step q s =
        (M.mergeState e (M.step q s).1, (M.step q s).2.1, (M.step q s).2.2) ∧
      (M.mergeAccept e).step p s =
        (M.mergeState e (M.step p s).1, (M.step p s).2.1, (M.step p s).2.2) ∧
      ((M.mergeAccept e).step p s).1 ≠ e :=
  ⟨M.mergeAccept_step_of_ne e ha hr s, M.mergeAccept_step e he p s,
    M.mergeAccept_step_ne e hea he p s⟩

/-- One merged transition off `e`, restated in full. -/
theorem check_mergeAccept_stepConfig (M : UniformTM) (e : Fin M.stateCount) {n B : Nat}
    (c : Config M.stateCount n B) (hne : c.state ≠ e) :
    (M.mergeAccept e).stepConfig (M.mergeConfig e c) = M.mergeConfig e (M.stepConfig c) :=
  M.mergeAccept_stepConfig e c hne

/-- The merged run, restated in full: the `M` run re-embedded up to `T`, never in `e`, both
success endpoints as the merged accept at `T`, and no merged accept before `T`. -/
theorem check_mergeAccept_runs (M : UniformTM) (e : Fin M.stateCount) (ha : e ≠ M.accept)
    (hr : e ≠ M.reject) {n B : Nat} (c : Config M.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M.run t c).state ≠ e ∧ (M.run t c).state ≠ M.accept)
    (hT : (M.run T c).state = e ∨ (M.run T c).state = M.accept) :
    (∀ t, t ≤ T → (M.mergeAccept e).run t (M.mergeConfig e c) = M.mergeConfig e (M.run t c)) ∧
      (∀ t, ((M.mergeAccept e).run t (M.mergeConfig e c)).state ≠ e) ∧
      (M.mergeAccept e).run T (M.mergeConfig e c) =
        ⟨(M.mergeAccept e).accept, (M.run T c).head, (M.run T c).tape⟩ ∧
      (∀ t, t < T →
        ((M.mergeAccept e).run t (M.mergeConfig e c)).state ≠ (M.mergeAccept e).accept) :=
  ⟨M.mergeAccept_run e c (fun t ht => (hwork t ht).1), M.mergeAccept_run_ne e ha hr c,
    M.mergeAccept_run_accept e hr c (fun t ht => (hwork t ht).1) hT,
    M.mergeAccept_run_ne_accept e c hwork⟩

/-- The merged left block of a composition, restated in full. -/
theorem check_mergeAccept_seq_run_left (M₁ M₂ : UniformTM) (e : Fin M₁.stateCount) {n B : Nat}
    (c : Config M₁.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M₁.run t c).state ≠ e ∧ (M₁.run t c).state ≠ M₁.accept) :
    ∀ t, t ≤ T →
      ((M₁.mergeAccept e).seq M₂).run t
          ((M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e c)) =
        (M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e (M₁.run t c)) :=
  M₁.mergeAccept_seq_run_left M₂ e c hwork

/-- The two-success-source handoff, restated in full. -/
theorem check_mergeAccept_seq_handoff (M₁ M₂ : UniformTM) (e : Fin M₁.stateCount) {n B : Nat}
    (c : Config M₁.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M₁.run t c).state ≠ e ∧ (M₁.run t c).state ≠ M₁.accept)
    (hT : (M₁.run T c).state = e ∨ (M₁.run T c).state = M₁.accept)
    (he : e ≠ M₁.reject) (s : Nat) :
    ((M₁.mergeAccept e).seq M₂).run (T + s)
        ((M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e c)) =
      (M₁.mergeAccept e).seqEmbedRight M₂
        (M₂.run s ⟨M₂.start, (M₁.run T c).head, (M₁.run T c).tape⟩) :=
  M₁.mergeAccept_seq_handoff M₂ e c hwork hT he s

/-- The rejecting handoff through the merge, restated in full. -/
theorem check_mergeAccept_seq_reject_handoff (M₁ M₂ : UniformTM) (e : Fin M₁.stateCount)
    {n B : Nat} (c : Config M₁.stateCount n B) {T : Nat}
    (hwork : ∀ t, t < T → (M₁.run t c).state ≠ e) (hrej : (M₁.run T c).state = M₁.reject)
    (he : e ≠ M₁.reject) (s : Nat) :
    ((M₁.mergeAccept e).seq M₂).run (T + s)
        ((M₁.mergeAccept e).seqEmbedRouted M₂ (M₁.mergeConfig e c)) =
      ⟨((M₁.mergeAccept e).seq M₂).reject, (M₁.run T c).head, (M₁.run T c).tape⟩ :=
  M₁.mergeAccept_seq_reject_handoff M₂ e c hwork hrej he s

/-! ### Independent literal reduction probe -/

/-- On a blank: write `some true`, move right, accept.  On `true`: stop in the second absorbing
endpoint `3`, neither verdict.  On `false`: reject in place. -/
private def twin : UniformTM where
  stateCount := 4
  start := ⟨0, by decide⟩
  accept := ⟨1, by decide⟩
  reject := ⟨2, by decide⟩
  accept_ne_reject := by decide
  rawStep := fun q s =>
    match q.val, s with
    | 0, none => (⟨1, by decide⟩, some true, .right)
    | 0, some true => (⟨3, by decide⟩, some true, .stay)
    | 0, some false => (⟨2, by decide⟩, some false, .stay)
    | _, s => (q, s, .stay)

private def e3 : Fin twin.stateCount := ⟨3, by decide⟩
private def merged : UniformTM := twin.mergeAccept e3

/-- On a blank: write `some false`, accept in place.  On anything else: reject in place. -/
private def reader : UniformTM where
  stateCount := 3
  start := ⟨0, by decide⟩
  accept := ⟨1, by decide⟩
  reject := ⟨2, by decide⟩
  accept_ne_reject := by decide
  rawStep := fun q s =>
    match q.val, s with
    | 0, none => (⟨1, by decide⟩, some false, .stay)
    | 0, some b => (⟨2, by decide⟩, some b, .stay)
    | _, s => (q, s, .stay)

private def pair : UniformTM := merged.seq reader
/-- The negative control: the same composition without the merge. -/
private def stuck : UniformTM := twin.seq reader
private def emptyWord : Bitstring 0 := fun i => Fin.elim0 i
private def trueWord : Bitstring 1 := fun _ => true
private def falseWord : Bitstring 1 := fun _ => false

/-- **The merged and composed runs, reduced**, at budget `2`.  Each conjunct is a claim about its
own literal machine and input only. -/
theorem check_merge_literal_probe :
    merged.stateCount = 4 ∧ merged.accept.val = 1 ∧ merged.reject.val = 2 ∧
    (twin.step ⟨0, by decide⟩ (some true)).1.val = 3 ∧
    (merged.step ⟨0, by decide⟩ (some true)).1.val = 1 ∧
    (∀ q : Fin merged.stateCount, (merged.step q none).1 ≠ e3 ∧
      (merged.step q (some true)).1 ≠ e3 ∧ (merged.step q (some false)).1 ≠ e3) ∧
    (twin.run 1 (initialConfig twin 2 trueWord)).state.val = 3 ∧
    (merged.run 1 (initialConfig merged 2 trueWord)).state = merged.accept ∧
    (merged.run 1 (initialConfig merged 2 trueWord)).head.val = 0 ∧
    (merged.run 1 (initialConfig merged 2 emptyWord)).state = merged.accept ∧
    (merged.run 1 (initialConfig merged 2 emptyWord)).tape ⟨0, by decide⟩ = some true ∧
    (merged.run 1 (initialConfig merged 2 falseWord)).state = merged.reject ∧
    pair.stateCount = 7 ∧ pair.accept.val = 5 ∧ pair.reject.val = 6 ∧
    (pair.run 1 (initialConfig pair 2 trueWord)).state.val = 4 ∧
    (pair.run 2 (initialConfig pair 2 trueWord)).state = pair.reject ∧
    (pair.run 1 (initialConfig pair 2 emptyWord)).state.val = 4 ∧
    (pair.run 2 (initialConfig pair 2 emptyWord)).state = pair.accept ∧
    (pair.run 1 (initialConfig pair 2 falseWord)).state = pair.reject ∧
    (stuck.run 6 (initialConfig stuck 2 trueWord)).state.val = 3 ∧
    (stuck.run 6 (initialConfig stuck 2 trueWord)).state ≠ stuck.accept ∧
    (stuck.run 6 (initialConfig stuck 2 trueWord)).state ≠ stuck.reject := by
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1AcceptMergeSurfaceTests
