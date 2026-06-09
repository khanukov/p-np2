import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverTapeInv
import Pnp4.Frontier.ContractExpansion.TreeMCSPCertTokens

/-!
# `driverStrongInv` — D2t-5b (Block A1a): the strong driver tape invariant

`driverTapeInv` (#1605) pinned the region **contents**; this module supplies the **strong** invariant the
step-realization proofs actually thread — closing the review-deferred geometry/coherence gaps and fixing a
latent anchoring mismatch:

* **Dynamic anchors, derived — not parameters.**  Every region's live anchor is a *function of the abstract
  state*: the certificate cursor is `certEnd − |encodePreorder toks|` (the unread suffix **ends** at the fixed
  `certEnd`), the output anchor is `workBase − 1 − |out|`, the stacks' tops are `valBound − |encodeNatStack1 val|`
  / `ctrlBound − |encodeCtrlStack1 ctrl|` (the **shifted** stack codecs — see the section below: every field
  opens with a `1`, so the tops are scan-detectable on a `Bool` tape).  The cursor/`certBase ≤ cursor` coupling (review concern #2) is
  thereby **definitional**, and the push realization direction is honoured: `pushCtrlFrameRealizes` /
  `writeNatField_extends_natStack` grow a stack **leftward from a moving top** (frame lands on `[p, p+len)`,
  old stack at `[p+len, …)`), so the stacks here are anchored at their **moving top** against a **fixed
  bottom** (`valBound`/`ctrlBound`) — *not* at a fixed left base as in `driverTapeInv`'s stack clauses, which
  matched only the empty-stack initial state.  `driverTapeInv` remains valid for its merged uses
  (initialisation; cert/WORK clauses); `driverStrongInv` is what the realization layer consumes.
* **The COUNT region: the output window is `encodeGateStream`-shaped.**  The driver must push the fresh
  WORK index `out.length` (a value no tape region of `driverTapeInv` stores) — so the strong invariant keeps
  a **unary gate count** `1^|out|` growing **leftward** of a fixed terminator cell `workBase − 1`, with the
  records extending rightward from `workBase`.  The combined window starting at `workBase − 1 − |out|` spells
  `unaryField |out| ++ encodeGateRecordStream out` — which is **exactly `encodeGateStream out`**
  (`driverStrongInv_out_encodeGateStream`): at the terminal state the output region *already* holds the
  count-prefixed stream `transcodeWitness` demands, so D2t-6a (count prefix) needs no separate pass.
* **Length-aware non-overlap (review concern #2).**  `DriverZones.WellFormed` chains the fixed zone bounds
  `certBase ≤ certEnd ≤ outBase < workBase ≤ workEnd ≤ valLeft ≤ valBound ≤ ctrlLeft ≤ ctrlBound ≤ L`, and
  the invariant carries the per-state **fit** clauses (count fits left of `workBase`, records fit below
  `workEnd`, each stack fits above its `…Left` floor), so distinct regions provably never overlap at any
  reachable extent.
* **Validity + cheap coherence (the pointwise half of review concern #3).**  `ValidCertTokens toks` (non-vacuous
  certificate clause, #1607) and `settling = true → val ≠ []` (a settling state always carries the
  just-completed subtree's root index), the latter **step-preserved pointwise**
  (`DriveState.step_preserves_settling_val`).  The *reachability-dependent* coherence (e.g. sink soundness
  "settling ∧ ctrl = [] → toks = []") genuinely needs the run trace and is the next brick (A1b).

Also ships the generic window splitters `windowSpells_append_left` / `windowSpells_append_right` (project a
spelled concatenation onto its halves) and the derived projections `driverStrongInv_count_window` /
`driverStrongInv_records_window` (the count field alone at its moving anchor; the records alone at the fixed
`workBase`) — the shapes the per-arm body lemmas consume.

**Progress classification (AGENTS.md): Infrastructure** — a strengthened tape-layout invariant + initial-state
lemma + pointwise coherence preservation, proven against the verified codecs; builds no machine and proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Fixed zone bounds of the driver tape (the layout
`[ input | certificate | COUNT ← | WORK → | STACK_val ← | STACK_ctrl ← | … ]`).  `certEnd` is the certificate's
fixed right end (the cursor advances toward it); `workBase − 1` is the count field's fixed terminator cell,
with the unary count growing leftward toward `outBase` and the records growing rightward toward `workEnd`;
`valBound` / `ctrlBound` are the stacks' fixed bottoms, each stack growing leftward toward its `…Left` floor. -/
structure DriverZones where
  certBase : Nat
  certEnd : Nat
  outBase : Nat
  workBase : Nat
  workEnd : Nat
  valLeft : Nat
  valBound : Nat
  ctrlLeft : Nat
  ctrlBound : Nat

/-- **Zone-chain well-formedness**: the fixed bounds sit in order on a length-`L` tape (`outBase < workBase`
leaves room for the count terminator cell `workBase − 1` even at count `0`). -/
def DriverZones.WellFormed (z : DriverZones) (L : Nat) : Prop :=
  z.certBase ≤ z.certEnd ∧ z.certEnd ≤ z.outBase ∧ z.outBase < z.workBase ∧ z.workBase ≤ z.workEnd
    ∧ z.workEnd ≤ z.valLeft ∧ z.valLeft ≤ z.valBound ∧ z.valBound ≤ z.ctrlLeft
    ∧ z.ctrlLeft ≤ z.ctrlBound ∧ z.ctrlBound ≤ L

/-! ### The driver's shifted stack codecs (navigation-sound on a `Bool` tape)

A head hop between regions can only land by **scanning homogeneous content to a flip** (the proven
`selfLoopScan*` pattern — there are no markers on a `Bool` tape).  A stack top is therefore only
scan-detectable if its first cell is always `1`.  The plain codecs violate that: `unaryField 0 = [0]`
(and index `0` is a *real* value-stack entry — the first gate), and `ITag.tagCode .tnot = 0` makes a
`tnot` frame start with a bare `0`.  The driver's stacks are *internal* (written and read only by the
driver), so their on-tape format is ours to choose: each value field is stored **shifted** as
`unaryField (v + 1)` and each frame's tag field as `unaryField (tagCode + 1)` — every field now opens
with a `1`, so region boundaries are unambiguous to scans in both directions.  (The `remaining` field
needs no shift: reachable frames have `rem ≥ 1`, `pendingFrames_rem_bounds`.) -/

/-- The **shifted** value-stack codec: entry `v` is stored as `unaryField (v + 1) = 1^(v+1) 0`, so every
field opens with a `1` (index `0` included) and the stack top is scan-detectable. -/
def encodeNatStack1 : List Nat → List Bool
  | [] => []
  | v :: rest => unaryField (v + 1) ++ encodeNatStack1 rest

@[simp] theorem encodeNatStack1_nil : encodeNatStack1 [] = [] := rfl

@[simp] theorem encodeNatStack1_cons (v : Nat) (rest : List Nat) :
    encodeNatStack1 (v :: rest) = unaryField (v + 1) ++ encodeNatStack1 rest := rfl

/-- Shifted pop: one unary-field read off the encoded stack returns `v + 1` and the encoded tail. -/
@[simp] theorem decodeUnaryField_encodeNatStack1_cons (v : Nat) (rest : List Nat) :
    decodeUnaryField (encodeNatStack1 (v :: rest)) = some (v + 1, encodeNatStack1 rest) := by
  simp [encodeNatStack1]

/-- A nonempty shifted value stack **opens with a `1`** — the scan-detectability fact. -/
theorem encodeNatStack1_head_true (v : Nat) (rest : List Nat) :
    (encodeNatStack1 (v :: rest)).head? = some true := by
  simp [encodeNatStack1, unaryField, List.replicate_succ]

/-- The **shifted** control-frame codec: the tag field is stored as `unaryField (tagCode + 1)` (codes
`1`–`3`, never a bare `0`), the remaining-count field unshifted (reachable `rem ≥ 1`). -/
def encodeCtrlFrame1 : ITag × Nat → List Bool
  | (tag, rem) => unaryField (tag.tagCode + 1) ++ unaryField rem

/-- The shifted control-stack codec (top-first, like `encodeCtrlStack`). -/
def encodeCtrlStack1 : List (ITag × Nat) → List Bool
  | [] => []
  | f :: rest => encodeCtrlFrame1 f ++ encodeCtrlStack1 rest

@[simp] theorem encodeCtrlStack1_nil : encodeCtrlStack1 [] = [] := rfl

@[simp] theorem encodeCtrlStack1_cons (f : ITag × Nat) (rest : List (ITag × Nat)) :
    encodeCtrlStack1 (f :: rest) = encodeCtrlFrame1 f ++ encodeCtrlStack1 rest := rfl

/-- A nonempty shifted control stack **opens with a `1`**. -/
theorem encodeCtrlStack1_head_true (f : ITag × Nat) (rest : List (ITag × Nat)) :
    (encodeCtrlStack1 (f :: rest)).head? = some true := by
  obtain ⟨tag, rem⟩ := f
  simp [encodeCtrlFrame1, unaryField, List.replicate_succ]

/-- A spelled concatenation spells its **left** half at the same base. -/
theorem windowSpells_append_left {L : Nat} (tape : Fin L → Bool) (base : Nat)
    (xs ys : List Bool) (h : windowSpells tape base (xs ++ ys)) :
    windowSpells tape base xs := by
  obtain ⟨hfit, hcells⟩ := h
  have hl : (xs ++ ys).length = xs.length + ys.length := by simp
  rw [hl] at hfit
  refine ⟨by omega, fun q hlo hhi => ?_⟩
  rw [hcells q hlo (by rw [hl]; omega),
    List.getD_append xs ys false ((q : Nat) - base) (by omega)]

/-- A spelled concatenation spells its **right** half at the shifted base. -/
theorem windowSpells_append_right {L : Nat} (tape : Fin L → Bool) (base : Nat)
    (xs ys : List Bool) (h : windowSpells tape base (xs ++ ys)) :
    windowSpells tape (base + xs.length) ys := by
  obtain ⟨hfit, hcells⟩ := h
  have hl : (xs ++ ys).length = xs.length + ys.length := by simp
  rw [hl] at hfit
  refine ⟨by omega, fun q hlo hhi => ?_⟩
  rw [hcells q (by omega) (by rw [hl]; omega),
    List.getD_append_right xs ys false ((q : Nat) - base) (by omega)]
  congr 1
  omega

/-- **The strong driver tape invariant.**  All four live anchors are *derived* from the abstract state `st`:

* **certificate** — the unread suffix `encodePreorder st.toks` ends at the fixed `certEnd` (anchor
  `certEnd − |·|`), and fits above `certBase` (the definitional cursor coupling);
* **output** — the window at `workBase − 1 − |st.out|` spells `unaryField |st.out| ++
  encodeGateRecordStream st.out` (unary count growing leftward of the fixed terminator cell, records growing
  rightward from `workBase`), fitting between `outBase` and `workEnd`;
* **stacks** — each stack's encoding (the **shifted** codecs `encodeNatStack1`/`encodeCtrlStack1`, see
  above) ends at its fixed bottom (`valBound`/`ctrlBound`), the moving top `…Bound − |·|` staying above
  its `…Left` floor (matching the leftward push realization);
* **validity/coherence** — `ValidCertTokens st.toks`, and a settling state always carries a value-stack top;
* **geometry** — the fixed zone chain `z.WellFormed L` is carried as the leading conjunct, so the invariant
  alone supports every non-overlap argument (it is state-independent and threads through steps unchanged). -/
def driverStrongInv {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverZones) (tape : Fin L → Bool) (st : DriveState n) : Prop :=
  z.WellFormed L
  ∧ windowSpells tape (z.certEnd - (encodePreorder width h_width st.toks).length)
      (encodePreorder width h_width st.toks)
  ∧ z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd
  ∧ windowSpells tape (z.workBase - 1 - st.out.length)
      (unaryField st.out.length ++ encodeGateRecordStream st.out)
  ∧ z.outBase + st.out.length + 1 ≤ z.workBase
  ∧ z.workBase + (encodeGateRecordStream st.out).length ≤ z.workEnd
  ∧ windowSpells tape (z.valBound - (encodeNatStack1 st.val).length) (encodeNatStack1 st.val)
  ∧ z.valLeft + (encodeNatStack1 st.val).length ≤ z.valBound
  ∧ windowSpells tape (z.ctrlBound - (encodeCtrlStack1 st.ctrl).length) (encodeCtrlStack1 st.ctrl)
  ∧ z.ctrlLeft + (encodeCtrlStack1 st.ctrl).length ≤ z.ctrlBound
  ∧ ValidCertTokens st.toks
  ∧ (st.settling = true → st.val ≠ [])

/-- The output window of `driverStrongInv` **is** the self-delimiting gate stream: `unaryField |out| ++
encodeGateRecordStream out = encodeGateStream out`.  At the terminal state (`out = (flatten c).gates`) the
output region therefore already spells the count-prefixed stream `transcodeWitness` expects — the D2t-6a
count prefix is maintained in-band, not added by a separate pass. -/
theorem driverStrongInv_out_encodeGateStream {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverZones) (tape : Fin L → Bool) (st : DriveState n)
    (h : driverStrongInv width h_width z tape st) :
    windowSpells tape (z.workBase - 1 - st.out.length) (encodeGateStream st.out) := by
  simpa [encodeGateStream] using h.2.2.2.1

/-- Projection: the unary **count field** alone, at its moving anchor `workBase − 1 − |out|`. -/
theorem driverStrongInv_count_window {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverZones) (tape : Fin L → Bool) (st : DriveState n)
    (h : driverStrongInv width h_width z tape st) :
    windowSpells tape (z.workBase - 1 - st.out.length) (unaryField st.out.length) :=
  windowSpells_append_left tape _ _ _ h.2.2.2.1

/-- Projection: the **record stream** alone, at the fixed `workBase` (the count terminator sits at
`workBase − 1`, so the records start exactly at `workBase` whenever the count fits left of it). -/
theorem driverStrongInv_records_window {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverZones) (tape : Fin L → Bool) (st : DriveState n)
    (h : driverStrongInv width h_width z tape st) :
    windowSpells tape z.workBase (encodeGateRecordStream st.out) := by
  have hfit := h.2.2.2.2.1
  have hproj := windowSpells_append_right tape (z.workBase - 1 - st.out.length)
    (unaryField st.out.length) (encodeGateRecordStream st.out) h.2.2.2.1
  rw [unaryField_length] at hproj
  have : z.workBase - 1 - st.out.length + (st.out.length + 1) = z.workBase := by omega
  rwa [this] at hproj

/-- **The cheap coherence clause is step-preserved pointwise** (no reachability needed): a settling
post-state always carries a value-stack top — the leaf read and the pop-emit arms push one, and every other
arm clears the flag. -/
theorem DriveState.step_preserves_settling_val {n : Nat} (s : DriveState n)
    (h : s.settling = true → s.val ≠ []) :
    s.step.settling = true → s.step.val ≠ [] := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  cases settling with
  | false =>
      cases toks with
      | nil => exact h
      | cons tok toks' =>
          cases tok with
          | leaf g => intro _; simp [DriveState.step]
          | node tag => intro hs; simp [DriveState.step] at hs
  | true =>
      cases ctrl with
      | nil => intro hs; simp [DriveState.step] at hs
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => intro hs; simp [DriveState.step] at hs
                | cons i vs => intro _; simp [DriveState.step]
            | tand =>
                cases val with
                | nil => intro hs; simp [DriveState.step] at hs
                | cons i2 rest =>
                    cases rest with
                    | nil => intro hs; simp [DriveState.step] at hs
                    | cons i1 vs => intro _; simp [DriveState.step]
            | tor =>
                cases val with
                | nil => intro hs; simp [DriveState.step] at hs
                | cons i2 rest =>
                    cases rest with
                    | nil => intro hs; simp [DriveState.step] at hs
                    | cons i1 vs => intro _; simp [DriveState.step]
          · intro hs; simp [DriveState.step, hrem] at hs

/-- **The strong invariant holds at the start.**  Hypotheses: the zone chain is well-formed; the certificate
`encodeCircuitTree c` is laid out at `certBase` and ends exactly at `certEnd`; and the count terminator cell
`workBase − 1` holds `0` (the empty count field `unaryField 0 = [false]`).  Then the initial driver state
`⟨preorder c, [], [], [], false⟩` satisfies `driverStrongInv`: the certificate clause is
`encodePreorder_preorder` (#1604) re-anchored by the length equation; the output clause is the terminator
cell; the stack windows are empty at their bottoms (`windowSpells_nil`); validity is
`validCertTokens_preorder` (#1607). -/
theorem driverStrongInv_init {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverZones) (tape : Fin L → Bool) (c : CircuitTree n)
    (hwf : z.WellFormed L)
    (hcert : windowSpells tape z.certBase (encodeCircuitTree width h_width c))
    (hlen : z.certBase + (encodeCircuitTree width h_width c).length = z.certEnd)
    (hcount0 : windowSpells tape (z.workBase - 1) [false]) :
    driverStrongInv width h_width z tape (⟨preorder c, [], [], [], false⟩ : DriveState n) := by
  obtain ⟨hce, hco, how, hwe, hev, hvl, hvc, hcl, hcb⟩ := hwf
  refine ⟨⟨hce, hco, how, hwe, hev, hvl, hvc, hcl, hcb⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show windowSpells tape (z.certEnd - (encodePreorder width h_width (preorder c)).length)
      (encodePreorder width h_width (preorder c))
    rw [encodePreorder_preorder]
    have ha : z.certEnd - (encodeCircuitTree width h_width c).length = z.certBase := by omega
    rw [ha]
    exact hcert
  · rw [encodePreorder_preorder]; omega
  · show windowSpells tape (z.workBase - 1 - List.length ([] : List (SLGate n)))
      (unaryField (List.length ([] : List (SLGate n))) ++ encodeGateRecordStream ([] : List (SLGate n)))
    simpa [unaryField, encodeGateRecordStream] using hcount0
  · simp only [List.length_nil]; omega
  · show z.workBase + (encodeGateRecordStream ([] : List (SLGate n))).length ≤ z.workEnd
    simp only [encodeGateRecordStream, List.length_nil]; omega
  · show windowSpells tape (z.valBound - (encodeNatStack1 []).length) (encodeNatStack1 [])
    simpa [encodeNatStack1] using windowSpells_nil tape z.valBound (by omega)
  · simp only [encodeNatStack1, List.length_nil]; omega
  · show windowSpells tape (z.ctrlBound - (encodeCtrlStack1 []).length) (encodeCtrlStack1 [])
    simpa [encodeCtrlStack1] using windowSpells_nil tape z.ctrlBound (by omega)
  · simp only [encodeCtrlStack1, List.length_nil]; omega
  · exact validCertTokens_preorder c
  · intro hs; cases hs

end ContractExpansion
end Frontier
end Pnp4
