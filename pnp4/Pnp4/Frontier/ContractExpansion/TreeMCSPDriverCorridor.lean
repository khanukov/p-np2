import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverStrongInv

/-!
# `driverCorridorInv` — D2t-5b (Block A3): the corridor layout (no hop crosses WORK)

`driverStrongInv` (A1) fixed the contents/geometry story but kept the certificate **left** of the
working regions — under which the reading arms' head hops (cursor → control stack, cursor → WORK
frontier) would have to cross the heterogeneous, growing WORK region, where no `Bool`-tape scan can
land deterministically.  This module revises the layout so that **every hop of every driver arm is a
scan over a guaranteed-all-`0` corridor onto a guaranteed-`1` anchor**:

```
[ input | COUNT← 0 | WORK→ FM | …0…  VAL→ | …0… CTRL→ | …0… M | cert-suffix → certEnd ]
```

* the **certificate sits rightmost**; the cursor advances rightward, the consumed prefix is kept
  zeroed except a single **cursor marker** `M` at `cursor − 1` (the hop *to* the cursor is a rightward
  0-scan onto `M`; the consumed-prefix zeros merge with the dead zone left of `certBase`);
* the stacks live in fixed zones **between WORK and the certificate**, stored **right-anchored**
  (`encodeNatStackR` / `encodeCtrlStackR`): the **top is the rightmost field** and every field's
  rightmost cell is a `1`, so a leftward 0-scan from `M` (or from a stack's left content edge) lands
  exactly on the next stack's top; each stack carries a permanent **base sentinel `1`** at its base
  cell, so the same scan is sound when the stack is empty — and "control stack empty" (the A1b sink
  test) becomes *land on a `1`, peek one cell left: a `0` means the base sentinel* (frame tag blocks
  carry **`tagCode + 2 ≥ 2` ones**, frame remaining-count blocks **`rem + 1 ≥ 2` ones**, and value
  blocks **`v + 2 ≥ 2` ones**, so during a zone walk no block edge is ever confused with the
  single-`1` sentinel);
* the **WORK frontier marker** `FM` is a single `1` just past the last record: the hop val → frontier
  is a leftward 0-scan onto `FM`; a record append overwrites `FM` and re-plants it at the new
  frontier.  Inside a record, the A2 transfer's home delimiters come for free: every operand field is
  preceded by the previous field's `0` terminator;
* the **COUNT/WORK output window is unchanged from A1** (it spells `encodeGateStream st.out`, the
  D2t-6a in-band count prefix).

The value/control clauses of `driverStrongInv` are therefore **superseded** by the corridor forms
below (`driverStrongInv` itself remains valid for its merged uses; nothing machine-level consumed its
stack clauses yet — A2's transfer loop is layout-generic).

**Progress classification (AGENTS.md): Infrastructure** — a tape-layout invariant revision proven
against the verified codecs; builds no machine and proves no separation.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### Right-anchored (corridor) stack codecs -/

/-- A right-anchored value entry: `[0] ++ 1^(v+2)` — the left `0` delimits, the field is read
right-to-left, and the **rightmost cell is a `1`** (the scan anchor), index `0` included.  The block
carries `v + 2 ≥ 2` ones so that during a zone walk a value field is never confused with the
**single-`1` base sentinel** (the same `≥ 2` discipline as the control frames' tag blocks). -/
def encodeNatEntryR (v : Nat) : List Bool :=
  false :: List.replicate (v + 2) true

@[simp] theorem encodeNatEntryR_length (v : Nat) : (encodeNatEntryR v).length = v + 3 := by
  simp [encodeNatEntryR]

/-- The right-anchored value stack: a permanent base sentinel `1` at the base cell, then the entries
bottom-to-top **left-to-right** (the head of the list — the top — is written last/rightmost).  Defined
by a single linear pass (`reverse` + `flatMap`, O(output)); the geometric push equation
`encodeNatStackR (v :: S) = encodeNatStackR S ++ encodeNatEntryR v` is the simp lemma below. -/
def encodeNatStackR (S : List Nat) : List Bool :=
  true :: S.reverse.flatMap encodeNatEntryR

@[simp] theorem encodeNatStackR_nil : encodeNatStackR [] = [true] := rfl

@[simp] theorem encodeNatStackR_cons (v : Nat) (rest : List Nat) :
    encodeNatStackR (v :: rest) = encodeNatStackR rest ++ encodeNatEntryR v := by
  unfold encodeNatStackR
  rw [List.reverse_cons, List.flatMap_append]
  simp

/-- The encoded right-anchored value stack always ends in a `1` (the scan anchor): the base sentinel
when empty, the top entry's last unit otherwise. -/
theorem encodeNatStackR_getLast_true (S : List Nat) :
    (encodeNatStackR S).getLast? = some true := by
  cases S with
  | nil => rfl
  | cons v rest =>
      rw [encodeNatStackR_cons, List.getLast?_append_of_ne_nil]
      · show (encodeNatEntryR v).getLast? = some true
        rw [show encodeNatEntryR v = [false] ++ List.replicate (v + 2) true from rfl]
        rw [List.getLast?_append_of_ne_nil]
        · rw [List.getLast?_replicate]
          simp
        · simp
      · simp [encodeNatEntryR]

/-- Exact length of the right-anchored value stack: `1 + Σ (vᵢ + 3)`. -/
theorem encodeNatStackR_length (S : List Nat) :
    (encodeNatStackR S).length = 1 + (S.map (· + 3)).sum := by
  induction S with
  | nil => rfl
  | cons v rest ih => rw [encodeNatStackR_cons]; simp [encodeNatEntryR, ih]; omega

/-- A right-anchored control frame: `[0] ++ 1^(rem+1) ++ [0] ++ 1^(tagCode+2)` — read right-to-left:
the tag block, a `0` separator, the remaining-count block, the left `0` delimiter.  **Both** blocks
carry `≥ 2` ones (`tagCode + 2 ≥ 2`; `rem + 1 ≥ 2` since reachable `rem ≥ 1`), so during a zone walk
*neither* edge of a frame is ever confused with the single-`1` base sentinel — the `rem` block with
`rem = 1` (every `tnot` frame; `tand`/`tor` before the pop) would otherwise be a bare `1` and stop the
walker mid-zone. -/
def encodeCtrlFrameR : ITag × Nat → List Bool
  | (tag, rem) =>
      false :: (List.replicate (rem + 1) true ++ (false :: List.replicate (tag.tagCode + 2) true))

@[simp] theorem encodeCtrlFrameR_length (tag : ITag) (rem : Nat) :
    (encodeCtrlFrameR (tag, rem)).length = rem + tag.tagCode + 5 := by
  simp [encodeCtrlFrameR]; omega

/-- The right-anchored control stack: base sentinel `1`, then the frames bottom-to-top left-to-right
(the top frame rightmost).  Linear-pass definition; the push equation is the simp lemma below. -/
def encodeCtrlStackR (S : List (ITag × Nat)) : List Bool :=
  true :: S.reverse.flatMap encodeCtrlFrameR

@[simp] theorem encodeCtrlStackR_nil : encodeCtrlStackR [] = [true] := rfl

@[simp] theorem encodeCtrlStackR_cons (f : ITag × Nat) (rest : List (ITag × Nat)) :
    encodeCtrlStackR (f :: rest) = encodeCtrlStackR rest ++ encodeCtrlFrameR f := by
  unfold encodeCtrlStackR
  rw [List.reverse_cons, List.flatMap_append]
  simp

/-- The encoded right-anchored control stack always ends in a `1` (the scan anchor). -/
theorem encodeCtrlStackR_getLast_true (S : List (ITag × Nat)) :
    (encodeCtrlStackR S).getLast? = some true := by
  cases S with
  | nil => rfl
  | cons f rest =>
      obtain ⟨tag, rem⟩ := f
      rw [encodeCtrlStackR_cons, List.getLast?_append_of_ne_nil]
      · show (encodeCtrlFrameR (tag, rem)).getLast? = some true
        rw [show encodeCtrlFrameR (tag, rem)
            = ([false] ++ List.replicate (rem + 1) true)
              ++ ([false] ++ List.replicate (tag.tagCode + 2) true)
            from by simp [encodeCtrlFrameR]]
        rw [List.getLast?_append_of_ne_nil]
        · rw [List.getLast?_append_of_ne_nil]
          · rw [List.getLast?_replicate]
            simp
          · simp
        · simp
      · simp [encodeCtrlFrameR]

/-! ### The corridor zones and the revised strong invariant -/

/-- Fixed zone bounds of the corridor layout
`[ input | COUNT← 0 | WORK→ FM | VAL→ | CTRL→ | M | certificate → ]` — the certificate rightmost, the
stacks (right-anchored, in fixed zones) between WORK and the certificate. -/
structure DriverCorridor where
  outBase : Nat
  workBase : Nat
  workEnd : Nat
  valBase : Nat
  valEnd : Nat
  ctrlBase : Nat
  ctrlEnd : Nat
  certBase : Nat
  certEnd : Nat

/-- Corridor zone-chain well-formedness: `outBase < workBase < workEnd < valBase < valEnd < ctrlBase <
ctrlEnd ∧ ctrlEnd + 1 < certBase ≤ certEnd ≤ L`.  The **strict** inter-zone links guarantee at least
one dead `0` cell between any zone's content capacity and the next zone's content (and between the
control zone and the cursor-marker slot `certBase − 1`) — so every inter-zone hop scan starts on a
guaranteed-dead cell, with no zero-gap edge cases.  (`outBase < workBase` keeps the count terminator
cell; `workBase < workEnd` the frontier marker even with empty WORK.) -/
def DriverCorridor.WellFormed (z : DriverCorridor) (L : Nat) : Prop :=
  z.outBase < z.workBase ∧ z.workBase < z.workEnd ∧ z.workEnd < z.valBase ∧ z.valBase < z.valEnd
    ∧ z.valEnd < z.ctrlBase ∧ z.ctrlBase < z.ctrlEnd ∧ z.ctrlEnd + 1 < z.certBase
    ∧ z.certBase ≤ z.certEnd ∧ z.certEnd ≤ L

/-- **The corridor strong invariant.**  Live anchors derived from the abstract state (`cursor :=
certEnd − |enc toks|`); every inter-region corridor is pinned all-`0` and every landing anchor is a
pinned `1`:

* certificate suffix at the cursor + the **cursor marker** `1` at `cursor − 1` + consumed/dead zeros
  from the control stack's content end up to the marker;
* output window `encodeGateStream st.out` (count + records, as A1) + the **frontier marker** `1` just
  past the records + zeros from past the marker up to the value zone;
* right-anchored stack windows at their fixed bases + zeros between the stacks' content ends and the
  next zone;
* `ValidCertTokens` + the settling/value coherence clause (as A1). -/
def driverCorridorInv {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (tape : Fin L → Bool) (st : DriveState n) : Prop :=
  z.WellFormed L
  -- certificate: unread suffix ends at certEnd; cursor marker; cursor stays right of certBase − 1
  ∧ windowSpells tape (z.certEnd - (encodePreorder width h_width st.toks).length)
      (encodePreorder width h_width st.toks)
  ∧ z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd
  ∧ (∀ p : Fin L,
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 → tape p = true)
  -- consumed/dead corridor: from the control content end to the cursor marker, all 0
  ∧ (∀ p : Fin L,
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 → tape p = false)
  -- output: encodeGateStream window (count + records) + frontier marker + dead corridor to VAL
  ∧ windowSpells tape (z.workBase - 1 - st.out.length)
      (unaryField st.out.length ++ encodeGateRecordStream st.out)
  ∧ z.outBase + st.out.length + 1 ≤ z.workBase
  ∧ (∀ p : Fin L,
      (p : Nat) = z.workBase + (encodeGateRecordStream st.out).length → tape p = true)
  ∧ z.workBase + (encodeGateRecordStream st.out).length + 1 ≤ z.workEnd
  ∧ (∀ p : Fin L,
      z.workBase + (encodeGateRecordStream st.out).length + 1 ≤ (p : Nat) →
      (p : Nat) < z.valBase → tape p = false)
  -- value stack: right-anchored window at its fixed base + dead corridor to CTRL
  ∧ windowSpells tape z.valBase (encodeNatStackR st.val)
  ∧ z.valBase + (encodeNatStackR st.val).length ≤ z.valEnd
  ∧ (∀ p : Fin L,
      z.valBase + (encodeNatStackR st.val).length ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → tape p = false)
  -- control stack: right-anchored window at its fixed base
  ∧ windowSpells tape z.ctrlBase (encodeCtrlStackR st.ctrl)
  ∧ z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd
  -- validity + cheap coherence (as A1)
  ∧ ValidCertTokens st.toks
  ∧ (st.settling = true → st.val ≠ [])

/-- **The corridor invariant holds at the start.**  Hypotheses: the zone chain; the certificate laid
out at `certBase` ending at `certEnd`; the initial cursor marker at `certBase − 1`; the count
terminator cell; the frontier marker at `workBase`; the two stack base sentinels; and the three dead
corridors zeroed.  The certificate clause is `encodePreorder_preorder`; validity is
`validCertTokens_preorder`. -/
theorem driverCorridorInv_init {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (tape : Fin L → Bool) (c : CircuitTree n)
    (hwf : z.WellFormed L)
    (hcert : windowSpells tape z.certBase (encodeCircuitTree width h_width c))
    (hlen : z.certBase + (encodeCircuitTree width h_width c).length = z.certEnd)
    (hM : ∀ p : Fin L, (p : Nat) = z.certBase - 1 → tape p = true)
    (hcount0 : windowSpells tape (z.workBase - 1) [false])
    (hFM : ∀ p : Fin L, (p : Nat) = z.workBase → tape p = true)
    (hvalS : windowSpells tape z.valBase [true])
    (hctrlS : windowSpells tape z.ctrlBase [true])
    (hdead1 : ∀ p : Fin L, z.workBase + 1 ≤ (p : Nat) → (p : Nat) < z.valBase → tape p = false)
    (hdead2 : ∀ p : Fin L, z.valBase + 1 ≤ (p : Nat) → (p : Nat) < z.ctrlBase → tape p = false)
    (hdead3 : ∀ p : Fin L, z.ctrlBase + 1 ≤ (p : Nat) → (p : Nat) < z.certBase - 1 → tape p = false) :
    driverCorridorInv width h_width z tape (⟨preorder c, [], [], [], false⟩ : DriveState n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hwf
  have hcur : z.certEnd - (encodePreorder width h_width (preorder c)).length = z.certBase := by
    rw [encodePreorder_preorder]; omega
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · show windowSpells tape (z.certEnd - (encodePreorder width h_width (preorder c)).length)
      (encodePreorder width h_width (preorder c))
    rw [hcur, encodePreorder_preorder]
    exact hcert
  · rw [encodePreorder_preorder]; omega
  · intro p hp
    rw [hcur] at hp
    exact hM p hp
  · intro p hp1 hp2
    rw [hcur] at hp2
    simp only [encodeCtrlStackR_nil, List.length_singleton] at hp1
    exact hdead3 p (by omega) (by omega)
  · show windowSpells tape (z.workBase - 1 - List.length ([] : List (SLGate n)))
      (unaryField (List.length ([] : List (SLGate n))) ++ encodeGateRecordStream ([] : List (SLGate n)))
    simpa [unaryField, encodeGateRecordStream] using hcount0
  · simp only [List.length_nil]; omega
  · intro p hp
    simp only [encodeGateRecordStream, List.length_nil, Nat.add_zero] at hp
    exact hFM p hp
  · simp only [encodeGateRecordStream, List.length_nil]; omega
  · intro p hp1 hp2
    simp only [encodeGateRecordStream, List.length_nil, Nat.add_zero] at hp1
    exact hdead1 p hp1 hp2
  · show windowSpells tape z.valBase (encodeNatStackR [])
    simpa using hvalS
  · simp only [encodeNatStackR_nil, List.length_singleton]; omega
  · intro p hp1 hp2
    simp only [encodeNatStackR_nil, List.length_singleton] at hp1
    exact hdead2 p hp1 hp2
  · show windowSpells tape z.ctrlBase (encodeCtrlStackR [])
    simpa using hctrlS
  · simp only [encodeCtrlStackR_nil, List.length_singleton]; omega
  · exact validCertTokens_preorder c
  · intro hs; cases hs

end ContractExpansion
end Frontier
end Pnp4
