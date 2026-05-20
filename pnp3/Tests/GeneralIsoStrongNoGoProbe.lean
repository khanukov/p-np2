import Models.Model_PartialMCSP
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import Tests.CircuitCountTraceBoundProbe

/-!
# General iso-strong no-go probe (L1, sessions 1, 2, and 3)

L1 staging probe consuming the counting bricks landed in
`pnp3/Tests/CircuitCountTraceBoundProbe.lean` and lifting the full
generalised pigeonhole, slack, diagonal-encoding, and not-YES bridge
chain towards `isoStrong_conclusion_negative_general`.

After session 3 all six canonical L1 ingredients have generic
replacements, kernel-checked here.  The only remaining work is the
final route-level assembly into `isoStrong_conclusion_negative_general`
over an arbitrary `GapSliceFamilyEventually`.

This file is intentionally local to `pnp3/Tests/` and does not modify
endpoints, specs, or trust-root surfaces.  No `axiom` / `opaque` /
`sorry` / `admit` / `native_decide` are introduced.

## What session 1 lands

1. `exists_label_not_in_trace_image_of_card_lt` — the parameter-agnostic
   finite-image pigeonhole step: any sub-family `S ⊆ (α → Bool)` of
   cardinality strictly below `2 ^ |α|` misses some Boolean labeling.
   Generic replacement for the canonical L1 session 1 pigeonhole
   `exists_trace_not_size1_of_card_lt`.

2. `slack_for_D_of_isoStrong_slack_general` — converts iso-strong
   slack on the `(tableLen, κ)` axis into the `D.card` form needed by
   the diagonal step, by composing `F.hIndex` / `F.hM` / `F.hT` to
   line up `F.Mof n (F.Tof n β)` with
   `circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1)`,
   then weakening the exponent via `Nat.sub_le_sub_left` and
   `Nat.pow_le_pow_right`.  Generic replacement for the canonical L1
   session 4 `slack_for_D_of_isoStrong_slack`.

## What session 2 lands

3. `generalDiagonalPartialTable` — the general diagonal partial table
   carrying `decodePartial yYes` on fixed coordinates `D` and `label`
   on the free rows.  Generic replacement for canonical
   `diagonalPartialTable`.

4. `general_diagonal_z_valid` — the encoded general diagonal is a
   `ValidEncoding`.  Generic replacement for canonical
   `diagonal_z_valid`.

5. `general_diagonal_z_agrees_on_D` — the encoded general diagonal
   agrees with `yYes` on the fixed coordinates `D` (under
   `ValidEncoding p yYes`).  Generic replacement for canonical
   `diagonal_z_agrees_on_D`.  Closed by the same value-bit calc chain
   used in the canonical proof.

## What session 3 lands

6. `is_consistent_general_diagonal_table_implies_trace_in_image` —
   any bounded-size circuit `C` consistent with the general diagonal
   table satisfies `traceCircuitOnRows ... C = label` on the free
   rows.  Generic replacement for canonical
   `is_consistent_diagonal_table_implies_label_trace`, lifted from
   size-1 candidate consistency to arbitrary bounded-size circuit
   consistency.

7. `general_diagonal_z_not_yes_of_label_not_in_trace_image` — if
   `label` lies outside the bounded-size trace image, then the
   encoded general diagonal cannot be in the YES promise slice.
   Generic replacement for canonical
   `diagonal_z_not_yes_of_label_not_trace`.

8. `exists_valid_agreeing_not_yes_under_general_slack` — the
   final session-3 composition: under the strict trace-cardinality
   slack `circuitCountBound p.n (p.sNO - 1) < 2 ^ |Finset.univ \ D|`,
   there exists `z` that is a `ValidEncoding`, agrees with `yYes`
   on `D`, and is not in the YES promise slice.  Generic replacement
   for canonical `exists_valid_agreeing_not_yes_under_slack`.

## What remains for L1 session 4

- Final route-level assembly
  `isoStrong_conclusion_negative_general (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
    ¬ IsoStrongFamilyEventually F hInDag`,
  composing the per-slice bricks above with `slack_for_D_of_isoStrong_slack_general`
  to thread the eventual κ-slack through `F.hM` / `F.hT`.
-/

namespace Pnp3
namespace Tests
namespace GeneralIsoStrongNoGoProbe

open Models
open LowerBounds
open Counting

/--
Finite-image pigeonhole: any `S : Finset (α → Bool)` of cardinality strictly
below `2 ^ |α|` misses some Boolean labeling `label : α → Bool`.

Parameter-agnostic replacement for the canonical
`exists_trace_not_size1_of_card_lt` (L1 session 1) — operates on an
arbitrary finite trace image, not specifically the size-1 candidate
trace family.
-/
theorem exists_label_not_in_trace_image_of_card_lt
    {α : Type} [Fintype α] [DecidableEq (α → Bool)]
    (S : Finset (α → Bool))
    (h : S.card < 2 ^ Fintype.card α) :
    ∃ label : α → Bool, label ∉ S := by
  classical
  have hCardU : (Finset.univ : Finset (α → Bool)).card = 2 ^ Fintype.card α := by
    simp [Fintype.card_bool]
  have hLt : S.card < (Finset.univ : Finset (α → Bool)).card := by
    simpa [hCardU] using h
  by_contra hNo
  have hAll : ∀ label : α → Bool, label ∈ S := by
    intro label
    by_contra hNotMem
    exact hNo ⟨label, hNotMem⟩
  have hEq : S = (Finset.univ : Finset (α → Bool)) := by
    ext label
    constructor
    · intro _; simp
    · intro _; exact hAll label
  have hNotLt : ¬ S.card < (Finset.univ : Finset (α → Bool)).card := by
    simp [hEq]
  exact hNotLt hLt

/--
Convert iso-strong slack from the `(tableLen, κ)` axis to the `D.card`
form needed by the diagonal step at a general
`GapSliceFamilyEventually`.

Composition:
- `F.hIndex` aligns `(F.paramsOf n β).n` with `n` for `n ≥ F.N0`;
- `F.hM` rewrites `F.Mof n T` to `circuitCountBound n T`;
- `F.hT` rewrites `F.Tof n β` to `(F.paramsOf n β).sNO - 1`;
- monotonicity of `Nat.sub` and `Nat.pow` weakens the `κv` exponent
  to the `D.card` exponent via `D.card ≤ κv`.

Parameter-agnostic replacement for the canonical L1 session 4
`slack_for_D_of_isoStrong_slack`.
-/
theorem slack_for_D_of_isoStrong_slack_general
    (F : GapSliceFamilyEventually)
    (n : Nat) (β : Rat)
    (hn : F.N0 ≤ n)
    (D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)))
    (κv : Nat)
    (hDcard : D.card ≤ κv)
    (hRawSlack :
      F.Mof n (F.Tof n β) <
        2 ^ (GapSliceFamilyEventually.tableLen F n β - κv)) :
    circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) <
      2 ^ (Partial.tableLen (F.paramsOf n β).n - D.card) := by
  have hRaw' :
      circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1)
        < 2 ^ (GapSliceFamilyEventually.tableLen F n β - κv) := by
    have hIdx : (F.paramsOf n β).n = n := F.hIndex n hn β
    have hM := F.hM n hn ((F.paramsOf n β).sNO - 1)
    have hT := F.hT n hn β
    simpa [hIdx, hM, hT] using hRawSlack
  have hExpLe : GapSliceFamilyEventually.tableLen F n β - κv ≤
      GapSliceFamilyEventually.tableLen F n β - D.card :=
    Nat.sub_le_sub_left hDcard _
  have hPowLe : 2 ^ (GapSliceFamilyEventually.tableLen F n β - κv) ≤
      2 ^ (GapSliceFamilyEventually.tableLen F n β - D.card) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hExpLe
  have hLt' := lt_of_lt_of_le hRaw' hPowLe
  simpa [GapSliceFamilyEventually.tableLen] using hLt'

/--
General diagonal partial table over an arbitrary bounded-size trace family:
copy `yYes` on fixed rows `D`, and use `label` on free rows.
-/
def generalDiagonalPartialTable
    (p : GapPartialMCSPParams)
    (yYes : Core.BitVec (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \ D).attach → Bool) :
    PartialTruthTable p.n :=
  fun j =>
    if hD : j ∈ D then
      decodePartial yYes j
    else
      some (label ⟨⟨j, by
        refine Finset.mem_sdiff.mpr ?_
        exact ⟨Finset.mem_univ j, hD⟩⟩, by simp⟩)

theorem general_diagonal_z_valid
    (p : GapPartialMCSPParams)
    (yYes : Core.BitVec (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \ D).attach → Bool) :
    ValidEncoding p (encodePartial (generalDiagonalPartialTable p yYes D label)) := by
  exact validEncoding_encodePartial p _

/--
General version of canonical `diagonal_z_agrees_on_D`: the encoded
diagonal agrees with the YES witness `yYes` on every fixed coordinate
`i ∈ D`, under `ValidEncoding p yYes`.

Proof structure follows the canonical value-bit calc chain:
- on `D`, the diagonal table equals `decodePartial yYes`;
- `Partial.valPart` is invariant under canonical `encodePartial`
  / `decodePartial` round-trips, so both sides reduce to
  `(decodePartial yYes i).getD false`.
-/
theorem general_diagonal_z_agrees_on_D
    (p : GapPartialMCSPParams)
    (yYes : Core.BitVec (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \ D).attach → Bool) :
    AgreeOnValues D yYes
      (encodePartial (generalDiagonalPartialTable p yYes D label)) := by
  intro i hi
  -- Canonicality of `yYes` on valid encodings.
  have hy : yYes = encodePartial (decodePartial yYes) := hValidYes
  -- The diagonal table copies `decodePartial yYes` on all points of `D`.
  have hdiag :
      generalDiagonalPartialTable p yYes D label i = decodePartial yYes i := by
    simp [generalDiagonalPartialTable, hi]
  -- Compare value-bits through the canonical encoding.
  calc
    Partial.valPart yYes i
        = Partial.valPart (encodePartial (decodePartial yYes)) i := by
      exact congrArg (fun s => Partial.valPart s i) hy
    _ = (decodePartial yYes i).getD false := by
      simp [Partial.valPart, encodePartial, Partial.valIndex]
    _ = (generalDiagonalPartialTable p yYes D label i).getD false := by
      rw [hdiag]
    _ = Partial.valPart
        (encodePartial (generalDiagonalPartialTable p yYes D label)) i := by
      symm
      simp [Partial.valPart, encodePartial, Partial.valIndex]

/--
General version of canonical `is_consistent_diagonal_table_implies_label_trace`:
any bounded-size circuit `C` consistent with the general diagonal table
satisfies `traceCircuitOnRows ... C = label` on the free rows.

Lifted from canonical size-1 candidate consistency to arbitrary
bounded-size circuit consistency.  The `_hSize` argument is retained
in the signature for downstream consumers (used by
`general_diagonal_z_not_yes_of_label_not_in_trace_image`) but is not
needed for the trace-equality conclusion at this layer.
-/
theorem is_consistent_general_diagonal_table_implies_trace_in_image
    (p : GapPartialMCSPParams)
    (yYes : Core.BitVec (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \ D).attach → Bool)
    (C : Circuit p.n)
    (_hSize : C.size ≤ p.sYES)
    (hCons :
      is_consistent C
        (generalDiagonalPartialTable p yYes D label)) :
    CircuitCountTraceBoundProbe.traceCircuitOnRows
      ((Finset.univ \ D).attach)
      (fun a => a.1)
      C
    =
    label := by
  funext a
  have hdiag : generalDiagonalPartialTable p yYes D label a.1 = some (label a) := by
    have hNotMem : a.1.1 ∉ D := by
      exact (Finset.mem_sdiff.mp a.1.2).2
    simp [generalDiagonalPartialTable, hNotMem]
  have hAt := hCons (Core.vecOfNat p.n a.1.1.val)
  have hIdx : assignmentIndex (Core.vecOfNat p.n a.1.1.val) = a.1.1 := by
    exact assignmentIndex_vecOfNat_eq a.1.1
  rw [hIdx, hdiag] at hAt
  simpa [CircuitCountTraceBoundProbe.traceCircuitOnRows] using hAt

/--
General not-YES bridge: if `label` is not in the bounded-size trace
image, the encoded general diagonal cannot be in the YES promise
slice.

Generic replacement for canonical `diagonal_z_not_yes_of_label_not_trace`.
Proof unpacks YES-membership via `gapPartialMCSP_language_true_iff_yes`
(direct API, avoiding the heavier `gapSlice_yes_iff` route which can
trigger `whnf` blow-ups under this file's import surface), pulls out
the bounded-size circuit witness `C`, converts consistency-on-decoded
to consistency-on-table via `decodePartial_encodePartial`, applies the
trace-equality lemma `is_consistent_general_diagonal_table_implies_trace_in_image`,
and contradicts `hLabel` by exhibiting `label` in the trace image
through `C`.
-/
theorem general_diagonal_z_not_yes_of_label_not_in_trace_image
    (p : GapPartialMCSPParams)
    (yYes : Core.BitVec (partialInputLen p))
    (D : Finset (Fin (Partial.tableLen p.n)))
    (label : (Finset.univ \ D).attach → Bool)
    (hLabel :
      label ∉
        (Counting.circuitsOfSizeAtMost p.n p.sYES).image
          (CircuitCountTraceBoundProbe.traceCircuitOnRows
            ((Finset.univ \ D).attach)
            (fun a => a.1))) :
    ¬ encodePartial (generalDiagonalPartialTable p yYes D label)
        ∈ (gapSliceOfParams p).Yes := by
  intro hzYes
  have hLang :
      gapPartialMCSP_Language p
        (partialInputLen p)
        (encodePartial (generalDiagonalPartialTable p yYes D label)) = true := hzYes
  have hYes :
      ∃ (C : Circuit p.n), C.size ≤ p.sYES ∧
        is_consistent C (decodePartial (encodePartial (generalDiagonalPartialTable p yYes D label))) := by
    exact (gapPartialMCSP_language_true_iff_yes p
      (encodePartial (generalDiagonalPartialTable p yYes D label))).1 hLang
  rcases hYes with ⟨C, hSize, hCons⟩
  have hTable : is_consistent C (generalDiagonalPartialTable p yYes D label) := by
    simpa [decodePartial_encodePartial] using hCons
  have hTrace :
      CircuitCountTraceBoundProbe.traceCircuitOnRows
        ((Finset.univ \ D).attach)
        (fun a => a.1)
        C
      =
      label :=
    is_consistent_general_diagonal_table_implies_trace_in_image
      p yYes D label C hSize hTable
  have hMemC : C ∈ Counting.circuitsOfSizeAtMost p.n p.sYES := by
    exact Counting.mem_circuitsOfSizeAtMost C p.sYES hSize
  have hInImage :
      label ∈
        (Counting.circuitsOfSizeAtMost p.n p.sYES).image
          (CircuitCountTraceBoundProbe.traceCircuitOnRows
            ((Finset.univ \ D).attach)
            (fun a => a.1)) := by
    refine Finset.mem_image.mpr ?_
    exact ⟨C, hMemC, hTrace⟩
  exact hLabel hInImage

/--
The session-3 final composition.  Under the strict trace-cardinality
slack `circuitCountBound p.n (p.sNO - 1) < 2 ^ |Finset.univ \ D|`,
there exists a partial-encoding `z` that is

- a `ValidEncoding`;
- agrees with `yYes` on the fixed coordinates `D`; and
- is not in the YES promise slice.

Generic replacement for canonical `exists_valid_agreeing_not_yes_under_slack`.

Proof: bound the cardinality of the bounded-size trace image via
`boundedSizeTrace_image_card_lt_of_slack` (L0 brick), invoke
`exists_label_not_in_trace_image_of_card_lt` (session-1 pigeonhole)
to pick a `label` outside the image, and assemble the diagonal `z`
from `generalDiagonalPartialTable` together with the three witnesses
(`general_diagonal_z_valid`, `general_diagonal_z_agrees_on_D`,
`general_diagonal_z_not_yes_of_label_not_in_trace_image`).

This closes the six-of-six generic ingredient set required for the
final route-level theorem `isoStrong_conclusion_negative_general`
(staged for L1 session 4).
-/
theorem exists_valid_agreeing_not_yes_under_general_slack
    (p : GapPartialMCSPParams)
    (yYes : Core.BitVec (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack :
      circuitCountBound p.n (p.sNO - 1) <
        2 ^ ((Finset.univ \ D).card)) :
    ∃ z : Core.BitVec (partialInputLen p),
      ValidEncoding p z ∧
      AgreeOnValues D yYes z ∧
      ¬ z ∈ (gapSliceOfParams p).Yes := by
  let S :
      Finset ((Finset.univ \ D).attach → Bool) :=
    (Counting.circuitsOfSizeAtMost p.n p.sYES).image
      (CircuitCountTraceBoundProbe.traceCircuitOnRows
        ((Finset.univ \ D).attach)
        (fun a => a.1))
  have hCardLtRaw :
      S.card < 2 ^ ((Finset.univ \ D).card) := by
    simpa [S] using
      CircuitCountTraceBoundProbe.boundedSizeTrace_image_card_lt_of_slack p D hSlack
  have hCardLt : S.card < 2 ^ (Partial.tableLen p.n - D.card) := by
    simpa [Finset.card_sdiff (Finset.subset_univ D)] using hCardLtRaw
  rcases exists_label_not_in_trace_image_of_card_lt S (by simpa using hCardLt) with ⟨label, hLabel⟩
  refine ⟨encodePartial (generalDiagonalPartialTable p yYes D label), ?_, ?_, ?_⟩
  · exact general_diagonal_z_valid p yYes D label
  · exact general_diagonal_z_agrees_on_D p yYes hValidYes D label
  · exact general_diagonal_z_not_yes_of_label_not_in_trace_image p yYes D label hLabel

lemma correctOnPromiseSlice_of_InPpolyDAG_family_general
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n β,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β)))
    (n : Nat) (β : Rat) :
    CorrectOnPromiseSlice
      ((hInDag n β).family (GapSliceFamilyEventually.encodedLen F n β))
      (gapSliceOfParams (F.paramsOf n β)) := by
  constructor
  · intro x hx
    have hCorr := (hInDag n β).correct
      (GapSliceFamilyEventually.encodedLen F n β) x
    exact hx ▸ hCorr
  · intro x hx
    have hCorr := (hInDag n β).correct
      (GapSliceFamilyEventually.encodedLen F n β) x
    exact hx ▸ hCorr

theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag :
      ∀ n β,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language (F.paramsOf n β))) :
    ¬ IsoStrongFamilyEventually F hInDag := by
  intro hIso
  rcases hIso with ⟨β0, hβ0, κ, nIso, hForce, hSlack⟩
  let β : Rat := β0 / 2
  have hβPos : 0 < β := by
    dsimp [β]
    exact div_pos hβ0 (by norm_num)
  have hβLt : β < β0 := by
    dsimp [β]
    linarith
  let n : Nat := max F.N0 (nIso β)
  have hn : n ≥ max F.N0 (nIso β) := by exact le_rfl
  have hn0 : F.N0 ≤ n := by exact le_max_left _ _
  let p := F.paramsOf n β
  let C : ComplexityInterfaces.DagCircuit (GapSliceFamilyEventually.encodedLen F n β) :=
    (hInDag n β).family (GapSliceFamilyEventually.encodedLen F n β)
  have hSize :
      ppolyDAGSizeBoundOnSlicesEventually F hInDag n β 1
        (ComplexityInterfaces.DagCircuit.size C) := by
    simpa [C, ppolyDAGSizeBoundOnSlicesEventually] using
      (hInDag n β).family_size_le (GapSliceFamilyEventually.encodedLen F n β)
  have hCorrect : CorrectOnPromiseSlice C (gapSliceOfParams p) := by
    simpa [C, p] using
      correctOnPromiseSlice_of_InPpolyDAG_family_general F hInDag n β
  rcases hForce n β hβPos hβLt hn C hSize hCorrect with
    ⟨yYes, hyYes, hValidYes, D, hDcard, hAllYes⟩
  have hRawSlack := hSlack n β hβPos hβLt hn
  have hSlackForD :
      circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) <
        2 ^ (Partial.tableLen (F.paramsOf n β).n - D.card) := by
    exact slack_for_D_of_isoStrong_slack_general
      F n β hn0 D (κ n β) hDcard hRawSlack
  have hSlackForD' :
      circuitCountBound p.n (p.sNO - 1) <
        2 ^ ((Finset.univ \ D).card) := by
    simpa [p, Finset.card_sdiff (Finset.subset_univ D)] using hSlackForD
  rcases exists_valid_agreeing_not_yes_under_general_slack
      p yYes hValidYes D hSlackForD' with
    ⟨z, hzValid, hzAgree, hzNotYes⟩
  exact hzNotYes (hAllYes z hzValid hzAgree)

end GeneralIsoStrongNoGoProbe
end Tests
end Pnp3
