import Models.Model_PartialMCSP
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import Tests.CircuitCountTraceBoundProbe

/-!
# General iso-strong no-go probe (L1, sessions 1 and 2 partial)

L1 staging probe consuming the counting bricks landed in
`pnp3/Tests/CircuitCountTraceBoundProbe.lean` and lifting generalised
pigeonhole, slack, and diagonal-encoding bricks towards
`isoStrong_conclusion_negative_general`.

This file is intentionally local to `pnp3/Tests/` and does not modify
endpoints, specs, or trust-root surfaces.  No `axiom` / `opaque` /
`sorry` / `admit` / `native_decide` are introduced.  The remaining
not-YES bridge and final contradiction assembly are staged for a
follow-up L1 session (`open_general_isoStrong_no_go_L1_session_3`).

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

## What session 2 partially lands

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

## What remains for L1 session 3

- A general not-YES bridge analogous to canonical
  `is_consistent_diagonal_table_implies_label_trace` and
  `diagonal_z_not_yes_of_label_not_trace`, generalised from size-1
  candidate consistency to bounded-size circuit consistency via the
  L0 trace-image cardinality bound `boundedSizeTrace_image_card_le`.
- A general composition theorem
  `exists_valid_agreeing_not_yes_under_general_slack`.
- Final assembly into `isoStrong_conclusion_negative_general` over an
  arbitrary `GapSliceFamilyEventually`.
-/

namespace Pnp3
namespace Tests
namespace GeneralIsoStrongNoGoProbe

open Models
open LowerBounds

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

end GeneralIsoStrongNoGoProbe
end Tests
end Pnp3
