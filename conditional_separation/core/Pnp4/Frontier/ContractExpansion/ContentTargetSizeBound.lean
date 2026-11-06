import Pnp4.Frontier.ContractExpansion.ContentParseFieldRecovery
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-!
# Accepted content has a polynomially bounded target — FEAS-0

This module closes outcome (a) of `VERIFIER_RETARGET_PLAN.md` §1.0 for the concrete
`treeCircuitWitnessCodec (thresholdPoly k)`.  The proof works at the target `r := pr.2.n`
returned by the narrow parser.  Its only comparison with the content header `n_header` is

`treeMCSPPrefixM codec r = treeMCSPPrefixM codec n_header`,

obtained from the parser's surviving length gate.  In particular, no injectivity or gamma
canonicity result is imported or used.

In the wide case, the witness window is blank.  The concrete decoder then fails at `r = 0` and,
at positive `r`, decodes exactly the projection circuit `Circuit.input 0`.  Evaluating that
circuit on the all-true assignment forces the last truth-table cell to be true.  Parser field
recovery locates that cell in the physical word, proving `tableLen r ≤ N`.  The existing
`PolyBoundedInTable` / `powAdd` chain then supplies the advertised polynomial bound.

**Progress classification (AGENTS.md): Infrastructure.**  This is a feasibility bound for the
content-verifier specification.  It builds no verifier machine, proves no lower bound, reduces
neither `VerifiedNPDAGLowerBoundSource` nor `SearchMCSPWeakLowerBound`, and carries no `P ≠ NP`
claim.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

private theorem decodeFin_replicate_false (width : Nat) :
    decodeFin width (List.replicate width false) = some ⟨0, by simp⟩ := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [List.replicate_succ, decodeFin, ih, Bool.false_eq_true, ↓reduceIte]

private theorem thresholdPoly_pos (k r : Nat) : 0 < thresholdPoly k r := by
  unfold thresholdPoly
  by_cases hk : k = 0
  · subst k
    simp
  · have : 0 < k := Nat.pos_of_ne_zero hk
    omega

private theorem tableLen_pos (r : Nat) : 0 < Pnp3.Models.Partial.tableLen r := by
  simp [Pnp3.Models.Partial.tableLen]

private theorem blank_width_covers_payload (k r : Nat) :
    3 + bitLength r ≤
      (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits r := by
  change 3 + bitLength r ≤ (bitLength r + 4) * thresholdPoly k r
  have hT := thresholdPoly_pos k r
  nlinarith

/-- The concrete fixed-width decoder rejects an all-blank witness at target zero. -/
theorem treeCircuitWitnessCodec_decode_blank_zero (k : Nat) :
    (treeCircuitWitnessCodec (thresholdPoly k)).decode 0
        (fun _ => false) = none := by
  let L := (bitLength 0 + 4) * thresholdPoly k 0
  have hcover : 3 + bitLength 0 ≤ L := by
    simpa [L, treeCircuitWitnessCodec, treeSelfDelimitingCode] using
      blank_width_covers_payload k 0
  have hrep : List.replicate L false =
      false :: false :: false :: List.replicate (L - 3) false := by
    rw [show L = 3 + (L - 3) by omega, List.replicate_add]
    simp
  have hsucc : L = (L - 1) + 1 := by omega
  have hrest : L - 1 - 2 = L - 3 := by omega
  have hwidth : bitLength 0 ≤ L - 3 := by omega
  simp only [treeCircuitWitnessCodec, treeSelfDelimitingCode,
    SelfDelimitingCircuitCode.toCodec, List.ofFn_const]
  unfold decodeCircuitFull decodeCircuit
  simp only [List.length_replicate]
  change Option.map Prod.fst
      (Option.map (fun p => (fromTree p.1, p.2))
        (decodeCircuitTreeAtDepth 0 (bitLength 0) L (List.replicate L false))) = none
  rw [hrep, hsucc]
  simp [decodeCircuitTreeAtDepth, List.take_replicate, hrest, hwidth,
    decodeFin_replicate_false]

/-- At a positive target, the concrete fixed-width decoder reads an all-blank witness as the
input-zero projection circuit.  This is the codec-specific fact that makes FEAS-0 true; no
codec-generic analogue is asserted. -/
theorem treeCircuitWitnessCodec_decode_blank_pos (k : Nat) {r : Nat} (hr : 0 < r) :
    (treeCircuitWitnessCodec (thresholdPoly k)).decode r
        (fun _ => false) = some (Pnp3.Models.Circuit.input ⟨0, hr⟩) := by
  let L := (bitLength r + 4) * thresholdPoly k r
  have hcover : 3 + bitLength r ≤ L := by
    simpa [L, treeCircuitWitnessCodec, treeSelfDelimitingCode] using
      blank_width_covers_payload k r
  have hrep : List.replicate L false =
      false :: false :: false :: List.replicate (L - 3) false := by
    rw [show L = 3 + (L - 3) by omega, List.replicate_add]
    simp
  have hsucc : L = (L - 1) + 1 := by omega
  have hrest : L - 1 - 2 = L - 3 := by omega
  have hwidth : bitLength r ≤ L - 3 := by omega
  simp only [treeCircuitWitnessCodec, treeSelfDelimitingCode,
    SelfDelimitingCircuitCode.toCodec, List.ofFn_const]
  unfold decodeCircuitFull decodeCircuit
  simp only [List.length_replicate]
  change Option.map Prod.fst
      (Option.map (fun p => (fromTree p.1, p.2))
        (decodeCircuitTreeAtDepth r (bitLength r) L (List.replicate L false))) =
      some (Pnp3.Models.Circuit.input ⟨0, hr⟩)
  rw [hrep, hsucc]
  simp [decodeCircuitTreeAtDepth, List.take_replicate, hrest, hwidth,
    decodeFin_replicate_false, hr, fromTree]

/-! ## The input-zero truth-table forcing argument -/

/-- The all-true `n`-bit vector is the last truth-table assignment in the repository's
little-endian convention. -/
theorem bitVecToNat_all_true (n : Nat) :
    Pnp3.Models.bitVecToNat (fun _ : Fin n => true) = 2 ^ n - 1 := by
  induction n with
  | zero => simp [Pnp3.Models.bitVecToNat]
  | succ n ih =>
      rw [Pnp3.Models.bitVecToNat_succ]
      simp only [if_pos, ih]
      rw [pow_succ]
      have hpow : 0 < 2 ^ n := pow_pos (by omega) n
      omega

/-- If the input-zero projection computes a truth table, its last cell is true. -/
theorem input_zero_computes_forces_last_true {r : Nat} (hr : 0 < r)
    (tt : TruthTable r)
    (hcomputes : ComputesTruthTable treeCircuitClass
      (Pnp3.Models.Circuit.input ⟨0, hr⟩) tt) :
    tt ⟨Pnp3.Models.Partial.tableLen r - 1, by
      have := tableLen_pos r
      omega⟩ = true := by
  let allTrue : AlgorithmsToLowerBounds.BitVec r := fun _ => true
  have h := hcomputes allTrue
  have htable : 0 < Pnp3.Models.Partial.tableLen r :=
    tableLen_pos r
  have hlast : Pnp3.Models.Partial.tableLen r - 1 <
      Pnp3.Models.Partial.tableLen r := by omega
  change true = Pnp3.Models.truthTableFunction tt allTrue at h
  have hindex : Pnp3.Models.bitVecToNat allTrue =
      Pnp3.Models.Partial.tableLen r - 1 := by
    simpa [allTrue, Pnp3.Models.Partial.tableLen] using bitVecToNat_all_true r
  unfold Pnp3.Models.truthTableFunction at h
  simp only [hindex] at h
  let _ : NeZero (Pnp3.Models.Partial.tableLen r) := ⟨Nat.ne_of_gt htable⟩
  have hfin : Fin.ofNat (Pnp3.Models.Partial.tableLen r)
      (Pnp3.Models.Partial.tableLen r - 1) =
      (⟨Pnp3.Models.Partial.tableLen r - 1, hlast⟩ :
        Fin (Pnp3.Models.Partial.tableLen r)) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hlast
  rw [hfin] at h
  exact h.symm

/-! ## Parsed-target and support bounds -/

/-- A successful content parse preserves the convention length between the wide header target and
the target `pr.2.n` returned by the narrow parser.  This deliberately states only equality of the
two `treeMCSPPrefixM` values, not equality of the targets. -/
theorem contentInput?_target_length
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {N : Nat}
    (z : PrefixBitVec N) (n_header consumed : Nat)
    {pr : Σ r : Nat, PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec r)}
    (hheader : contentHeader? z = some (n_header, consumed))
    (hpr : contentInput? codec z = some pr) :
    treeMCSPPrefixM codec n_header = treeMCSPPrefixM codec pr.2.n := by
  unfold contentInput? at hpr
  rw [hheader] at hpr
  cases hparse : parseTreeMCSPPrefixInput threshold codec
      (padWord z (treeMCSPPrefixM codec n_header)) with
  | none => simp [hparse] at hpr
  | some input =>
      simp only [hparse, Option.map_some] at hpr
      cases hpr
      exact parseTreeMCSPPrefixInput_length_convention threshold codec
        (padWord z (treeMCSPPrefixM codec n_header)) input hparse

/-- If the physical word ends before a target's query window, the following witness window is
entirely blank. -/
theorem contentWitness_eq_false_of_lt
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {N : Nat}
    (z : PrefixBitVec N) (r : Nat) (hwide : N < treeMCSPPrefixM codec r) :
    contentWitness codec z r = fun _ => false := by
  funext j
  unfold contentWitness
  rw [padRead_ge]
  omega

/-- In the wide case, acceptance forces the parsed target's full truth-table length into the
physical support.  All semantic work is at `r := pr.2.n`; `n_header` enters only through equality
of convention lengths. -/
theorem contentAccepts_parsed_tableLen_le_of_header_target_wide
    (k : Nat) {N : Nat} (z : PrefixBitVec N) (n_header consumed : Nat)
    (hheader : contentHeader? z = some (n_header, consumed))
    (haccepts : ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z)
    (hwide : N < treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n_header) :
    ∃ pr : Σ r : Nat, PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec
            (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ N := by
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  change N < treeMCSPPrefixM codec n_header at hwide
  rcases haccepts with ⟨pr, hpr, _hprefix, hrelation⟩
  have hM : treeMCSPPrefixM codec n_header = treeMCSPPrefixM codec pr.2.n :=
    contentInput?_target_length codec z n_header consumed hheader hpr
  have hwide_r : N < treeMCSPPrefixM codec pr.2.n := by omega
  have hblank : contentWitness codec z pr.2.n = fun _ => false :=
    contentWitness_eq_false_of_lt codec z pr.2.n hwide_r
  change codec.verifies pr.2.n pr.2.x (contentWitness codec z pr.2.n) at hrelation
  rcases hrelation with ⟨c, hdecode, _hsize, hcomputes⟩
  have hr : 0 < pr.2.n := by
    by_contra hr
    have hr0 : pr.2.n = 0 := by omega
    have hnone : codec.decode pr.2.n (fun _ => false) = none := by
      rw [hr0]
      simpa [codec] using treeCircuitWitnessCodec_decode_blank_zero k
    rw [hblank, hnone] at hdecode
    cases hdecode
  rw [hblank, treeCircuitWitnessCodec_decode_blank_pos k hr] at hdecode
  cases hdecode
  have hlast := input_zero_computes_forces_last_true hr pr.2.x hcomputes
  obtain ⟨cg, hx⟩ := contentInput?_x_apply codec z hpr
  let jlast : Fin (Pnp3.Models.Partial.tableLen pr.2.n) :=
    ⟨Pnp3.Models.Partial.tableLen pr.2.n - 1, by
      have := tableLen_pos pr.2.n
      omega⟩
  have hread : padRead z (tagLen + cg + jlast.1) = true := by
    rw [← hx jlast]
    exact hlast
  have hsupport : tagLen + cg + jlast.1 < N :=
    lt_of_padRead_eq_true z hread
  refine ⟨pr, hpr, ?_⟩
  change Pnp3.Models.Partial.tableLen pr.2.n ≤ N
  dsimp [jlast] at hsupport
  have htag : 0 < tagLen := by decide
  omega

/-! ## FEAS-0 headline -/

/-- **FEAS-0 outcome (a).** Every content-accepted word at the concrete polynomial-threshold
codec has polynomially bounded header convention length.  The exponent depends only on `k`.

The proof uses the parsed target `r := pr.2.n`.  In the wide case the preceding theorem gives
`tableLen r ≤ N`; `PolyBoundedInTable.powAdd` bounds `M r`; and
`contentInput?_target_length` transports the result through `M r = M n_header`.  It never infers
`r = n_header`. -/
theorem contentAccepts_target_poly_treePoly (k : Nat) :
    ∃ c : Nat, ∀ (N : Nat) (z : PrefixBitVec N) (n_header consumed : Nat),
      contentHeader? z = some (n_header, consumed) →
      ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z →
      treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n_header ≤ N ^ c + c := by
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  have hW : PolyBoundedInTable codec.witnessBits :=
    polyBoundedInTable_treeWitnessBits_of_thresholdPoly (thresholdPoly k)
      (polyBoundedInTable_thresholdPoly k)
  obtain ⟨d, hd⟩ :=
    (polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly codec hW).powAdd
  refine ⟨d + 1, fun N z n_header consumed hheader haccepts => ?_⟩
  by_cases hwide : N < treeMCSPPrefixM codec n_header
  · obtain ⟨pr, hpr, htable⟩ :=
      contentAccepts_parsed_tableLen_le_of_header_target_wide k z n_header consumed
        hheader haccepts hwide
    have hM : treeMCSPPrefixM codec n_header = treeMCSPPrefixM codec pr.2.n :=
      contentInput?_target_length codec z n_header consumed hheader hpr
    have hgrowth := hd pr.2.n
    have hNpos : 0 < N :=
      lt_of_lt_of_le (tableLen_pos pr.2.n) htable
    calc
      treeMCSPPrefixM codec n_header = treeMCSPPrefixM codec pr.2.n := hM
      _ ≤ (Pnp3.Models.Partial.tableLen pr.2.n) ^ d + d := hgrowth
      _ ≤ N ^ d + d := Nat.add_le_add_right (Nat.pow_le_pow_left htable d) d
      _ ≤ N ^ (d + 1) + (d + 1) := by
        apply Nat.add_le_add
        · exact Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNpos))
            (Nat.le_succ d)
        · omega
  · have hnarrow : treeMCSPPrefixM codec n_header ≤ N := by omega
    have hNpow : N ≤ N ^ (d + 1) := Nat.le_pow (by omega)
    exact le_trans hnarrow (le_trans hNpow (Nat.le_add_right _ _))

end ContractExpansion
end Frontier
end Pnp4
