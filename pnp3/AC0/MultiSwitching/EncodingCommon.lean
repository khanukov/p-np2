import AC0.MultiSwitching.Encoding
import AC0.MultiSwitching.CommonBad

/-!
  pnp3/AC0/MultiSwitching/EncodingCommon.lean

  Encoding/injection for common‑CCDT bad predicate.
  Here the formula index may change at each step, so we encode it per‑step
  using `Aux n t (w+1) (F.length+1)`.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n w : Nat}

def BadFamilyDetCommonInRsCNF {n w : Nat} (F : FormulaFamily n w) (s t : Nat) : Type :=
  {ρ : Restriction n // ρ ∈ R_s (n := n) s ∧ BadFamily_deterministic_common (F := F) t ρ}

lemma badRestrictions_eq_common_badFamilyDet
    {n w t s : Nat} (F : FormulaFamily n w)
    [DecidablePred (BadEvent_common (F := F) t)]
    [DecidablePred (BadFamily_deterministic_common (F := F) t)] :
    badRestrictions (n := n) s (BadEvent_common (F := F) t)
      =
    badRestrictions (n := n) s (BadFamily_deterministic_common (F := F) t) := by
  classical
  ext ρ
  constructor
  · intro hmem
    have hmem' :
        ρ ∈ R_s (n := n) s ∧ BadEvent_common (F := F) t ρ := by
      simpa [mem_badRestrictions] using hmem
    rcases hmem' with ⟨hRs, hbad⟩
    exact (mem_badRestrictions).2 ⟨hRs,
      (badEvent_common_iff_badFamilyDet_common (F := F) (t := t) (ρ := ρ)).1 hbad⟩
  · intro hmem
    have hmem' :
        ρ ∈ R_s (n := n) s ∧ BadFamily_deterministic_common (F := F) t ρ := by
      simpa [mem_badRestrictions] using hmem
    rcases hmem' with ⟨hRs, hbad⟩
    exact (mem_badRestrictions).2 ⟨hRs,
      (badEvent_common_iff_badFamilyDet_common (F := F) (t := t) (ρ := ρ)).2 hbad⟩

/-!
### Aux encoding for common trace
-/

noncomputable def auxSimpleOfCommonTrace
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) : AuxSimple n t := by
  classical
  let fixes := CommonTrace.assignedBitFixes trace
  have hlen : fixes.length = t := CommonTrace.assignedBitFixes_length trace
  exact fun i => fixes.get (Fin.cast hlen.symm i)

noncomputable def auxOfCommonTrace
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) :
    Aux n t (w + 1) (F.length + 1) := by
  classical
  let fixes := CommonTrace.assignedBitFixes trace
  let lits := CommonTrace.literalPositions trace
  let forms := CommonTrace.formulaIndices trace
  have hlen_fix : fixes.length = t := CommonTrace.assignedBitFixes_length trace
  have hlen_lit : lits.length = t := CommonTrace.literalPositions_length trace
  have hlen_form : forms.length = t := CommonTrace.formulaIndices_length trace
  refine fun i =>
    let bitFix := fixes.get (Fin.cast hlen_fix.symm i)
    let lit := lits.get (Fin.cast hlen_lit.symm i)
    let form := forms.get (Fin.cast hlen_form.symm i)
    (bitFix, Fin.ofNat (w + 1) lit, Fin.ofNat (F.length + 1) form)

lemma auxSimpleOfAux_ofCommonTrace
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) :
    auxSimpleOfAux (auxOfCommonTrace (trace := trace))
      = auxSimpleOfCommonTrace (trace := trace) := by
  classical
  funext i
  simp [auxSimpleOfAux, auxOfCommonTrace, auxSimpleOfCommonTrace]

lemma decodeAuxSimple_ofCommonTrace
    {F : FormulaFamily n w} {ρ : Restriction n} {t : Nat}
    (trace : CommonTrace F ρ t) :
    decodeAuxSimple (ρ' := CommonTrace.finalRestriction trace)
      (aux := auxSimpleOfCommonTrace (trace := trace)) = ρ := by
  classical
  -- `List.ofFn` от `List.get` возвращает исходный список.
  let fixes := CommonTrace.assignedBitFixes trace
  have hlen : fixes.length = t := CommonTrace.assignedBitFixes_length trace
  have hcongr :
      List.ofFn
          (fun i : Fin t =>
            fixes.get (Fin.cast hlen.symm i))
        =
      List.ofFn
          (fun i : Fin fixes.length =>
            fixes.get i) := by
    simpa using
      (List.ofFn_congr (h := hlen)
        (f := fun i : Fin fixes.length => fixes.get i)).symm
  have hlist :
      List.ofFn (auxSimpleOfCommonTrace (trace := trace)) = fixes := by
    calc
      List.ofFn (auxSimpleOfCommonTrace (trace := trace))
          =
          List.ofFn
            (fun i : Fin t =>
              fixes.get (Fin.cast hlen.symm i)) := by
            simp [auxSimpleOfCommonTrace, fixes]
      _ = List.ofFn
            (fun i : Fin fixes.length =>
              fixes.get i) := hcongr
      _ = fixes := by
            simp
  -- `reconstructRestriction` восстанавливает исходную рестрикцию.
  have hdecode :
      Core.SelectionTrace.reconstructRestriction
          (ρ := CommonTrace.finalRestriction trace)
          (CommonTrace.assignedBitFixes trace) = ρ := by
    simpa using (CommonTrace.reconstruct_eq_original (trace := trace))
  simpa [decodeAuxSimple, hlist] using hdecode

/-!
### Encoding/injection for common bad
-/

noncomputable def encodeBadFamilyDetCommon_aux
    {n w t s : Nat} (F : FormulaFamily n w) :
    BadFamilyDetCommonInRsCNF (F := F) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product
        (auxCodes n t (w + 1) (F.length + 1))} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := Classical.choose hbad
  have hdet : commonTraceDeterministic (F := F) trace :=
    Classical.choose_spec hbad
  let ρ' := CommonTrace.finalRestriction trace
  let aux := auxOfCommonTrace (trace := trace)
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    simpa [ρ'] using
      (CommonTrace.finalRestriction_mem_R_s
        (trace := trace) (s := s) hρs)
  refine ⟨⟨ρ', aux⟩, ?_⟩
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [auxCodes]⟩

noncomputable def decodeBadFamilyDetCommon_aux
    {n w t : Nat} (F : FormulaFamily n w) :
    (Restriction n × Aux n t (w + 1) (F.length + 1)) → Restriction n
  | ⟨ρ', aux⟩ => decodeAuxSimple (ρ' := ρ') (aux := auxSimpleOfAux aux)

lemma decode_encodeBadFamilyDetCommon_aux
    {n w t s : Nat} (F : FormulaFamily n w)
    (ρbad : BadFamilyDetCommonInRsCNF (F := F) s t) :
    decodeBadFamilyDetCommon_aux (F := F)
        (encodeBadFamilyDetCommon_aux (F := F) (s := s) (t := t) ρbad).1
      = ρbad.1 := by
  classical
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := Classical.choose hbad
  have hdet : commonTraceDeterministic (F := F) trace :=
    Classical.choose_spec hbad
  have hdecode := decodeAuxSimple_ofCommonTrace (trace := trace)
  have haux :
      auxSimpleOfAux (auxOfCommonTrace (trace := trace))
        = auxSimpleOfCommonTrace (trace := trace) := by
    simpa using (auxSimpleOfAux_ofCommonTrace (trace := trace))
  simpa [encodeBadFamilyDetCommon_aux, decodeBadFamilyDetCommon_aux,
    auxOfCommonTrace, haux] using hdecode

lemma encodeBadFamilyDetCommon_aux_injective
    {n w t s : Nat} (F : FormulaFamily n w) :
    Function.Injective (encodeBadFamilyDetCommon_aux (F := F) (s := s) (t := t)) := by
  classical
  intro x y hxy
  have hx := decode_encodeBadFamilyDetCommon_aux (F := F) (s := s) (t := t) x
  have hy := decode_encodeBadFamilyDetCommon_aux (F := F) (s := s) (t := t) y
  have hρ :
      decodeBadFamilyDetCommon_aux (F := F) (t := t)
          (encodeBadFamilyDetCommon_aux (F := F) (s := s) (t := t) x).1
        =
      decodeBadFamilyDetCommon_aux (F := F) (t := t)
          (encodeBadFamilyDetCommon_aux (F := F) (s := s) (t := t) y).1 := by
    simp [hxy]
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this

end MultiSwitching
end AC0
end Pnp3
