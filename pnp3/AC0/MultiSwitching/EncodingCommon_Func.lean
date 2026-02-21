import AC0.MultiSwitching.Encoding
import AC0.MultiSwitching.CommonBad_Func

/-!
  pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean

  Encoding/injection for common‑CCDT bad predicate (FuncCNF/atoms).

  Мы используем Aux с грубой верхней границей на длину клаузы;
  literal/formula индексы кодируем фиксированным нулём (достаточно
  для инъективности, поскольку декодирование использует только AuxSimple).
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n : Nat}

/-!
### Max literal length (coarse bound)
-/

def maxClauseLits (Fs : List (FuncCNF n)) : Nat :=
  Fs.foldl (fun m F =>
    Nat.max m (F.clauses.foldl (fun m C => Nat.max m C.lits.length) 0)) 0

/-!
### Aux encoding for common trace (atoms)
-/

noncomputable def auxSimpleOfCommonTrace_atom
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t) : AuxSimple n t := by
  classical
  let fixes := CommonTraceAtom.assignedBitFixes trace
  have hlen : fixes.length = t := CommonTraceAtom.assignedBitFixes_length trace
  exact fun i => fixes.get (Fin.cast hlen.symm i)

noncomputable def auxOfCommonTrace_atom
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t) :
    Aux n t (maxClauseLits Fs + 1) (Fs.length + 1) := by
  classical
  let fixes := CommonTraceAtom.assignedBitFixes trace
  have hlen_fix : fixes.length = t := CommonTraceAtom.assignedBitFixes_length trace
  refine fun i =>
    let bitFix := fixes.get (Fin.cast hlen_fix.symm i)
    let lit := (0 : Nat)
    let form := (0 : Nat)
    (bitFix,
      Fin.ofNat (maxClauseLits Fs + 1) lit,
      Fin.ofNat (Fs.length + 1) form)

lemma decodeAuxSimple_ofCommonTrace_atom
    {Fs : List (FuncCNF n)} {ρ : Restriction n} {t : Nat}
    (trace : CommonTraceAtom (n := n) Fs ρ t)
    (hdet : commonTraceDeterministic_atom (Fs := Fs) trace) :
    decodeAuxSimple (ρ' := CommonTraceAtom.finalRestriction trace)
      (aux := auxSimpleOfCommonTrace_atom (trace := trace)) = ρ := by
  classical
  -- `List.ofFn` от `List.get` возвращает исходный список.
  let fixes := CommonTraceAtom.assignedBitFixes trace
  have hlen : fixes.length = t := CommonTraceAtom.assignedBitFixes_length trace
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
      List.ofFn (auxSimpleOfCommonTrace_atom (trace := trace)) = fixes := by
    calc
      List.ofFn (auxSimpleOfCommonTrace_atom (trace := trace))
          =
          List.ofFn
            (fun i : Fin t =>
              fixes.get (Fin.cast hlen.symm i)) := by
            simp [auxSimpleOfCommonTrace_atom, fixes]
      _ = List.ofFn
            (fun i : Fin fixes.length =>
              fixes.get i) := hcongr
      _ = fixes := by
            simp
  -- `reconstructRestriction` восстанавливает исходную рестрикцию.
  have hdecode :
      Core.SelectionTrace.reconstructRestriction
          (ρ := CommonTraceAtom.finalRestriction trace)
          (CommonTraceAtom.assignedBitFixes trace) = ρ := by
    exact reconstruct_eq_original_atom (trace := trace) hdet
  simpa [decodeAuxSimple, hlist] using hdecode

/-!
### Encoding/injection for common bad (atoms)
-/

def BadFamilyDetCommonInRsAtom {n : Nat} (Fs : List (FuncCNF n)) (s t : Nat) : Type :=
  {ρ : Restriction n // ρ ∈ R_s (n := n) s ∧ BadFamily_deterministic_common_atom (Fs := Fs) t ρ}

noncomputable def encodeBadFamilyDetCommon_aux_atom
    {n t s : Nat} (Fs : List (FuncCNF n)) :
    BadFamilyDetCommonInRsAtom (n := n) (Fs := Fs) s t →
      {c // c ∈ (R_s (n := n) (s - t)).product
        (auxCodes n t (maxClauseLits Fs + 1) (Fs.length + 1))} := by
  classical
  intro ρbad
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := Classical.choose hbad
  have hdet : commonTraceDeterministic_atom (Fs := Fs) trace :=
    Classical.choose_spec hbad
  let ρ' := CommonTraceAtom.finalRestriction trace
  let aux := auxOfCommonTrace_atom (trace := trace)
  have hρ' : ρ' ∈ R_s (n := n) (s - t) := by
    simpa [ρ'] using
      (finalRestriction_mem_R_s_atom (trace := trace) (hdet := hdet) (s := s) hρs)
  refine ⟨⟨ρ', aux⟩, ?_⟩
  refine Finset.mem_product.2 ?_
  exact ⟨hρ', by simp [auxCodes]⟩

noncomputable def decodeBadFamilyDetCommon_aux_atom
    {n t : Nat} (Fs : List (FuncCNF n)) :
    (Restriction n × Aux n t (maxClauseLits Fs + 1) (Fs.length + 1)) → Restriction n
  | ⟨ρ', aux⟩ => decodeAuxSimple (ρ' := ρ') (aux := auxSimpleOfAux aux)

lemma decode_encodeBadFamilyDetCommon_aux_atom
    {n t s : Nat} (Fs : List (FuncCNF n))
    (ρbad : BadFamilyDetCommonInRsAtom (n := n) (Fs := Fs) s t) :
    decodeBadFamilyDetCommon_aux_atom (Fs := Fs)
        (encodeBadFamilyDetCommon_aux_atom (Fs := Fs) (s := s) (t := t) ρbad).1
      = ρbad.1 := by
  classical
  rcases ρbad with ⟨ρ, hρs, hbad⟩
  let trace := Classical.choose hbad
  have hdet : commonTraceDeterministic_atom (Fs := Fs) trace :=
    Classical.choose_spec hbad
  have hdecode := decodeAuxSimple_ofCommonTrace_atom (trace := trace) hdet
  have haux :
      auxSimpleOfAux (auxOfCommonTrace_atom (trace := trace))
        = auxSimpleOfCommonTrace_atom (trace := trace) := by
    funext i
    simp [auxSimpleOfAux, auxOfCommonTrace_atom, auxSimpleOfCommonTrace_atom]
  simpa [encodeBadFamilyDetCommon_aux_atom, decodeBadFamilyDetCommon_aux_atom,
    auxOfCommonTrace_atom, haux] using hdecode

lemma encodeBadFamilyDetCommon_aux_atom_injective
    {n t s : Nat} (Fs : List (FuncCNF n)) :
    Function.Injective
      (encodeBadFamilyDetCommon_aux_atom (Fs := Fs) (s := s) (t := t)) := by
  classical
  intro x y hxy
  have hx :=
    decode_encodeBadFamilyDetCommon_aux_atom (Fs := Fs) (s := s) (t := t) x
  have hy :=
    decode_encodeBadFamilyDetCommon_aux_atom (Fs := Fs) (s := s) (t := t) y
  have hρ :
      decodeBadFamilyDetCommon_aux_atom (Fs := Fs) (t := t)
          (encodeBadFamilyDetCommon_aux_atom (Fs := Fs) (s := s) (t := t) x).1
        =
      decodeBadFamilyDetCommon_aux_atom (Fs := Fs) (t := t)
          (encodeBadFamilyDetCommon_aux_atom (Fs := Fs) (s := s) (t := t) y).1 := by
    simp [hxy]
  have : x.1 = y.1 := by simpa [hx, hy] using hρ
  exact Subtype.ext this

end MultiSwitching
end AC0
end Pnp3
