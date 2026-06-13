import Pnp4.AlgorithmsToLowerBounds.SparseWitnessPruning

/-!
# Symmetric witness pruning: weight-determined languages lie in `PpolyDAG`

Second pruning theorem toward the residual input-1 gap (continuing
`SparseWitnessPruning.lean`, same ground rule: self-contained, no external
sources).  Target statement:

* `PpolyDAG_of_weightDetermined`: every language whose slices depend only
  on the Hamming weight of the input lies in `PpolyDAG`.

Consequently no symmetric language — MAJORITY, thresholds, parity,
exact-weight tests, mod-counters, or any other weight-determined predicate
— can witness `NP_not_subset_PpolyDAG`, regardless of its `NP` status:
`VerifiedNPDAGLowerBoundSource.not_weightDetermined`.

Method: the classical shared dynamic program for prefix weights, realized
on the repository's `DagBundle` layer.  Cell `(i, j)` computes
"the first `i` bits have weight exactly `j`"; row `i+1` is appended onto
the shared gate list with `snocBundleSubst` (additive gate growth), and
the final row yields the exact-weight indicators, whose disjunction over
the accepted weights decides the language.  Total size is `O(n²)` gates
per slice, far below the polynomial schedule.

The module also records the endpoint complement-closure law
(`PpolyDAG_compl_iff`), so hardness of a witness transfers to its
complement — with the standing caveat that complementation does not
preserve `NP` membership.
-/

namespace Pnp4
namespace AlgorithmsToLowerBounds

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-! ### Output re-selection for bundles -/

/-- Re-select the outputs of a bundle along an index map (shared gate list,
no new gates). -/
def remapOutputs {m out out' : Nat} (B : DagBundle m out)
    (f : Fin out' → Fin out) : DagBundle m out' where
  gates := B.gates
  gate := B.gate
  output := fun o => B.output (f o)

@[simp] theorem remapOutputs_gates {m out out' : Nat} (B : DagBundle m out)
    (f : Fin out' → Fin out) : (remapOutputs B f).gates = B.gates := rfl

@[simp] theorem evalOutput_remapOutputs {m out out' : Nat} (B : DagBundle m out)
    (f : Fin out' → Fin out) (o : Fin out') (x : Bitstring m) :
    (remapOutputs B f).evalOutput o x = B.evalOutput (f o) x := rfl

/-! ### Endpoint closure law: complement -/

/-- Pointwise complement of a language. -/
def complLanguage (L : Language) : Language := fun n x => !(L n x)

/-- Helper estimate for the complement schedule shift. -/
private lemma compl_schedule (c n : Nat) :
    n ^ c + c + 2 ≤ n ^ (c + 3) + (c + 3) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; decide
      · have h1 : (0 : Nat) ^ c = 0 := Nat.zero_pow hc
        have h2 : (0 : Nat) ^ (c + 3) = 0 := Nat.zero_pow (by omega)
        omega
    · simp only [Nat.one_pow]
      omega
  · have h : n ^ c ≤ n ^ (c + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- `PpolyDAG` is closed under complement (negate the output). -/
theorem PpolyDAG_compl {L : Language} (h : PpolyDAG L) :
    PpolyDAG (complLanguage L) := by
  obtain ⟨W, -⟩ := h
  obtain ⟨c, hc⟩ := W.polyBound_poly
  refine ⟨⟨fun n => n ^ (c + 3) + (c + 3),
          ⟨c + 3, fun n => Nat.le_refl _⟩,
          fun n => notC (W.family n), ?_, ?_⟩, trivial⟩
  · intro n
    show size (notC (W.family n)) ≤ n ^ (c + 3) + (c + 3)
    have hnot := size_notC_le (W.family n)
    have hsize := W.family_size_le n
    have hpb := hc n
    have hsched := compl_schedule c n
    omega
  · intro n x
    rw [eval_notC, W.correct n x]
    rfl

/-- Complement closure, iff form: a language is hard for `PpolyDAG` exactly
when its complement is.  (NB: complementation does not preserve `NP`, so
this transfers hardness, not witnesses.) -/
theorem PpolyDAG_compl_iff (L : Language) :
    PpolyDAG (complLanguage L) ↔ PpolyDAG L := by
  constructor
  · intro h
    have h2 := PpolyDAG_compl h
    have hLL : complLanguage (complLanguage L) = L := by
      funext n x
      simp [complLanguage]
    rwa [hLL] at h2
  · exact PpolyDAG_compl

/-! ### Hamming weight and prefix weights -/

/-- Hamming weight of a bitstring. -/
def hammingWeight {n : Nat} (x : Bitstring n) : Nat :=
  (Finset.univ.filter (fun t : Fin n => x t = true)).card

/-- Weight of the length-`i` prefix, by recursion on `i`. -/
def prefixWeight {n : Nat} (x : Bitstring n) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      prefixWeight x i +
        (if h : i < n then (if x ⟨i, h⟩ then 1 else 0) else 0)

@[simp] theorem prefixWeight_zero {n : Nat} (x : Bitstring n) :
    prefixWeight x 0 = 0 := rfl

theorem prefixWeight_succ {n : Nat} (x : Bitstring n) (i : Nat) (h : i < n) :
    prefixWeight x (i + 1)
      = prefixWeight x i + (if x ⟨i, h⟩ then 1 else 0) := by
  simp [prefixWeight, h]

theorem prefixWeight_le {n : Nat} (x : Bitstring n) (i : Nat) :
    prefixWeight x i ≤ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      by_cases h : i < n
      · rw [prefixWeight_succ x i h]
        by_cases hx : x ⟨i, h⟩ <;> simp [hx] <;> omega
      · simp only [prefixWeight, dif_neg h]
        omega

/-- The filter-characterization of the prefix weight. -/
theorem prefixWeight_eq_card {n : Nat} (x : Bitstring n) (i : Nat) :
    prefixWeight x i
      = (Finset.univ.filter (fun t : Fin n => t.1 < i ∧ x t = true)).card := by
  induction i with
  | zero =>
      simp [prefixWeight]
  | succ i ih =>
      by_cases h : i < n
      · have hsplit :
            (Finset.univ.filter (fun t : Fin n => t.1 < i + 1 ∧ x t = true))
              = (Finset.univ.filter (fun t : Fin n => t.1 < i ∧ x t = true))
                ∪ (Finset.univ.filter (fun t : Fin n => t.1 = i ∧ x t = true)) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
            true_and]
          constructor
          · rintro ⟨hti, htx⟩
            rcases Nat.lt_or_ge t.1 i with hlt | hge
            · exact Or.inl ⟨hlt, htx⟩
            · exact Or.inr ⟨by omega, htx⟩
          · rintro (⟨hti, htx⟩ | ⟨hti, htx⟩)
            · exact ⟨by omega, htx⟩
            · exact ⟨by omega, htx⟩
        have hdisj :
            Disjoint
              (Finset.univ.filter (fun t : Fin n => t.1 < i ∧ x t = true))
              (Finset.univ.filter (fun t : Fin n => t.1 = i ∧ x t = true)) := by
          rw [Finset.disjoint_filter]
          rintro t - ⟨hti, -⟩
          omega
        have hlast :
            (Finset.univ.filter (fun t : Fin n => t.1 = i ∧ x t = true))
              = if x ⟨i, h⟩ then {⟨i, h⟩} else ∅ := by
          by_cases hx : x ⟨i, h⟩
          · rw [if_pos hx]
            ext t
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · rintro ⟨hti, -⟩
              exact Fin.ext hti
            · rintro rfl
              exact ⟨rfl, hx⟩
          · rw [if_neg hx]
            ext t
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false, not_and]
            intro hti
            have : t = ⟨i, h⟩ := Fin.ext hti
            subst this
            intro hcontra
            exact hx hcontra
        rw [prefixWeight_succ x i h, ih, hsplit,
          Finset.card_union_of_disjoint hdisj, hlast]
        by_cases hx : x ⟨i, h⟩
        · simp [hx]
        · simp [hx]
      · have hext :
            (Finset.univ.filter (fun t : Fin n => t.1 < i + 1 ∧ x t = true))
              = (Finset.univ.filter (fun t : Fin n => t.1 < i ∧ x t = true)) := by
          ext t
          have := t.isLt
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨-, htx⟩
            exact ⟨by omega, htx⟩
          · rintro ⟨hti, htx⟩
            exact ⟨by omega, htx⟩
        simp only [prefixWeight, dif_neg h]
        rw [ih, hext]
        omega

/-- At `i = n` the prefix weight is the Hamming weight. -/
theorem prefixWeight_n_eq_hammingWeight {n : Nat} (x : Bitstring n) :
    prefixWeight x n = hammingWeight x := by
  rw [prefixWeight_eq_card, hammingWeight]
  congr 1
  ext t
  have := t.isLt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, htx⟩
    exact htx
  · intro htx
    exact ⟨t.isLt, htx⟩

/-- The Hamming weight never exceeds the length. -/
theorem hammingWeight_le {n : Nat} (x : Bitstring n) : hammingWeight x ≤ n := by
  rw [← prefixWeight_n_eq_hammingWeight]
  exact prefixWeight_le x n


/-! ### DP cell head circuits -/

/--
Head circuit for cell `j` of the next DP row.  Its input space consists of
the `n` real inputs followed by the current bundle outputs (at least the
`n + 1` old-row cells, plus `extra` already-appended new cells).  It reads
the row input bit at position `i` and the old-row cells at positions
`n + j` (and `n + (j-1)` when `j ≥ 1`).
-/
def weightStepHead (n extra : Nat) (i : Fin n) (j : Fin (n + 1)) :
    DagCircuit (n + ((n + 1) + extra)) :=
  if _ : j.1 = 0 then
    andC (inputProj ⟨n + j.1, by have := j.isLt; omega⟩)
      (notC (inputProj ⟨i.1, by have := i.isLt; omega⟩))
  else
    orC
      (andC (inputProj ⟨n + j.1, by have := j.isLt; omega⟩)
        (notC (inputProj ⟨i.1, by have := i.isLt; omega⟩)))
      (andC (inputProj ⟨n + (j.1 - 1), by have := j.isLt; omega⟩)
        (inputProj ⟨i.1, by have := i.isLt; omega⟩))

theorem eval_weightStepHead_zero (n extra : Nat) (i : Fin n) (j : Fin (n + 1))
    (hj : j.1 = 0) (y : Bitstring (n + ((n + 1) + extra))) :
    eval (weightStepHead n extra i j) y
      = (y ⟨n + j.1, by have := j.isLt; omega⟩
          && !(y ⟨i.1, by have := i.isLt; omega⟩)) := by
  rw [weightStepHead, dif_pos hj]
  simp

theorem eval_weightStepHead_pos (n extra : Nat) (i : Fin n) (j : Fin (n + 1))
    (hj : j.1 ≠ 0) (y : Bitstring (n + ((n + 1) + extra))) :
    eval (weightStepHead n extra i j) y
      = ((y ⟨n + j.1, by have := j.isLt; omega⟩
            && !(y ⟨i.1, by have := i.isLt; omega⟩))
         || (y ⟨n + (j.1 - 1), by have := j.isLt; omega⟩
            && y ⟨i.1, by have := i.isLt; omega⟩)) := by
  rw [weightStepHead, dif_neg hj]
  simp

theorem size_weightStepHead_le (n extra : Nat) (i : Fin n) (j : Fin (n + 1)) :
    size (weightStepHead n extra i j) ≤ 14 := by
  by_cases hj : j.1 = 0
  · rw [weightStepHead, dif_pos hj]
    have h1 := size_notC_le
      (inputProj (n := n + ((n + 1) + extra)) ⟨i.1, by have := i.isLt; omega⟩)
    have h2 := size_andC_le
      (inputProj (n := n + ((n + 1) + extra)) ⟨n + j.1, by have := j.isLt; omega⟩)
      (notC (inputProj ⟨i.1, by have := i.isLt; omega⟩))
    simp only [size_inputProj] at h1 h2
    omega
  · rw [weightStepHead, dif_neg hj]
    have h1 := size_notC_le
      (inputProj (n := n + ((n + 1) + extra)) ⟨i.1, by have := i.isLt; omega⟩)
    have h2 := size_andC_le
      (inputProj (n := n + ((n + 1) + extra)) ⟨n + j.1, by have := j.isLt; omega⟩)
      (notC (inputProj ⟨i.1, by have := i.isLt; omega⟩))
    have h3 := size_andC_le
      (inputProj (n := n + ((n + 1) + extra)) ⟨n + (j.1 - 1), by have := j.isLt; omega⟩)
      (inputProj ⟨i.1, by have := i.isLt; omega⟩)
    have h4 := size_orC_le
      (andC (inputProj (n := n + ((n + 1) + extra)) ⟨n + j.1, by have := j.isLt; omega⟩)
        (notC (inputProj ⟨i.1, by have := i.isLt; omega⟩)))
      (andC (inputProj ⟨n + (j.1 - 1), by have := j.isLt; omega⟩)
        (inputProj ⟨i.1, by have := i.isLt; omega⟩))
    simp only [size_inputProj] at h1 h2 h3 h4
    omega

/-! ### Row 0 and the row-append recursion -/

/-- Row 0 of the DP: cell `j` is the constant `decide (j = 0)`
("the empty prefix has weight 0"). -/
def row0Aux (n : Nat) : (j : Nat) → DagBundle n j
  | 0 => emptyBundle n
  | j + 1 => snocBundleSubst (row0Aux n j) (constCircuit (n + j) (decide (j = 0)))

/-- The initial row bundle with `n + 1` constant cells. -/
def row0Bundle (n : Nat) : DagBundle n (n + 1) := row0Aux n (n + 1)

/-- Append cells `0..j-1` of the next row (for input index `i`) onto a row
bundle, sharing the gate list. -/
def appendRowAux (n : Nat) (i : Fin n) (B₀ : DagBundle n (n + 1)) :
    (j : Nat) → j ≤ n + 1 → DagBundle n ((n + 1) + j)
  | 0, _ => B₀
  | j + 1, h =>
      snocBundleSubst (appendRowAux n i B₀ j (by omega))
        (weightStepHead n j i ⟨j, by omega⟩)

/-- One full DP row step: append all `n + 1` next-row cells, then re-select
only the new row as the bundle outputs. -/
def rowStep (n : Nat) (i : Fin n) (B₀ : DagBundle n (n + 1)) :
    DagBundle n (n + 1) :=
  remapOutputs (appendRowAux n i B₀ (n + 1) (Nat.le_refl _))
    (fun o => ⟨(n + 1) + o.1, by have := o.isLt; omega⟩)

/-- The expected Boolean value of cell `j` in the next row, given the old
row `r` and the row input bit `xi`. -/
def nextCell {n : Nat} (r : Fin (n + 1) → Bool) (xi : Bool)
    (j : Fin (n + 1)) : Bool :=
  if _ : j.1 = 0 then r j && !xi
  else (r j && !xi) || (r ⟨j.1 - 1, by have := j.isLt; omega⟩ && xi)


/-! ### Passthrough value helpers -/

theorem passthrough_input_val {m out : Nat} (B : DagBundle m out)
    (x : Bitstring m) (v : Nat) (hv : v < m) (h2 : v < m + out) :
    (passthroughBundle B).evalOutput ⟨v, h2⟩ x = x ⟨v, hv⟩ := by
  have hco : (⟨v, h2⟩ : Fin (m + out)) = Fin.castAdd out ⟨v, hv⟩ := by
    apply Fin.ext
    simp
  rw [hco, evalOutput_passthroughBundle_input]

theorem passthrough_output_val {m out : Nat} (B : DagBundle m out)
    (x : Bitstring m) (k : Nat) (hk : k < out) (h2 : m + k < m + out) :
    (passthroughBundle B).evalOutput ⟨m + k, h2⟩ x = B.evalOutput ⟨k, hk⟩ x := by
  have hco : (⟨m + k, h2⟩ : Fin (m + out)) = Fin.natAdd m ⟨k, hk⟩ := by
    apply Fin.ext
    simp
  rw [hco, evalOutput_passthroughBundle_output]

/-! ### Row 0 semantics -/

theorem row0Aux_eval (n : Nat) (x : Bitstring n) :
    ∀ (j : Nat) (o : Fin j), (row0Aux n j).evalOutput o x = decide (o.1 = 0)
  | 0, o => absurd o.isLt (Nat.not_lt_zero _)
  | j + 1, o => by
      rcases Nat.lt_or_ge o.1 j with ho | ho
      · have hco : o = Fin.castAdd 1 (⟨o.1, ho⟩ : Fin j) := by
          apply Fin.ext
          simp
        simp only [row0Aux]
        rw [hco, evalOutput_snocBundleSubst_old]
        exact row0Aux_eval n x j ⟨o.1, ho⟩
      · have hoj : o.1 = j := by have := o.isLt; omega
        have hno : o = Fin.natAdd j (0 : Fin 1) := by
          apply Fin.ext
          simp [hoj]
        simp only [row0Aux]
        rw [hno, evalOutput_snocBundleSubst_new, eval_constCircuit]
        have hval : ((Fin.natAdd j (0 : Fin 1)) : Nat) = j := by simp
        rw [hval]

theorem row0Bundle_eval (n : Nat) (x : Bitstring n) (o : Fin (n + 1)) :
    (row0Bundle n).evalOutput o x = decide (o.1 = 0) :=
  row0Aux_eval n x (n + 1) o

/-! ### Row-append semantics -/

theorem nextCell_zero {n : Nat} (r : Fin (n + 1) → Bool) (xi : Bool)
    (j : Fin (n + 1)) (hj : j.1 = 0) :
    nextCell r xi j = (r j && !xi) := by
  simp only [nextCell, dif_pos hj]

theorem nextCell_pos {n : Nat} (r : Fin (n + 1) → Bool) (xi : Bool)
    (j : Fin (n + 1)) (hj : j.1 ≠ 0) :
    nextCell r xi j
      = ((r j && !xi) || (r ⟨j.1 - 1, by have := j.isLt; omega⟩ && xi)) := by
  simp only [nextCell, dif_neg hj]

theorem appendRowAux_eval (n : Nat) (i : Fin n) (B₀ : DagBundle n (n + 1))
    (x : Bitstring n) :
    ∀ (j : Nat) (hj : j ≤ n + 1) (o : Fin ((n + 1) + j)),
      (appendRowAux n i B₀ j hj).evalOutput o x
        = if ho : o.1 < n + 1
          then B₀.evalOutput ⟨o.1, ho⟩ x
          else nextCell (fun t => B₀.evalOutput t x) (x i)
                 ⟨o.1 - (n + 1), by have := o.isLt; omega⟩
  | 0, hj, o => by
      have ho : o.1 < n + 1 := o.isLt
      rw [dif_pos ho]
      rfl
  | j + 1, hj, o => by
      have hjn : j < n + 1 := by omega
      rcases Nat.lt_or_ge o.1 ((n + 1) + j) with ho | ho
      · -- a previously existing output is preserved by the snoc step
        have hold :
            (appendRowAux n i B₀ (j + 1) hj).evalOutput o x
              = (appendRowAux n i B₀ j (Nat.le_of_succ_le hj)).evalOutput
                  ⟨o.1, ho⟩ x :=
          evalOutput_snocBundleSubst_old _ _ ⟨o.1, ho⟩ x
        rw [hold,
          appendRowAux_eval n i B₀ x j (Nat.le_of_succ_le hj) ⟨o.1, ho⟩]
      · -- the freshly appended cell
        have hoj : o.1 = (n + 1) + j := by have := o.isLt; omega
        rw [dif_neg (by omega : ¬ o.1 < n + 1)]
        have hno : o = Fin.natAdd ((n + 1) + j) (0 : Fin 1) := by
          apply Fin.ext
          simp [hoj]
        have hnew :
            (appendRowAux n i B₀ (j + 1) hj).evalOutput o x
              = eval (weightStepHead n j i ⟨j, hjn⟩)
                  (fun w =>
                    (passthroughBundle
                      (appendRowAux n i B₀ j (Nat.le_of_succ_le hj))).evalOutput
                        w x) := by
          conv_lhs => rw [hno]
          exact evalOutput_snocBundleSubst_new _ _ x
        rw [hnew]
        have hidx : (⟨o.1 - (n + 1), by have := o.isLt; omega⟩ : Fin (n + 1))
            = ⟨j, hjn⟩ := by
          apply Fin.ext
          show o.1 - (n + 1) = j
          omega
        rw [hidx]
        set y : Bitstring (n + ((n + 1) + j)) :=
          fun w =>
            (passthroughBundle
              (appendRowAux n i B₀ j (Nat.le_of_succ_le hj))).evalOutput w x
          with hy
        have hyi : ∀ h2 : i.1 < n + ((n + 1) + j),
            y ⟨i.1, h2⟩ = x i := by
          intro h2
          show (passthroughBundle _).evalOutput ⟨i.1, h2⟩ x = x i
          rw [passthrough_input_val _ x i.1 i.isLt]
        have hyprev : ∀ (k : Nat) (hk : k < n + 1)
            (h2 : n + k < n + ((n + 1) + j)),
            y ⟨n + k, h2⟩ = B₀.evalOutput ⟨k, hk⟩ x := by
          intro k hk h2
          show (passthroughBundle _).evalOutput ⟨n + k, h2⟩ x = _
          rw [passthrough_output_val _ x k (by omega)]
          rw [appendRowAux_eval n i B₀ x j (Nat.le_of_succ_le hj) ⟨k, by omega⟩]
          rw [dif_pos
            (show ((⟨k, by omega⟩ : Fin ((n + 1) + j)) : Nat) < n + 1 from hk)]
        by_cases hzero : j = 0
        · subst hzero
          rw [eval_weightStepHead_zero n 0 i ⟨0, hjn⟩ rfl y]
          rw [hyi, hyprev 0 (by omega) (by omega)]
          rw [nextCell_zero _ _ _ rfl]
        · rw [eval_weightStepHead_pos n j i ⟨j, hjn⟩ hzero y]
          rw [hyi, hyprev j (by omega) (by omega),
            hyprev (j - 1) (by omega) (by omega)]
          rw [nextCell_pos _ _ _ (show ((⟨j, hjn⟩ : Fin (n + 1)) : Nat) ≠ 0 from hzero)]

/-! ### Full row step and the weight bundle -/

theorem rowStep_eval (n : Nat) (i : Fin n) (B₀ : DagBundle n (n + 1))
    (x : Bitstring n) (o : Fin (n + 1)) :
    (rowStep n i B₀).evalOutput o x
      = nextCell (fun t => B₀.evalOutput t x) (x i) o := by
  unfold rowStep
  rw [evalOutput_remapOutputs]
  rw [appendRowAux_eval n i B₀ x (n + 1) (Nat.le_refl _)]
  rw [dif_neg (by omega : ¬ (n + 1) + o.1 < n + 1)]
  congr 1
  apply Fin.ext
  show (n + 1) + o.1 - (n + 1) = o.1
  omega

/-- The full prefix-weight DP bundle after `i` rows. -/
def weightBundleAux (n : Nat) : Nat → DagBundle n (n + 1)
  | 0 => row0Bundle n
  | i + 1 =>
      if h : i < n then rowStep n ⟨i, h⟩ (weightBundleAux n i)
      else weightBundleAux n i

/-- The completed weight bundle: output `w` decides `hammingWeight x = w`. -/
def weightBundle (n : Nat) : DagBundle n (n + 1) := weightBundleAux n n

/-- Semantic law for `nextCell` against prefix weights. -/
theorem nextCell_prefixWeight {n : Nat} (x : Bitstring n) (i : Nat)
    (hin : i < n) (o : Fin (n + 1)) :
    nextCell (fun t : Fin (n + 1) => decide (prefixWeight x i = t.1))
        (x ⟨i, hin⟩) o
      = decide (prefixWeight x (i + 1) = o.1) := by
  rw [prefixWeight_succ x i hin]
  cases hx : x ⟨i, hin⟩ with
  | false =>
      by_cases ho : o.1 = 0
      · simp only [nextCell, dif_pos ho]
        simp
      · simp only [nextCell, dif_neg ho]
        simp
  | true =>
      by_cases ho : o.1 = 0
      · simp only [nextCell, dif_pos ho]
        have : ¬ (prefixWeight x i + 1 = o.1) := by omega
        simp [this]
      · simp only [nextCell, dif_neg ho]
        have hiff : (prefixWeight x i = o.1 - 1)
            ↔ (prefixWeight x i + 1 = o.1) := by omega
        simp [decide_eq_decide.mpr hiff]

theorem weightBundleAux_eval (n : Nat) (x : Bitstring n) :
    ∀ (i : Nat), i ≤ n → ∀ (o : Fin (n + 1)),
      (weightBundleAux n i).evalOutput o x
        = decide (prefixWeight x i = o.1)
  | 0, hi, o => by
      simp only [weightBundleAux]
      rw [row0Bundle_eval, prefixWeight_zero]
      exact decide_eq_decide.mpr (by omega)
  | i + 1, hi, o => by
      have hin : i < n := by omega
      simp only [weightBundleAux]
      rw [dif_pos hin]
      rw [rowStep_eval]
      have hfun : (fun t => (weightBundleAux n i).evalOutput t x)
          = (fun t : Fin (n + 1) => decide (prefixWeight x i = t.1)) := by
        funext t
        exact weightBundleAux_eval n x i (by omega) t
      rw [hfun]
      exact nextCell_prefixWeight x i hin o

theorem weightBundle_eval (n : Nat) (x : Bitstring n) (o : Fin (n + 1)) :
    (weightBundle n).evalOutput o x = decide (hammingWeight x = o.1) := by
  unfold weightBundle
  rw [weightBundleAux_eval n x n (Nat.le_refl _) o]
  rw [prefixWeight_n_eq_hammingWeight]


/-! ### Gate counts -/

theorem row0Aux_gates_le (n : Nat) : ∀ j : Nat, (row0Aux n j).gates ≤ j
  | 0 => Nat.le_refl 0
  | j + 1 => by
      simp only [row0Aux, snocBundleSubst_gates]
      have h1 := row0Aux_gates_le n j
      have h2 : (constCircuit (n + j) (decide (j = 0))).gates = 1 := rfl
      omega

theorem appendRowAux_gates_le (n : Nat) (i : Fin n) (B₀ : DagBundle n (n + 1)) :
    ∀ (j : Nat) (hj : j ≤ n + 1),
      (appendRowAux n i B₀ j hj).gates ≤ B₀.gates + 14 * j
  | 0, hj => by
      simp only [appendRowAux]
      omega
  | j + 1, hj => by
      simp only [appendRowAux, snocBundleSubst_gates]
      have h1 := appendRowAux_gates_le n i B₀ j (Nat.le_of_succ_le hj)
      have h2 : (weightStepHead n j i ⟨j, by omega⟩).gates ≤ 13 := by
        have hsz := size_weightStepHead_le n j i ⟨j, by omega⟩
        have hdef : size (weightStepHead n j i ⟨j, by omega⟩)
            = (weightStepHead n j i ⟨j, by omega⟩).gates + 1 := rfl
        omega
      omega

theorem rowStep_gates_le (n : Nat) (i : Fin n) (B₀ : DagBundle n (n + 1)) :
    (rowStep n i B₀).gates ≤ B₀.gates + 14 * (n + 1) := by
  unfold rowStep
  rw [remapOutputs_gates]
  exact appendRowAux_gates_le n i B₀ (n + 1) (Nat.le_refl _)

theorem weightBundleAux_gates_le (n : Nat) :
    ∀ i : Nat, (weightBundleAux n i).gates ≤ (n + 1) + 14 * (n + 1) * i
  | 0 => by
      simp only [weightBundleAux]
      unfold row0Bundle
      have := row0Aux_gates_le n (n + 1)
      omega
  | i + 1 => by
      simp only [weightBundleAux]
      by_cases h : i < n
      · rw [dif_pos h]
        have h1 := rowStep_gates_le n ⟨i, h⟩ (weightBundleAux n i)
        have h2 := weightBundleAux_gates_le n i
        have hexp : 14 * (n + 1) * (i + 1)
            = 14 * (n + 1) * i + 14 * (n + 1) := by ring
        omega
      · rw [dif_neg h]
        have h2 := weightBundleAux_gates_le n i
        have hmono : 14 * (n + 1) * i ≤ 14 * (n + 1) * (i + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega

theorem weightBundle_gates_le (n : Nat) :
    (weightBundle n).gates ≤ (n + 1) + 14 * (n + 1) * n :=
  weightBundleAux_gates_le n n

/-! ### Weight-determined languages -/

/-- A language is weight-determined (symmetric) if every slice depends only
on the Hamming weight of the input. -/
def WeightDetermined (L : Language) : Prop :=
  ∀ (n : Nat) (x y : Bitstring n),
    hammingWeight x = hammingWeight y → L n x = L n y

/-- The canonical string of weight `w`: ones on the first `w` coordinates. -/
def stepString (n w : Nat) : Bitstring n := fun t => decide (t.1 < w)

theorem prefixWeight_stepString (n w : Nat) :
    ∀ i : Nat, i ≤ n → prefixWeight (stepString n w) i = min i w
  | 0, _ => by simp
  | i + 1, hi => by
      have hin : i < n := by omega
      rw [prefixWeight_succ _ i hin,
        prefixWeight_stepString n w i (by omega)]
      by_cases hiw : i < w
      · simp only [stepString]
        rw [if_pos (by simpa using hiw)]
        omega
      · simp only [stepString]
        rw [if_neg (by simpa using hiw)]
        omega

theorem hammingWeight_stepString (n w : Nat) (hw : w ≤ n) :
    hammingWeight (stepString n w) = w := by
  rw [← prefixWeight_n_eq_hammingWeight,
    prefixWeight_stepString n w n (Nat.le_refl _)]
  omega

/-- The deciding circuit family for a weight-determined language: the
disjunction of the exact-weight indicators over the accepted weights. -/
noncomputable def symmetricFamily (L : Language) (n : Nat) : DagCircuit n :=
  orList
    (((List.finRange (n + 1)).filter (fun w => L n (stepString n w.1))).map
      (fun w => (weightBundle n).asCircuit w))

theorem eval_symmetricFamily {L : Language} (hL : WeightDetermined L)
    (n : Nat) (x : Bitstring n) :
    eval (symmetricFamily L n) x = L n x := by
  rw [symmetricFamily, eval_orList, List.any_map]
  have hcirc : ∀ w : Fin (n + 1),
      eval ((weightBundle n).asCircuit w) x
        = decide (hammingWeight x = w.1) := fun w => weightBundle_eval n x w
  cases hLx : L n x with
  | true =>
      rw [List.any_eq_true]
      have hw0 : hammingWeight x ≤ n := hammingWeight_le x
      refine ⟨⟨hammingWeight x, by omega⟩, ?_, ?_⟩
      · rw [List.mem_filter]
        refine ⟨List.mem_finRange _, ?_⟩
        have hws := hammingWeight_stepString n (hammingWeight x) hw0
        have heq := hL n (stepString n (hammingWeight x)) x (by rw [hws])
        rw [heq, hLx]
      · show eval ((weightBundle n).asCircuit _) x = true
        rw [hcirc]
        simp
  | false =>
      rw [List.any_eq_false]
      intro w hwmem hdec
      have hdec2 : decide (hammingWeight x = w.1) = true := by
        rw [← hcirc w]
        exact hdec
      have hdec' : hammingWeight x = w.1 := of_decide_eq_true hdec2
      rw [List.mem_filter] at hwmem
      have hpred : L n (stepString n w.1) = true := hwmem.2
      have hws := hammingWeight_stepString n w.1 (by have := w.isLt; omega)
      have heq := hL n x (stepString n w.1) (by rw [hws, hdec'])
      rw [hLx, hpred] at heq
      exact Bool.false_ne_true heq

theorem size_symmetricFamily_le (L : Language) (n : Nat) :
    size (symmetricFamily L n)
      ≤ 2 + (n + 1) * (((n + 1) + 14 * (n + 1) * n + 1) + 2) := by
  set lst := ((List.finRange (n + 1)).filter
    (fun w => L n (stepString n w.1))).map
      (fun w => (weightBundle n).asCircuit w) with hlst
  have hlen : lst.length ≤ n + 1 := by
    rw [hlst, List.length_map]
    calc ((List.finRange (n + 1)).filter _).length
        ≤ (List.finRange (n + 1)).length := List.length_filter_le _ _
      _ = n + 1 := List.length_finRange
  have hel : ∀ C ∈ lst, size C + 2 ≤ ((n + 1) + 14 * (n + 1) * n + 1) + 2 := by
    intro C hC
    rw [hlst] at hC
    rcases List.mem_map.mp hC with ⟨w, -, rfl⟩
    have hg := weightBundle_gates_le n
    have hsz : size ((weightBundle n).asCircuit w)
        = (weightBundle n).gates + 1 := rfl
    omega
  have hsum := sum_map_le_of_forall_le lst (fun C => size C + 2)
    (((n + 1) + 14 * (n + 1) * n + 1) + 2) hel
  have horl := size_orList_le lst
  have hmul : lst.length * (((n + 1) + 14 * (n + 1) * n + 1) + 2)
      ≤ (n + 1) * (((n + 1) + 14 * (n + 1) * n + 1) + 2) :=
    Nat.mul_le_mul_right _ hlen
  show size (orList lst) ≤ _
  omega

/-- Master schedule estimate for the symmetric construction. -/
lemma symmetric_master (n : Nat) :
    2 + (n + 1) * (((n + 1) + 14 * (n + 1) * n + 1) + 2) ≤ n ^ 6 + 208 := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> decide
  · -- n ≥ 5
    have hn1 : n + 1 ≤ 2 * n := by omega
    have hsq : n ≤ n ^ 2 := by
      calc n = n ^ 1 := (Nat.pow_one n).symm
        _ ≤ n ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 4 ≤ n ^ 2 := by
      have : 2 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    -- inner ≤ 33 n²
    have hinner : ((n + 1) + 14 * (n + 1) * n + 1) + 2 ≤ 33 * n ^ 2 := by
      have h14 : 14 * (n + 1) * n ≤ 28 * n ^ 2 := by
        calc 14 * (n + 1) * n ≤ 14 * (2 * n) * n := by
              have := Nat.mul_le_mul_right n (Nat.mul_le_mul_left 14 hn1)
              omega
          _ = 28 * (n * n) := by ring
          _ = 28 * n ^ 2 := by rw [Nat.pow_two]
      omega
    -- total ≤ 2 + 2n · 33 n² = 2 + 66 n³
    have htotal : 2 + (n + 1) * (((n + 1) + 14 * (n + 1) * n + 1) + 2)
        ≤ 2 + 66 * n ^ 3 := by
      have hstep : (n + 1) * (((n + 1) + 14 * (n + 1) * n + 1) + 2)
          ≤ (2 * n) * (33 * n ^ 2) := Nat.mul_le_mul hn1 hinner
      have hcube : (2 * n) * (33 * n ^ 2) = 66 * n ^ 3 := by
        have : n ^ 3 = n * n ^ 2 := by
          rw [show (3 : Nat) = 1 + 2 from rfl, Nat.pow_add, Nat.pow_one]
        rw [this]
        ring
      omega
    -- 2 + 66 n³ ≤ n³ · n³ = n⁶
    have hfinal : 2 + 66 * n ^ 3 ≤ n ^ 6 := by
      have h125 : 125 ≤ n ^ 3 := by
        have : 5 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
        omega
      have hbridge : n ^ 6 = n ^ 3 * n ^ 3 := by
        rw [← Nat.pow_add]
      have hge : 125 * n ^ 3 ≤ n ^ 3 * n ^ 3 := Nat.mul_le_mul_right _ h125
      have hcube_pos : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    omega

/-! ### Main theorem and pruning corollaries -/

/--
**Symmetric upper bound**: every weight-determined (symmetric) language
lies in `PpolyDAG`, via the shared prefix-weight dynamic program.
-/
theorem PpolyDAG_of_weightDetermined {L : Language}
    (hL : WeightDetermined L) : PpolyDAG L := by
  classical
  refine ⟨⟨fun n => n ^ 6 + 208, ⟨208, ?_⟩,
          fun n => symmetricFamily L n, ?_, ?_⟩, trivial⟩
  · intro n
    show n ^ 6 + 208 ≤ n ^ 208 + 208
    have hpow : n ^ 6 ≤ n ^ 208 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have h6 : (0 : Nat) ^ 6 = 0 := Nat.zero_pow (by omega)
        have h208 : (0 : Nat) ^ 208 = 0 := Nat.zero_pow (by omega)
        omega
      · exact Nat.pow_le_pow_right hn (by omega)
    omega
  · intro n
    show size (symmetricFamily L n) ≤ n ^ 6 + 208
    have h1 := size_symmetricFamily_le L n
    have h2 := symmetric_master n
    omega
  · intro n x
    exact eval_symmetricFamily hL n x

/-- Hard languages are never weight-determined. -/
theorem not_weightDetermined_of_not_PpolyDAG {L : Language}
    (h : ¬ PpolyDAG L) : ¬ WeightDetermined L :=
  fun hs => h (PpolyDAG_of_weightDetermined hs)

/-- Any valid source witness language is not symmetric: MAJORITY-style,
threshold, parity, and all other weight-determined candidates are formally
excluded. -/
theorem VerifiedNPDAGLowerBoundSource.not_weightDetermined
    (src : VerifiedNPDAGLowerBoundSource) : ¬ WeightDetermined src.L :=
  not_weightDetermined_of_not_PpolyDAG src.notInPpolyDAG

/-- The unconditional diagonal witness is not weight-determined. -/
theorem dagHardLanguage_not_weightDetermined :
    ¬ WeightDetermined dagHardLanguage :=
  not_weightDetermined_of_not_PpolyDAG dagHardLanguage_not_PpolyDAG

end AlgorithmsToLowerBounds
end Pnp4
